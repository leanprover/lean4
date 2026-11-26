// Lean compiler output
// Module: Lean.Elab.Tactic.Do.VCGen.Split
// Imports: public import Lean.Meta.Tactic.Simp.Types public import Lean.Meta.Match.MatcherApp.Transform public import Lean.Data.Array import Lean.Meta.Match.Rewrite import Lean.Meta.Tactic.Simp.Rewrite import Lean.Meta.Tactic.Assumption
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Array_mask___redArg(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withLocalDeclsDND___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withLocalDeclsD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_rwIfWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rwMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_resTy(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__4_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_discriminants(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_discriminants___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 154, 90, 102, 217, 192, 49, 255)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 228, 43, 115, 146, 126, 91, 53)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 11, 154, 178, 201, 214, 183, 192)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 128, 245, 49, 225, 62, 36, 86)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "discr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 61, 20, 168, 108, 94, 13, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_etaExpand___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(38, 183, 255, 58, 84, 31, 100, 5)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 70, 3, 12, 31, 103, 230, 247)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 82, 240, 34, 69, 121, 64, 234)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dcond"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MatcherApp_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Failed to find proof for if condition "};
static const lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Failed to find proof for cond condition "};
static const lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
lean_object* v_e_7_; lean_object* v___x_8_; 
v_e_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_e_7_);
lean_dec_ref(v_t_5_);
v___x_8_ = lean_apply_1(v_k_6_, v_e_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(lean_object* v_t_21_, lean_object* v_ite_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_21_, v_ite_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_ite_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_25_, v_ite_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(lean_object* v_t_29_, lean_object* v_dite_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_29_, v_dite_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_dite_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_33_, v_dite_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim___redArg(lean_object* v_t_37_, lean_object* v_cond_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_37_, v_cond_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_cond_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_41_, v_cond_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(lean_object* v_t_45_, lean_object* v_matcher_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_45_, v_matcher_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_matcher_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_49_, v_matcher_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_box(0);
v___x_57_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1));
v___x_58_ = l_Lean_Expr_const___override(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_zero_65_; uint8_t v_isZero_66_; 
v_zero_65_ = lean_unsigned_to_nat(0u);
v_isZero_66_ = lean_nat_dec_eq(v_x_63_, v_zero_65_);
if (v_isZero_66_ == 1)
{
lean_dec(v_x_63_);
return v_x_64_;
}
else
{
lean_object* v_one_67_; lean_object* v_n_68_; 
v_one_67_ = lean_unsigned_to_nat(1u);
v_n_68_ = lean_nat_sub(v_x_63_, v_one_67_);
lean_dec(v_x_63_);
if (lean_obj_tag(v_x_64_) == 1)
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_80_; 
v_val_69_ = lean_ctor_get(v_x_64_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_64_);
if (v_isSharedCheck_80_ == 0)
{
v___x_71_ = v_x_64_;
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v_x_64_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
if (lean_obj_tag(v_val_69_) == 6)
{
lean_object* v_body_73_; lean_object* v___x_75_; 
v_body_73_ = lean_ctor_get(v_val_69_, 2);
lean_inc_ref(v_body_73_);
lean_dec_ref_known(v_val_69_, 3);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v_body_73_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_body_73_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
v_x_63_ = v_n_68_;
v_x_64_ = v___x_75_;
goto _start;
}
}
else
{
lean_object* v___x_78_; 
lean_del_object(v___x_71_);
lean_dec(v_val_69_);
v___x_78_ = lean_box(0);
v_x_63_ = v_n_68_;
v_x_64_ = v___x_78_;
goto _start;
}
}
}
else
{
lean_object* v___x_81_; 
lean_dec(v_x_64_);
v___x_81_ = lean_box(0);
v_x_63_ = v_n_68_;
v_x_64_ = v___x_81_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_resTy(lean_object* v_info_83_){
_start:
{
lean_object* v_e_85_; 
if (lean_obj_tag(v_info_83_) == 3)
{
lean_object* v_matcherApp_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_108_; 
v_matcherApp_91_ = lean_ctor_get(v_info_83_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_info_83_);
if (v_isSharedCheck_108_ == 0)
{
v___x_93_ = v_info_83_;
v_isShared_94_ = v_isSharedCheck_108_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_matcherApp_91_);
lean_dec(v_info_83_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_108_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_toMatcherInfo_95_; lean_object* v_motive_96_; lean_object* v_discrInfos_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v_toMatcherInfo_95_ = lean_ctor_get(v_matcherApp_91_, 0);
lean_inc_ref(v_toMatcherInfo_95_);
v_motive_96_ = lean_ctor_get(v_matcherApp_91_, 4);
lean_inc_ref_n(v_motive_96_, 2);
lean_dec_ref(v_matcherApp_91_);
v_discrInfos_97_ = lean_ctor_get(v_toMatcherInfo_95_, 4);
lean_inc_ref(v_discrInfos_97_);
lean_dec_ref(v_toMatcherInfo_95_);
v___x_98_ = lean_array_get_size(v_discrInfos_97_);
lean_dec_ref(v_discrInfos_97_);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 1);
lean_ctor_set(v___x_93_, 0, v_motive_96_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_motive_96_);
v___x_100_ = v_reuseFailAlloc_107_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Init_Data_Nat_Basic_0__Nat_iterateTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(v___x_98_, v___x_100_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_dec_ref(v_motive_96_);
return v___x_101_;
}
else
{
lean_object* v_val_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_val_102_ = lean_ctor_get(v___x_101_, 0);
v___x_103_ = l_Lean_Expr_looseBVarRange(v_val_102_);
v___x_104_ = l_Lean_Expr_looseBVarRange(v_motive_96_);
lean_dec_ref(v_motive_96_);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
lean_dec(v___x_104_);
lean_dec(v___x_103_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
lean_dec_ref_known(v___x_101_, 1);
v___x_106_ = lean_box(0);
return v___x_106_;
}
else
{
return v___x_101_;
}
}
}
}
}
else
{
lean_object* v_e_109_; 
v_e_109_ = lean_ctor_get(v_info_83_, 0);
lean_inc_ref(v_e_109_);
lean_dec_ref(v_info_83_);
v_e_85_ = v_e_109_;
goto v___jp_84_;
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = l_Lean_Expr_getAppNumArgs(v_e_85_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_sub(v___x_86_, v___x_87_);
lean_dec(v___x_86_);
v___x_89_ = l_Lean_Expr_getRevArg_x21(v_e_85_, v___x_88_);
lean_dec_ref(v_e_85_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object* v_matcherApp_110_, size_t v_sz_111_, size_t v_i_112_, lean_object* v_bs_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = lean_usize_dec_lt(v_i_112_, v_sz_111_);
if (v___x_114_ == 0)
{
return v_bs_113_;
}
else
{
lean_object* v_v_115_; lean_object* v_alts_116_; lean_object* v___x_117_; lean_object* v_bs_x27_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; size_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; 
v_v_115_ = lean_array_uget(v_bs_113_, v_i_112_);
v_alts_116_ = lean_ctor_get(v_matcherApp_110_, 6);
v___x_117_ = lean_unsigned_to_nat(0u);
v_bs_x27_118_ = lean_array_uset(v_bs_113_, v_i_112_, v___x_117_);
v___x_119_ = l_Lean_instInhabitedExpr;
v___x_120_ = lean_usize_to_nat(v_i_112_);
v___x_121_ = lean_array_get_borrowed(v___x_119_, v_alts_116_, v___x_120_);
lean_dec(v___x_120_);
lean_inc(v___x_121_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_v_115_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_add(v_i_112_, v___x_123_);
v___x_125_ = lean_array_uset(v_bs_x27_118_, v_i_112_, v___x_122_);
v_i_112_ = v___x_124_;
v_bs_113_ = v___x_125_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object* v_matcherApp_127_, lean_object* v_sz_128_, lean_object* v_i_129_, lean_object* v_bs_130_){
_start:
{
size_t v_sz_boxed_131_; size_t v_i_boxed_132_; lean_object* v_res_133_; 
v_sz_boxed_131_ = lean_unbox_usize(v_sz_128_);
lean_dec(v_sz_128_);
v_i_boxed_132_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_127_, v_sz_boxed_131_, v_i_boxed_132_, v_bs_130_);
lean_dec_ref(v_matcherApp_127_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object* v_info_134_){
_start:
{
switch(lean_obj_tag(v_info_134_))
{
case 0:
{
lean_object* v_e_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_e_135_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref(v_e_135_);
lean_dec_ref_known(v_info_134_, 1);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_unsigned_to_nat(3u);
v___x_138_ = l_Lean_Expr_getAppNumArgs(v_e_135_);
v___x_139_ = lean_nat_sub(v___x_138_, v___x_137_);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_sub(v___x_139_, v___x_140_);
lean_dec(v___x_139_);
v___x_142_ = l_Lean_Expr_getRevArg_x21(v_e_135_, v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_136_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(4u);
v___x_145_ = lean_nat_sub(v___x_138_, v___x_144_);
lean_dec(v___x_138_);
v___x_146_ = lean_nat_sub(v___x_145_, v___x_140_);
lean_dec(v___x_145_);
v___x_147_ = l_Lean_Expr_getRevArg_x21(v_e_135_, v___x_146_);
lean_dec_ref(v_e_135_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_136_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_unsigned_to_nat(2u);
v___x_150_ = lean_mk_empty_array_with_capacity(v___x_149_);
v___x_151_ = lean_array_push(v___x_150_, v___x_143_);
v___x_152_ = lean_array_push(v___x_151_, v___x_148_);
return v___x_152_;
}
case 1:
{
lean_object* v_e_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_e_153_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref(v_e_153_);
lean_dec_ref_known(v_info_134_, 1);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_unsigned_to_nat(3u);
v___x_156_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
v___x_157_ = lean_nat_sub(v___x_156_, v___x_155_);
v___x_158_ = lean_nat_sub(v___x_157_, v___x_154_);
lean_dec(v___x_157_);
v___x_159_ = l_Lean_Expr_getRevArg_x21(v_e_153_, v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_154_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = lean_nat_sub(v___x_156_, v___x_161_);
lean_dec(v___x_156_);
v___x_163_ = lean_nat_sub(v___x_162_, v___x_154_);
lean_dec(v___x_162_);
v___x_164_ = l_Lean_Expr_getRevArg_x21(v_e_153_, v___x_163_);
lean_dec_ref(v_e_153_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_154_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(2u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_166_);
v___x_168_ = lean_array_push(v___x_167_, v___x_160_);
v___x_169_ = lean_array_push(v___x_168_, v___x_165_);
return v___x_169_;
}
case 2:
{
lean_object* v_e_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_e_170_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref(v_e_170_);
lean_dec_ref_known(v_info_134_, 1);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_unsigned_to_nat(2u);
v___x_173_ = l_Lean_Expr_getAppNumArgs(v_e_170_);
v___x_174_ = lean_nat_sub(v___x_173_, v___x_172_);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_sub(v___x_174_, v___x_175_);
lean_dec(v___x_174_);
v___x_177_ = l_Lean_Expr_getRevArg_x21(v_e_170_, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_171_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(3u);
v___x_180_ = lean_nat_sub(v___x_173_, v___x_179_);
lean_dec(v___x_173_);
v___x_181_ = lean_nat_sub(v___x_180_, v___x_175_);
lean_dec(v___x_180_);
v___x_182_ = l_Lean_Expr_getRevArg_x21(v_e_170_, v___x_181_);
lean_dec_ref(v_e_170_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_171_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_185_ = lean_array_push(v___x_184_, v___x_178_);
v___x_186_ = lean_array_push(v___x_185_, v___x_183_);
return v___x_186_;
}
default: 
{
lean_object* v_matcherApp_187_; lean_object* v___x_188_; size_t v_sz_189_; size_t v___x_190_; lean_object* v___x_191_; 
v_matcherApp_187_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref_n(v_matcherApp_187_, 2);
lean_dec_ref_known(v_info_134_, 1);
v___x_188_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_187_);
v_sz_189_ = lean_array_size(v___x_188_);
v___x_190_ = ((size_t)0ULL);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_187_, v_sz_189_, v___x_190_, v___x_188_);
lean_dec_ref(v_matcherApp_187_);
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object* v_matcherApp_192_, lean_object* v_as_193_, size_t v_sz_194_, size_t v_i_195_, lean_object* v_bs_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_192_, v_sz_194_, v_i_195_, v_bs_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object* v_matcherApp_198_, lean_object* v_as_199_, lean_object* v_sz_200_, lean_object* v_i_201_, lean_object* v_bs_202_){
_start:
{
size_t v_sz_boxed_203_; size_t v_i_boxed_204_; lean_object* v_res_205_; 
v_sz_boxed_203_ = lean_unbox_usize(v_sz_200_);
lean_dec(v_sz_200_);
v_i_boxed_204_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(v_matcherApp_198_, v_as_199_, v_sz_boxed_203_, v_i_boxed_204_, v_bs_202_);
lean_dec_ref(v_as_199_);
lean_dec_ref(v_matcherApp_198_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName(lean_object* v_x_215_){
_start:
{
switch(lean_obj_tag(v_x_215_))
{
case 0:
{
lean_object* v___x_216_; 
v___x_216_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__1));
return v___x_216_;
}
case 1:
{
lean_object* v___x_217_; 
v___x_217_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__3));
return v___x_217_;
}
case 2:
{
lean_object* v___x_218_; 
v___x_218_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__5));
return v___x_218_;
}
default: 
{
lean_object* v_matcherApp_219_; lean_object* v_matcherName_220_; 
v_matcherApp_219_ = lean_ctor_get(v_x_215_, 0);
v_matcherName_220_ = lean_ctor_get(v_matcherApp_219_, 1);
lean_inc(v_matcherName_220_);
return v_matcherName_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___boxed(lean_object* v_x_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitterName(v_x_221_);
lean_dec_ref(v_x_221_);
return v_res_222_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0(void){
_start:
{
lean_object* v___x_223_; lean_object* v_dummy_224_; 
v___x_223_ = lean_box(0);
v_dummy_224_ = l_Lean_Expr_sort___override(v___x_223_);
return v_dummy_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs(lean_object* v_x_225_){
_start:
{
lean_object* v_e_227_; 
switch(lean_obj_tag(v_x_225_))
{
case 2:
{
lean_object* v_e_236_; lean_object* v_dummy_237_; lean_object* v_nargs_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_e_236_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_e_236_);
lean_dec_ref_known(v_x_225_, 1);
v_dummy_237_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0);
v_nargs_238_ = l_Lean_Expr_getAppNumArgs(v_e_236_);
lean_inc(v_nargs_238_);
v___x_239_ = lean_mk_array(v_nargs_238_, v_dummy_237_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_sub(v_nargs_238_, v___x_240_);
v___x_242_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_236_, v___x_239_, v___x_241_);
v___x_243_ = lean_unsigned_to_nat(4u);
v___x_244_ = l_Array_extract___redArg(v___x_242_, v___x_243_, v_nargs_238_);
lean_dec_ref(v___x_242_);
return v___x_244_;
}
case 3:
{
lean_object* v_matcherApp_245_; lean_object* v_remaining_246_; 
v_matcherApp_245_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_matcherApp_245_);
lean_dec_ref_known(v_x_225_, 1);
v_remaining_246_ = lean_ctor_get(v_matcherApp_245_, 7);
lean_inc_ref(v_remaining_246_);
lean_dec_ref(v_matcherApp_245_);
return v_remaining_246_;
}
default: 
{
lean_object* v_e_247_; 
v_e_247_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_e_247_);
lean_dec_ref(v_x_225_);
v_e_227_ = v_e_247_;
goto v___jp_226_;
}
}
v___jp_226_:
{
lean_object* v_dummy_228_; lean_object* v_nargs_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_dummy_228_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0);
v_nargs_229_ = l_Lean_Expr_getAppNumArgs(v_e_227_);
lean_inc(v_nargs_229_);
v___x_230_ = lean_mk_array(v_nargs_229_, v_dummy_228_);
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_sub(v_nargs_229_, v___x_231_);
v___x_233_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_227_, v___x_230_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(5u);
v___x_235_ = l_Array_extract___redArg(v___x_233_, v___x_234_, v_nargs_229_);
lean_dec_ref(v___x_233_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_discriminants(lean_object* v_x_248_){
_start:
{
lean_object* v_e_250_; 
if (lean_obj_tag(v_x_248_) == 3)
{
lean_object* v_matcherApp_258_; lean_object* v_discrs_259_; 
v_matcherApp_258_ = lean_ctor_get(v_x_248_, 0);
v_discrs_259_ = lean_ctor_get(v_matcherApp_258_, 5);
lean_inc_ref(v_discrs_259_);
return v_discrs_259_;
}
else
{
lean_object* v_e_260_; 
v_e_260_ = lean_ctor_get(v_x_248_, 0);
v_e_250_ = v_e_260_;
goto v___jp_249_;
}
v___jp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = l_Lean_Expr_getAppNumArgs(v_e_250_);
v___x_253_ = lean_nat_sub(v___x_252_, v___x_251_);
lean_dec(v___x_252_);
v___x_254_ = lean_nat_sub(v___x_253_, v___x_251_);
lean_dec(v___x_253_);
v___x_255_ = l_Lean_Expr_getRevArg_x21(v_e_250_, v___x_254_);
v___x_256_ = lean_mk_empty_array_with_capacity(v___x_251_);
v___x_257_ = lean_array_push(v___x_256_, v___x_255_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_discriminants___boxed(lean_object* v_x_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Elab_Tactic_Do_SplitInfo_discriminants(v_x_261_);
lean_dec_ref(v_x_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_263_) == 3)
{
lean_object* v_matcherApp_264_; lean_object* v___x_265_; 
v_matcherApp_264_ = lean_ctor_get(v_x_263_, 0);
lean_inc_ref(v_matcherApp_264_);
lean_dec_ref_known(v_x_263_, 1);
v___x_265_ = l_Lean_Meta_MatcherApp_toExpr(v_matcherApp_264_);
return v___x_265_;
}
else
{
lean_object* v_e_266_; 
v_e_266_ = lean_ctor_get(v_x_263_, 0);
lean_inc_ref(v_e_266_);
lean_dec_ref(v_x_263_);
return v_e_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(lean_object* v___x_267_, lean_object* v_resTy_268_, lean_object* v_c_269_, lean_object* v_dec_270_, lean_object* v_t_271_, lean_object* v_e_272_, lean_object* v_k_273_, lean_object* v_u_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_275_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__1));
v___x_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_276_, 0, v_u_274_);
lean_ctor_set(v___x_276_, 1, v___x_267_);
v___x_277_ = l_Lean_mkConst(v___x_275_, v___x_276_);
lean_inc_ref(v_e_272_);
lean_inc_ref(v_t_271_);
lean_inc_ref(v_dec_270_);
lean_inc_ref(v_c_269_);
v___x_278_ = l_Lean_mkApp5(v___x_277_, v_resTy_268_, v_c_269_, v_dec_270_, v_t_271_, v_e_272_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
v___x_280_ = lean_unsigned_to_nat(4u);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_280_);
v___x_282_ = lean_array_push(v___x_281_, v_c_269_);
v___x_283_ = lean_array_push(v___x_282_, v_dec_270_);
v___x_284_ = lean_array_push(v___x_283_, v_t_271_);
v___x_285_ = lean_array_push(v___x_284_, v_e_272_);
v___x_286_ = lean_apply_2(v_k_273_, v___x_279_, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(lean_object* v___x_287_, lean_object* v_resTy_288_, lean_object* v_c_289_, lean_object* v_dec_290_, lean_object* v_t_291_, lean_object* v_k_292_, lean_object* v_inst_293_, lean_object* v_toBind_294_, lean_object* v_e_295_){
_start:
{
lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_inc_ref(v_resTy_288_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0), 8, 7);
lean_closure_set(v___f_296_, 0, v___x_287_);
lean_closure_set(v___f_296_, 1, v_resTy_288_);
lean_closure_set(v___f_296_, 2, v_c_289_);
lean_closure_set(v___f_296_, 3, v_dec_290_);
lean_closure_set(v___f_296_, 4, v_t_291_);
lean_closure_set(v___f_296_, 5, v_e_295_);
lean_closure_set(v___f_296_, 6, v_k_292_);
v___x_297_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_297_, 0, v_resTy_288_);
v___x_298_ = lean_apply_2(v_inst_293_, lean_box(0), v___x_297_);
v___x_299_ = lean_apply_4(v_toBind_294_, lean_box(0), lean_box(0), v___x_298_, v___f_296_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(lean_object* v___x_303_, lean_object* v_resTy_304_, lean_object* v_c_305_, lean_object* v_dec_306_, lean_object* v_k_307_, lean_object* v_inst_308_, lean_object* v_toBind_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_t_312_){
_start:
{
lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
lean_inc_ref(v_resTy_304_);
v___f_313_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1), 9, 8);
lean_closure_set(v___f_313_, 0, v___x_303_);
lean_closure_set(v___f_313_, 1, v_resTy_304_);
lean_closure_set(v___f_313_, 2, v_c_305_);
lean_closure_set(v___f_313_, 3, v_dec_306_);
lean_closure_set(v___f_313_, 4, v_t_312_);
lean_closure_set(v___f_313_, 5, v_k_307_);
lean_closure_set(v___f_313_, 6, v_inst_308_);
lean_closure_set(v___f_313_, 7, v_toBind_309_);
v___x_314_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_315_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_310_, v_inst_311_, v___x_314_, v_resTy_304_, v___f_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(lean_object* v___x_319_, lean_object* v_resTy_320_, lean_object* v_c_321_, lean_object* v_k_322_, lean_object* v_inst_323_, lean_object* v_toBind_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_dec_327_){
_start:
{
lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
lean_inc_ref(v_inst_326_);
lean_inc_ref(v_inst_325_);
lean_inc_ref(v_resTy_320_);
v___f_328_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2), 10, 9);
lean_closure_set(v___f_328_, 0, v___x_319_);
lean_closure_set(v___f_328_, 1, v_resTy_320_);
lean_closure_set(v___f_328_, 2, v_c_321_);
lean_closure_set(v___f_328_, 3, v_dec_327_);
lean_closure_set(v___f_328_, 4, v_k_322_);
lean_closure_set(v___f_328_, 5, v_inst_323_);
lean_closure_set(v___f_328_, 6, v_toBind_324_);
lean_closure_set(v___f_328_, 7, v_inst_325_);
lean_closure_set(v___f_328_, 8, v_inst_326_);
v___x_329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_330_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_325_, v_inst_326_, v___x_329_, v_resTy_320_, v___f_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_box(0);
v___x_338_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3));
v___x_339_ = l_Lean_mkConst(v___x_338_, v___x_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(lean_object* v_resTy_340_, lean_object* v_k_341_, lean_object* v_inst_342_, lean_object* v_toBind_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_c_346_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_347_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_348_ = lean_box(0);
lean_inc_ref(v_inst_345_);
lean_inc_ref(v_inst_344_);
lean_inc_ref(v_c_346_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3), 9, 8);
lean_closure_set(v___f_349_, 0, v___x_348_);
lean_closure_set(v___f_349_, 1, v_resTy_340_);
lean_closure_set(v___f_349_, 2, v_c_346_);
lean_closure_set(v___f_349_, 3, v_k_341_);
lean_closure_set(v___f_349_, 4, v_inst_342_);
lean_closure_set(v___f_349_, 5, v_toBind_343_);
lean_closure_set(v___f_349_, 6, v_inst_344_);
lean_closure_set(v___f_349_, 7, v_inst_345_);
v___x_350_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_351_ = l_Lean_Expr_app___override(v___x_350_, v_c_346_);
v___x_352_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_344_, v_inst_345_, v___x_347_, v___x_351_, v___f_349_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(lean_object* v_c_353_, lean_object* v_resTy_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_mkArrow(v_c_353_, v_resTy_354_, v___y_357_, v___y_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(lean_object* v_c_361_, lean_object* v_resTy_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(v_c_361_, v_resTy_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(lean_object* v___x_369_, lean_object* v_resTy_370_, lean_object* v_c_371_, lean_object* v_dec_372_, lean_object* v_t_373_, lean_object* v_e_374_, lean_object* v_k_375_, lean_object* v_u_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_377_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__3));
v___x_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_378_, 0, v_u_376_);
lean_ctor_set(v___x_378_, 1, v___x_369_);
v___x_379_ = l_Lean_mkConst(v___x_377_, v___x_378_);
lean_inc_ref(v_e_374_);
lean_inc_ref(v_t_373_);
lean_inc_ref(v_dec_372_);
lean_inc_ref(v_c_371_);
v___x_380_ = l_Lean_mkApp5(v___x_379_, v_resTy_370_, v_c_371_, v_dec_372_, v_t_373_, v_e_374_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = lean_unsigned_to_nat(4u);
v___x_383_ = lean_mk_empty_array_with_capacity(v___x_382_);
v___x_384_ = lean_array_push(v___x_383_, v_c_371_);
v___x_385_ = lean_array_push(v___x_384_, v_dec_372_);
v___x_386_ = lean_array_push(v___x_385_, v_t_373_);
v___x_387_ = lean_array_push(v___x_386_, v_e_374_);
v___x_388_ = lean_apply_2(v_k_375_, v___x_381_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(lean_object* v___x_389_, lean_object* v_resTy_390_, lean_object* v_c_391_, lean_object* v_dec_392_, lean_object* v_t_393_, lean_object* v_k_394_, lean_object* v_inst_395_, lean_object* v_toBind_396_, lean_object* v_e_397_){
_start:
{
lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_inc_ref(v_resTy_390_);
v___f_398_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6), 8, 7);
lean_closure_set(v___f_398_, 0, v___x_389_);
lean_closure_set(v___f_398_, 1, v_resTy_390_);
lean_closure_set(v___f_398_, 2, v_c_391_);
lean_closure_set(v___f_398_, 3, v_dec_392_);
lean_closure_set(v___f_398_, 4, v_t_393_);
lean_closure_set(v___f_398_, 5, v_e_397_);
lean_closure_set(v___f_398_, 6, v_k_394_);
v___x_399_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_399_, 0, v_resTy_390_);
v___x_400_ = lean_apply_2(v_inst_395_, lean_box(0), v___x_399_);
v___x_401_ = lean_apply_4(v_toBind_396_, lean_box(0), lean_box(0), v___x_400_, v___f_398_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(lean_object* v___x_402_, lean_object* v_resTy_403_, lean_object* v_c_404_, lean_object* v_dec_405_, lean_object* v_k_406_, lean_object* v_inst_407_, lean_object* v_toBind_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_eTy_411_, lean_object* v_t_412_){
_start:
{
lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7), 9, 8);
lean_closure_set(v___f_413_, 0, v___x_402_);
lean_closure_set(v___f_413_, 1, v_resTy_403_);
lean_closure_set(v___f_413_, 2, v_c_404_);
lean_closure_set(v___f_413_, 3, v_dec_405_);
lean_closure_set(v___f_413_, 4, v_t_412_);
lean_closure_set(v___f_413_, 5, v_k_406_);
lean_closure_set(v___f_413_, 6, v_inst_407_);
lean_closure_set(v___f_413_, 7, v_toBind_408_);
v___x_414_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_415_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_409_, v_inst_410_, v___x_414_, v_eTy_411_, v___f_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(lean_object* v___x_416_, lean_object* v_resTy_417_, lean_object* v_c_418_, lean_object* v_dec_419_, lean_object* v_k_420_, lean_object* v_inst_421_, lean_object* v_toBind_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_tTy_425_, lean_object* v_eTy_426_){
_start:
{
lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_inc_ref(v_inst_424_);
lean_inc_ref(v_inst_423_);
v___f_427_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8), 11, 10);
lean_closure_set(v___f_427_, 0, v___x_416_);
lean_closure_set(v___f_427_, 1, v_resTy_417_);
lean_closure_set(v___f_427_, 2, v_c_418_);
lean_closure_set(v___f_427_, 3, v_dec_419_);
lean_closure_set(v___f_427_, 4, v_k_420_);
lean_closure_set(v___f_427_, 5, v_inst_421_);
lean_closure_set(v___f_427_, 6, v_toBind_422_);
lean_closure_set(v___f_427_, 7, v_inst_423_);
lean_closure_set(v___f_427_, 8, v_inst_424_);
lean_closure_set(v___f_427_, 9, v_eTy_426_);
v___x_428_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_429_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_423_, v_inst_424_, v___x_428_, v_tTy_425_, v___f_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object* v___x_430_, lean_object* v_resTy_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_mkArrow(v___x_430_, v_resTy_431_, v___y_434_, v___y_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object* v___x_438_, lean_object* v_resTy_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(v___x_438_, v_resTy_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object* v___x_446_, lean_object* v_resTy_447_, lean_object* v_c_448_, lean_object* v_dec_449_, lean_object* v_k_450_, lean_object* v_inst_451_, lean_object* v_toBind_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_tTy_455_){
_start:
{
lean_object* v___f_456_; lean_object* v___x_457_; lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_inc(v_toBind_452_);
lean_inc(v_inst_451_);
lean_inc_ref(v_c_448_);
lean_inc_ref(v_resTy_447_);
v___f_456_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9), 11, 10);
lean_closure_set(v___f_456_, 0, v___x_446_);
lean_closure_set(v___f_456_, 1, v_resTy_447_);
lean_closure_set(v___f_456_, 2, v_c_448_);
lean_closure_set(v___f_456_, 3, v_dec_449_);
lean_closure_set(v___f_456_, 4, v_k_450_);
lean_closure_set(v___f_456_, 5, v_inst_451_);
lean_closure_set(v___f_456_, 6, v_toBind_452_);
lean_closure_set(v___f_456_, 7, v_inst_453_);
lean_closure_set(v___f_456_, 8, v_inst_454_);
lean_closure_set(v___f_456_, 9, v_tTy_455_);
v___x_457_ = l_Lean_mkNot(v_c_448_);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed), 7, 2);
lean_closure_set(v___f_458_, 0, v___x_457_);
lean_closure_set(v___f_458_, 1, v_resTy_447_);
v___x_459_ = lean_apply_2(v_inst_451_, lean_box(0), v___f_458_);
v___x_460_ = lean_apply_4(v_toBind_452_, lean_box(0), lean_box(0), v___x_459_, v___f_456_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object* v___x_461_, lean_object* v_resTy_462_, lean_object* v_c_463_, lean_object* v_k_464_, lean_object* v_inst_465_, lean_object* v_toBind_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v___f_469_, lean_object* v_dec_470_){
_start:
{
lean_object* v___f_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_inc(v_toBind_466_);
lean_inc(v_inst_465_);
v___f_471_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11), 10, 9);
lean_closure_set(v___f_471_, 0, v___x_461_);
lean_closure_set(v___f_471_, 1, v_resTy_462_);
lean_closure_set(v___f_471_, 2, v_c_463_);
lean_closure_set(v___f_471_, 3, v_dec_470_);
lean_closure_set(v___f_471_, 4, v_k_464_);
lean_closure_set(v___f_471_, 5, v_inst_465_);
lean_closure_set(v___f_471_, 6, v_toBind_466_);
lean_closure_set(v___f_471_, 7, v_inst_467_);
lean_closure_set(v___f_471_, 8, v_inst_468_);
v___x_472_ = lean_apply_2(v_inst_465_, lean_box(0), v___f_469_);
v___x_473_ = lean_apply_4(v_toBind_466_, lean_box(0), lean_box(0), v___x_472_, v___f_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object* v_resTy_474_, lean_object* v_k_475_, lean_object* v_inst_476_, lean_object* v_toBind_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_c_480_){
_start:
{
lean_object* v___f_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_inc_ref(v_resTy_474_);
lean_inc_ref_n(v_c_480_, 2);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed), 7, 2);
lean_closure_set(v___f_481_, 0, v_c_480_);
lean_closure_set(v___f_481_, 1, v_resTy_474_);
v___x_482_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_483_ = lean_box(0);
lean_inc_ref(v_inst_479_);
lean_inc_ref(v_inst_478_);
v___f_484_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12), 10, 9);
lean_closure_set(v___f_484_, 0, v___x_483_);
lean_closure_set(v___f_484_, 1, v_resTy_474_);
lean_closure_set(v___f_484_, 2, v_c_480_);
lean_closure_set(v___f_484_, 3, v_k_475_);
lean_closure_set(v___f_484_, 4, v_inst_476_);
lean_closure_set(v___f_484_, 5, v_toBind_477_);
lean_closure_set(v___f_484_, 6, v_inst_478_);
lean_closure_set(v___f_484_, 7, v_inst_479_);
lean_closure_set(v___f_484_, 8, v___f_481_);
v___x_485_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_486_ = l_Lean_Expr_app___override(v___x_485_, v_c_480_);
v___x_487_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_478_, v_inst_479_, v___x_482_, v___x_486_, v___f_484_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object* v___x_488_, lean_object* v_resTy_489_, lean_object* v_c_490_, lean_object* v_t_491_, lean_object* v_e_492_, lean_object* v_k_493_, lean_object* v_u_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_495_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__5));
v___x_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_496_, 0, v_u_494_);
lean_ctor_set(v___x_496_, 1, v___x_488_);
v___x_497_ = l_Lean_mkConst(v___x_495_, v___x_496_);
lean_inc_ref(v_e_492_);
lean_inc_ref(v_t_491_);
lean_inc_ref(v_c_490_);
v___x_498_ = l_Lean_mkApp4(v___x_497_, v_resTy_489_, v_c_490_, v_t_491_, v_e_492_);
v___x_499_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
v___x_500_ = lean_unsigned_to_nat(3u);
v___x_501_ = lean_mk_empty_array_with_capacity(v___x_500_);
v___x_502_ = lean_array_push(v___x_501_, v_c_490_);
v___x_503_ = lean_array_push(v___x_502_, v_t_491_);
v___x_504_ = lean_array_push(v___x_503_, v_e_492_);
v___x_505_ = lean_apply_2(v_k_493_, v___x_499_, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object* v___x_506_, lean_object* v_resTy_507_, lean_object* v_c_508_, lean_object* v_t_509_, lean_object* v_k_510_, lean_object* v_inst_511_, lean_object* v_toBind_512_, lean_object* v_e_513_){
_start:
{
lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_inc_ref(v_resTy_507_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14), 7, 6);
lean_closure_set(v___f_514_, 0, v___x_506_);
lean_closure_set(v___f_514_, 1, v_resTy_507_);
lean_closure_set(v___f_514_, 2, v_c_508_);
lean_closure_set(v___f_514_, 3, v_t_509_);
lean_closure_set(v___f_514_, 4, v_e_513_);
lean_closure_set(v___f_514_, 5, v_k_510_);
v___x_515_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_515_, 0, v_resTy_507_);
v___x_516_ = lean_apply_2(v_inst_511_, lean_box(0), v___x_515_);
v___x_517_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v___x_516_, v___f_514_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object* v___x_518_, lean_object* v_resTy_519_, lean_object* v_c_520_, lean_object* v_k_521_, lean_object* v_inst_522_, lean_object* v_toBind_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_t_526_){
_start:
{
lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_inc_ref(v_resTy_519_);
v___f_527_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15), 8, 7);
lean_closure_set(v___f_527_, 0, v___x_518_);
lean_closure_set(v___f_527_, 1, v_resTy_519_);
lean_closure_set(v___f_527_, 2, v_c_520_);
lean_closure_set(v___f_527_, 3, v_t_526_);
lean_closure_set(v___f_527_, 4, v_k_521_);
lean_closure_set(v___f_527_, 5, v_inst_522_);
lean_closure_set(v___f_527_, 6, v_toBind_523_);
v___x_528_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_529_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_524_, v_inst_525_, v___x_528_, v_resTy_519_, v___f_527_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object* v___x_530_, lean_object* v_resTy_531_, lean_object* v_k_532_, lean_object* v_inst_533_, lean_object* v_toBind_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_c_537_){
_start:
{
lean_object* v___f_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_inc_ref(v_inst_536_);
lean_inc_ref(v_inst_535_);
lean_inc_ref(v_resTy_531_);
v___f_538_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16), 9, 8);
lean_closure_set(v___f_538_, 0, v___x_530_);
lean_closure_set(v___f_538_, 1, v_resTy_531_);
lean_closure_set(v___f_538_, 2, v_c_537_);
lean_closure_set(v___f_538_, 3, v_k_532_);
lean_closure_set(v___f_538_, 4, v_inst_533_);
lean_closure_set(v___f_538_, 5, v_toBind_534_);
lean_closure_set(v___f_538_, 6, v_inst_535_);
lean_closure_set(v___f_538_, 7, v_inst_536_);
v___x_539_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_540_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_535_, v_inst_536_, v___x_539_, v_resTy_531_, v___f_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object* v_resTy_541_, lean_object* v_motiveArgs_542_, lean_object* v_x_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; uint8_t v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; 
v___x_549_ = 0;
v___x_550_ = 1;
v___x_551_ = 1;
v___x_552_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_542_, v_resTy_541_, v___x_549_, v___x_550_, v___x_549_, v___x_550_, v___x_551_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(lean_object* v_resTy_553_, lean_object* v_motiveArgs_554_, lean_object* v_x_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(v_resTy_553_, v_motiveArgs_554_, v_x_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec_ref(v_x_555_);
lean_dec_ref(v_motiveArgs_554_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object* v_i_565_, lean_object* v_a_566_, lean_object* v_x_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_568_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1));
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_add(v_i_565_, v___x_569_);
v___x_571_ = lean_name_append_index_after(v___x_568_, v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_a_566_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___boxed(lean_object* v_i_573_, lean_object* v_a_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(v_i_573_, v_a_574_, v_x_575_);
lean_dec(v_i_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object* v_i_577_, lean_object* v___x_578_, lean_object* v_discrs_579_, lean_object* v_prior_580_, lean_object* v_next_581_, lean_object* v_acc_582_, lean_object* v_h_583_, lean_object* v_G_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_a_591_; uint8_t v___x_595_; 
v___x_595_ = lean_nat_dec_lt(v_next_581_, v_i_577_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec_ref(v_G_584_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_acc_582_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_array_get_borrowed(v___x_578_, v_discrs_579_, v_next_581_);
v___x_598_ = l_Lean_Expr_isFVar(v___x_597_);
if (v___x_598_ == 0)
{
v_a_591_ = v_acc_582_;
goto v___jp_590_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_array_get_borrowed(v___x_578_, v_prior_580_, v_next_581_);
lean_inc(v___x_597_);
v___x_600_ = l_Lean_Expr_replaceFVar(v_acc_582_, v___x_597_, v___x_599_);
lean_dec_ref(v_acc_582_);
v_a_591_ = v___x_600_;
goto v___jp_590_;
}
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_next_581_, v___x_592_);
lean_inc(v___y_588_);
lean_inc_ref(v___y_587_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
v___x_594_ = lean_apply_9(v_G_584_, v___x_593_, v_a_591_, lean_box(0), lean_box(0), v___y_585_, v___y_586_, v___y_587_, v___y_588_, lean_box(0));
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object* v_i_601_, lean_object* v___x_602_, lean_object* v_discrs_603_, lean_object* v_prior_604_, lean_object* v_next_605_, lean_object* v_acc_606_, lean_object* v_h_607_, lean_object* v_G_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(v_i_601_, v___x_602_, v_discrs_603_, v_prior_604_, v_next_605_, v_acc_606_, v_h_607_, v_G_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v_next_605_);
lean_dec_ref(v_prior_604_);
lean_dec_ref(v_discrs_603_);
lean_dec_ref(v___x_602_);
lean_dec(v_i_601_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object* v_a_615_, lean_object* v___f_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
v___x_622_ = lean_infer_type(v_a_615_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v___x_2427__overap_625_; lean_object* v___x_626_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_2427__overap_625_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_616_, v___x_624_, v_a_623_, lean_box(0));
v___x_626_ = lean_apply_5(v___x_2427__overap_625_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, lean_box(0));
return v___x_626_;
}
else
{
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec_ref(v___f_616_);
return v___x_622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(lean_object* v_a_627_, lean_object* v___f_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(v_a_627_, v___f_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object* v_i_635_, lean_object* v___x_636_, lean_object* v_discrs_637_, lean_object* v_a_638_, lean_object* v_inst_639_, lean_object* v_prior_640_){
_start:
{
lean_object* v___f_641_; lean_object* v___f_642_; lean_object* v___x_643_; 
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed), 13, 4);
lean_closure_set(v___f_641_, 0, v_i_635_);
lean_closure_set(v___f_641_, 1, v___x_636_);
lean_closure_set(v___f_641_, 2, v_discrs_637_);
lean_closure_set(v___f_641_, 3, v_prior_640_);
v___f_642_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed), 7, 2);
lean_closure_set(v___f_642_, 0, v_a_638_);
lean_closure_set(v___f_642_, 1, v___f_641_);
v___x_643_ = lean_apply_2(v_inst_639_, lean_box(0), v___f_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object* v___x_647_, lean_object* v_discrs_648_, lean_object* v_inst_649_, lean_object* v_i_650_, lean_object* v_a_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___f_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_inc(v_i_650_);
v___f_653_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 6, 5);
lean_closure_set(v___f_653_, 0, v_i_650_);
lean_closure_set(v___f_653_, 1, v___x_647_);
lean_closure_set(v___f_653_, 2, v_discrs_648_);
lean_closure_set(v___f_653_, 3, v_a_651_);
lean_closure_set(v___f_653_, 4, v_inst_649_);
v___x_654_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1));
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_add(v_i_650_, v___x_655_);
lean_dec(v_i_650_);
v___x_657_ = lean_name_append_index_after(v___x_654_, v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___f_653_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object* v_toMatcherInfo_661_, lean_object* v_matcherName_662_, lean_object* v_matcherLevels_663_, lean_object* v_params_664_, lean_object* v_motive_665_, lean_object* v_discrs_666_, lean_object* v_alts_667_, lean_object* v_k_668_, lean_object* v_____do__lift_669_){
_start:
{
lean_object* v___x_670_; lean_object* v_abstractMatcherApp_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
lean_inc_ref(v_discrs_666_);
v_abstractMatcherApp_671_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_abstractMatcherApp_671_, 0, v_toMatcherInfo_661_);
lean_ctor_set(v_abstractMatcherApp_671_, 1, v_matcherName_662_);
lean_ctor_set(v_abstractMatcherApp_671_, 2, v_matcherLevels_663_);
lean_ctor_set(v_abstractMatcherApp_671_, 3, v_params_664_);
lean_ctor_set(v_abstractMatcherApp_671_, 4, v_motive_665_);
lean_ctor_set(v_abstractMatcherApp_671_, 5, v_discrs_666_);
lean_ctor_set(v_abstractMatcherApp_671_, 6, v_____do__lift_669_);
lean_ctor_set(v_abstractMatcherApp_671_, 7, v___x_670_);
v___x_672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_672_, 0, v_abstractMatcherApp_671_);
v___x_673_ = l_Array_append___redArg(v_discrs_666_, v_alts_667_);
v___x_674_ = lean_apply_2(v_k_668_, v___x_672_, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(lean_object* v_toMatcherInfo_675_, lean_object* v_matcherName_676_, lean_object* v_matcherLevels_677_, lean_object* v_params_678_, lean_object* v_motive_679_, lean_object* v_discrs_680_, lean_object* v_alts_681_, lean_object* v_k_682_, lean_object* v_____do__lift_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(v_toMatcherInfo_675_, v_matcherName_676_, v_matcherLevels_677_, v_params_678_, v_motive_679_, v_discrs_680_, v_alts_681_, v_k_682_, v_____do__lift_683_);
lean_dec_ref(v_alts_681_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object* v_toMatcherInfo_686_, lean_object* v_matcherName_687_, lean_object* v_matcherLevels_688_, lean_object* v_params_689_, lean_object* v_motive_690_, lean_object* v_discrs_691_, lean_object* v_k_692_, lean_object* v___x_693_, lean_object* v_inst_694_, lean_object* v_toBind_695_, lean_object* v_alts_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; size_t v_sz_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
lean_inc_ref(v_alts_696_);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed), 9, 8);
lean_closure_set(v___f_697_, 0, v_toMatcherInfo_686_);
lean_closure_set(v___f_697_, 1, v_matcherName_687_);
lean_closure_set(v___f_697_, 2, v_matcherLevels_688_);
lean_closure_set(v___f_697_, 3, v_params_689_);
lean_closure_set(v___f_697_, 4, v_motive_690_);
lean_closure_set(v___f_697_, 5, v_discrs_691_);
lean_closure_set(v___f_697_, 6, v_alts_696_);
lean_closure_set(v___f_697_, 7, v_k_692_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0));
v_sz_699_ = lean_array_size(v_alts_696_);
v___x_700_ = ((size_t)0ULL);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_693_, v___x_698_, v_sz_699_, v___x_700_, v_alts_696_);
v___x_702_ = lean_apply_2(v_inst_694_, lean_box(0), v___x_701_);
v___x_703_ = lean_apply_4(v_toBind_695_, lean_box(0), lean_box(0), v___x_702_, v___f_697_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object* v___f_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v___f_726_, lean_object* v_origAltTypes_727_){
_start:
{
lean_object* v___x_728_; size_t v_sz_729_; size_t v___x_730_; lean_object* v_altNamesTypes_731_; uint8_t v___x_732_; lean_object* v___x_733_; 
v___x_728_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_729_ = lean_array_size(v_origAltTypes_727_);
v___x_730_ = ((size_t)0ULL);
lean_inc_ref(v_origAltTypes_727_);
v_altNamesTypes_731_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_728_, v_origAltTypes_727_, v___f_723_, v_sz_729_, v___x_730_, v_origAltTypes_727_);
lean_dec_ref(v_origAltTypes_727_);
v___x_732_ = 0;
v___x_733_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_724_, v_inst_725_, v_altNamesTypes_731_, v___f_726_, v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object* v_toMatcherInfo_734_, lean_object* v_matcherName_735_, lean_object* v_params_736_, lean_object* v_motive_737_, lean_object* v_discrs_738_, lean_object* v_k_739_, lean_object* v___x_740_, lean_object* v_inst_741_, lean_object* v_toBind_742_, lean_object* v___f_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_alts_746_, lean_object* v_matcherLevels_747_){
_start:
{
lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_matcherPartial_752_; lean_object* v_matcherPartial_753_; lean_object* v_matcherPartial_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_inc(v_toBind_742_);
lean_inc(v_inst_741_);
lean_inc_ref(v_discrs_738_);
lean_inc_ref(v_motive_737_);
lean_inc_ref(v_params_736_);
lean_inc_ref(v_matcherLevels_747_);
lean_inc(v_matcherName_735_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25), 11, 10);
lean_closure_set(v___f_748_, 0, v_toMatcherInfo_734_);
lean_closure_set(v___f_748_, 1, v_matcherName_735_);
lean_closure_set(v___f_748_, 2, v_matcherLevels_747_);
lean_closure_set(v___f_748_, 3, v_params_736_);
lean_closure_set(v___f_748_, 4, v_motive_737_);
lean_closure_set(v___f_748_, 5, v_discrs_738_);
lean_closure_set(v___f_748_, 6, v_k_739_);
lean_closure_set(v___f_748_, 7, v___x_740_);
lean_closure_set(v___f_748_, 8, v_inst_741_);
lean_closure_set(v___f_748_, 9, v_toBind_742_);
v___f_749_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26), 5, 4);
lean_closure_set(v___f_749_, 0, v___f_743_);
lean_closure_set(v___f_749_, 1, v_inst_744_);
lean_closure_set(v___f_749_, 2, v_inst_745_);
lean_closure_set(v___f_749_, 3, v___f_748_);
v___x_750_ = lean_array_to_list(v_matcherLevels_747_);
v___x_751_ = l_Lean_mkConst(v_matcherName_735_, v___x_750_);
v_matcherPartial_752_ = l_Lean_mkAppN(v___x_751_, v_params_736_);
lean_dec_ref(v_params_736_);
v_matcherPartial_753_ = l_Lean_Expr_app___override(v_matcherPartial_752_, v_motive_737_);
v_matcherPartial_754_ = l_Lean_mkAppN(v_matcherPartial_753_, v_discrs_738_);
lean_dec_ref(v_discrs_738_);
v___x_755_ = lean_array_get_size(v_alts_746_);
v___x_756_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_756_, 0, v___x_755_);
lean_closure_set(v___x_756_, 1, v_matcherPartial_754_);
v___x_757_ = lean_apply_2(v_inst_741_, lean_box(0), v___x_756_);
v___x_758_ = lean_apply_4(v_toBind_742_, lean_box(0), lean_box(0), v___x_757_, v___f_749_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object* v_toMatcherInfo_759_, lean_object* v_matcherName_760_, lean_object* v_params_761_, lean_object* v_motive_762_, lean_object* v_discrs_763_, lean_object* v_k_764_, lean_object* v___x_765_, lean_object* v_inst_766_, lean_object* v_toBind_767_, lean_object* v___f_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_alts_771_, lean_object* v_matcherLevels_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(v_toMatcherInfo_759_, v_matcherName_760_, v_params_761_, v_motive_762_, v_discrs_763_, v_k_764_, v___x_765_, v_inst_766_, v_toBind_767_, v___f_768_, v_inst_769_, v_inst_770_, v_alts_771_, v_matcherLevels_772_);
lean_dec_ref(v_alts_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28(lean_object* v___f_774_, lean_object* v_matcherLevels_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = lean_apply_1(v___f_774_, v_matcherLevels_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(lean_object* v_matcherLevels_777_, lean_object* v_val_778_, lean_object* v_toPure_779_, lean_object* v_toBind_780_, lean_object* v___f_781_, lean_object* v_____do__lift_782_){
_start:
{
lean_object* v_uElim_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_uElim_783_ = l_Lean_Level_normalize(v_____do__lift_782_);
v___x_784_ = lean_array_set(v_matcherLevels_777_, v_val_778_, v_uElim_783_);
v___x_785_ = lean_apply_2(v_toPure_779_, lean_box(0), v___x_784_);
v___x_786_ = lean_apply_4(v_toBind_780_, lean_box(0), lean_box(0), v___x_785_, v___f_781_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed(lean_object* v_matcherLevels_787_, lean_object* v_val_788_, lean_object* v_toPure_789_, lean_object* v_toBind_790_, lean_object* v___f_791_, lean_object* v_____do__lift_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(v_matcherLevels_787_, v_val_788_, v_toPure_789_, v_toBind_790_, v___f_791_, v_____do__lift_792_);
lean_dec(v_____do__lift_792_);
lean_dec(v_val_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29(lean_object* v_toMatcherInfo_794_, lean_object* v_matcherName_795_, lean_object* v_params_796_, lean_object* v_discrs_797_, lean_object* v_k_798_, lean_object* v___x_799_, lean_object* v_inst_800_, lean_object* v_toBind_801_, lean_object* v___f_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_alts_805_, lean_object* v_toPure_806_, lean_object* v_matcherLevels_807_, lean_object* v_resTy_808_, lean_object* v_motive_809_){
_start:
{
lean_object* v_uElimPos_x3f_810_; lean_object* v___f_811_; 
v_uElimPos_x3f_810_ = lean_ctor_get(v_toMatcherInfo_794_, 3);
lean_inc(v_uElimPos_x3f_810_);
lean_inc(v_toBind_801_);
lean_inc(v_inst_800_);
v___f_811_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed), 14, 13);
lean_closure_set(v___f_811_, 0, v_toMatcherInfo_794_);
lean_closure_set(v___f_811_, 1, v_matcherName_795_);
lean_closure_set(v___f_811_, 2, v_params_796_);
lean_closure_set(v___f_811_, 3, v_motive_809_);
lean_closure_set(v___f_811_, 4, v_discrs_797_);
lean_closure_set(v___f_811_, 5, v_k_798_);
lean_closure_set(v___f_811_, 6, v___x_799_);
lean_closure_set(v___f_811_, 7, v_inst_800_);
lean_closure_set(v___f_811_, 8, v_toBind_801_);
lean_closure_set(v___f_811_, 9, v___f_802_);
lean_closure_set(v___f_811_, 10, v_inst_803_);
lean_closure_set(v___f_811_, 11, v_inst_804_);
lean_closure_set(v___f_811_, 12, v_alts_805_);
if (lean_obj_tag(v_uElimPos_x3f_810_) == 0)
{
lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec_ref(v_resTy_808_);
lean_dec(v_inst_800_);
v___f_812_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28), 2, 1);
lean_closure_set(v___f_812_, 0, v___f_811_);
v___x_813_ = lean_apply_2(v_toPure_806_, lean_box(0), v_matcherLevels_807_);
v___x_814_ = lean_apply_4(v_toBind_801_, lean_box(0), lean_box(0), v___x_813_, v___f_812_);
return v___x_814_;
}
else
{
lean_object* v_val_815_; lean_object* v___f_816_; lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_val_815_ = lean_ctor_get(v_uElimPos_x3f_810_, 0);
lean_inc(v_val_815_);
lean_dec_ref_known(v_uElimPos_x3f_810_, 1);
v___f_816_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28), 2, 1);
lean_closure_set(v___f_816_, 0, v___f_811_);
lean_inc(v_toBind_801_);
v___f_817_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed), 6, 5);
lean_closure_set(v___f_817_, 0, v_matcherLevels_807_);
lean_closure_set(v___f_817_, 1, v_val_815_);
lean_closure_set(v___f_817_, 2, v_toPure_806_);
lean_closure_set(v___f_817_, 3, v_toBind_801_);
lean_closure_set(v___f_817_, 4, v___f_816_);
v___x_818_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_818_, 0, v_resTy_808_);
v___x_819_ = lean_apply_2(v_inst_800_, lean_box(0), v___x_818_);
v___x_820_ = lean_apply_4(v_toBind_801_, lean_box(0), lean_box(0), v___x_819_, v___f_817_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(lean_object* v_toMatcherInfo_821_, lean_object* v_matcherName_822_, lean_object* v_params_823_, lean_object* v_k_824_, lean_object* v___x_825_, lean_object* v_inst_826_, lean_object* v_toBind_827_, lean_object* v___f_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_alts_831_, lean_object* v_toPure_832_, lean_object* v_matcherLevels_833_, lean_object* v_resTy_834_, lean_object* v___x_835_, lean_object* v_motive_836_, lean_object* v___f_837_, lean_object* v_discrs_838_){
_start:
{
lean_object* v___f_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_inc(v_toBind_827_);
lean_inc(v_inst_826_);
lean_inc_ref(v___x_825_);
v___f_839_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29), 16, 15);
lean_closure_set(v___f_839_, 0, v_toMatcherInfo_821_);
lean_closure_set(v___f_839_, 1, v_matcherName_822_);
lean_closure_set(v___f_839_, 2, v_params_823_);
lean_closure_set(v___f_839_, 3, v_discrs_838_);
lean_closure_set(v___f_839_, 4, v_k_824_);
lean_closure_set(v___f_839_, 5, v___x_825_);
lean_closure_set(v___f_839_, 6, v_inst_826_);
lean_closure_set(v___f_839_, 7, v_toBind_827_);
lean_closure_set(v___f_839_, 8, v___f_828_);
lean_closure_set(v___f_839_, 9, v_inst_829_);
lean_closure_set(v___f_839_, 10, v_inst_830_);
lean_closure_set(v___f_839_, 11, v_alts_831_);
lean_closure_set(v___f_839_, 12, v_toPure_832_);
lean_closure_set(v___f_839_, 13, v_matcherLevels_833_);
lean_closure_set(v___f_839_, 14, v_resTy_834_);
v___x_840_ = 0;
v___x_841_ = l_Lean_Meta_lambdaTelescope___redArg(v___x_835_, v___x_825_, v_motive_836_, v___f_837_, v___x_840_);
v___x_842_ = lean_apply_2(v_inst_826_, lean_box(0), v___x_841_);
v___x_843_ = lean_apply_4(v_toBind_827_, lean_box(0), lean_box(0), v___x_842_, v___f_839_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_844_ = _args[0];
lean_object* v_matcherName_845_ = _args[1];
lean_object* v_params_846_ = _args[2];
lean_object* v_k_847_ = _args[3];
lean_object* v___x_848_ = _args[4];
lean_object* v_inst_849_ = _args[5];
lean_object* v_toBind_850_ = _args[6];
lean_object* v___f_851_ = _args[7];
lean_object* v_inst_852_ = _args[8];
lean_object* v_inst_853_ = _args[9];
lean_object* v_alts_854_ = _args[10];
lean_object* v_toPure_855_ = _args[11];
lean_object* v_matcherLevels_856_ = _args[12];
lean_object* v_resTy_857_ = _args[13];
lean_object* v___x_858_ = _args[14];
lean_object* v_motive_859_ = _args[15];
lean_object* v___f_860_ = _args[16];
lean_object* v_discrs_861_ = _args[17];
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(v_toMatcherInfo_844_, v_matcherName_845_, v_params_846_, v_k_847_, v___x_848_, v_inst_849_, v_toBind_850_, v___f_851_, v_inst_852_, v_inst_853_, v_alts_854_, v_toPure_855_, v_matcherLevels_856_, v_resTy_857_, v___x_858_, v_motive_859_, v___f_860_, v_discrs_861_);
return v_res_862_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0(void){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_instMonadEIO___redArg();
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_865_ = l_StateRefT_x27_instMonad___redArg(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = l_Lean_Level_ofNat(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8);
v___x_876_ = l_Lean_mkSort(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_box(0);
v___x_881_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11));
v___x_882_ = l_Lean_mkConst(v___x_881_, v___x_880_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_info_887_, lean_object* v_resTy_888_, lean_object* v_k_889_){
_start:
{
lean_object* v___x_890_; lean_object* v_toApplicative_891_; lean_object* v_toFunctor_892_; lean_object* v_toSeq_893_; lean_object* v_toSeqLeft_894_; lean_object* v_toSeqRight_895_; lean_object* v___f_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v_toApplicative_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_988_; 
v___x_890_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_891_ = lean_ctor_get(v___x_890_, 0);
v_toFunctor_892_ = lean_ctor_get(v_toApplicative_891_, 0);
v_toSeq_893_ = lean_ctor_get(v_toApplicative_891_, 2);
v_toSeqLeft_894_ = lean_ctor_get(v_toApplicative_891_, 3);
v_toSeqRight_895_ = lean_ctor_get(v_toApplicative_891_, 4);
v___f_896_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_897_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_892_, 2);
v___f_898_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_898_, 0, v_toFunctor_892_);
v___f_899_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_899_, 0, v_toFunctor_892_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___f_898_);
lean_ctor_set(v___x_900_, 1, v___f_899_);
lean_inc(v_toSeqRight_895_);
v___f_901_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_901_, 0, v_toSeqRight_895_);
lean_inc(v_toSeqLeft_894_);
v___f_902_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_902_, 0, v_toSeqLeft_894_);
lean_inc(v_toSeq_893_);
v___f_903_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_903_, 0, v_toSeq_893_);
v___x_904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_904_, 0, v___x_900_);
lean_ctor_set(v___x_904_, 1, v___f_896_);
lean_ctor_set(v___x_904_, 2, v___f_903_);
lean_ctor_set(v___x_904_, 3, v___f_902_);
lean_ctor_set(v___x_904_, 4, v___f_901_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___f_897_);
v___x_906_ = l_StateRefT_x27_instMonad___redArg(v___x_905_);
v_toApplicative_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_906_, 1);
lean_dec(v_unused_989_);
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_988_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_toApplicative_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_988_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_toFunctor_911_; lean_object* v_toSeq_912_; lean_object* v_toSeqLeft_913_; lean_object* v_toSeqRight_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_986_; 
v_toFunctor_911_ = lean_ctor_get(v_toApplicative_907_, 0);
v_toSeq_912_ = lean_ctor_get(v_toApplicative_907_, 2);
v_toSeqLeft_913_ = lean_ctor_get(v_toApplicative_907_, 3);
v_toSeqRight_914_ = lean_ctor_get(v_toApplicative_907_, 4);
v_isSharedCheck_986_ = !lean_is_exclusive(v_toApplicative_907_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; 
v_unused_987_ = lean_ctor_get(v_toApplicative_907_, 1);
lean_dec(v_unused_987_);
v___x_916_ = v_toApplicative_907_;
v_isShared_917_ = v_isSharedCheck_986_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_toSeqRight_914_);
lean_inc(v_toSeqLeft_913_);
lean_inc(v_toSeq_912_);
lean_inc(v_toFunctor_911_);
lean_dec(v_toApplicative_907_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_986_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___f_918_; lean_object* v___f_919_; lean_object* v___f_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___f_924_; lean_object* v___f_925_; lean_object* v___x_927_; 
v___f_918_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_919_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_911_);
v___f_920_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_920_, 0, v_toFunctor_911_);
v___f_921_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_921_, 0, v_toFunctor_911_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___f_920_);
lean_ctor_set(v___x_922_, 1, v___f_921_);
v___f_923_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_923_, 0, v_toSeqRight_914_);
v___f_924_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_924_, 0, v_toSeqLeft_913_);
v___f_925_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_925_, 0, v_toSeq_912_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 4, v___f_923_);
lean_ctor_set(v___x_916_, 3, v___f_924_);
lean_ctor_set(v___x_916_, 2, v___f_925_);
lean_ctor_set(v___x_916_, 1, v___f_918_);
lean_ctor_set(v___x_916_, 0, v___x_922_);
v___x_927_ = v___x_916_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___f_918_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v___f_925_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v___f_924_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v___f_923_);
v___x_927_ = v_reuseFailAlloc_985_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___f_919_);
lean_ctor_set(v___x_909_, 0, v___x_927_);
v___x_929_ = v___x_909_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___f_919_);
v___x_929_ = v_reuseFailAlloc_984_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v_toApplicative_930_; lean_object* v_toFunctor_931_; lean_object* v_toSeq_932_; lean_object* v_toSeqLeft_933_; lean_object* v_toSeqRight_934_; lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___x_937_; lean_object* v___f_938_; lean_object* v___f_939_; lean_object* v___f_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_toApplicative_930_ = lean_ctor_get(v___x_890_, 0);
v_toFunctor_931_ = lean_ctor_get(v_toApplicative_930_, 0);
v_toSeq_932_ = lean_ctor_get(v_toApplicative_930_, 2);
v_toSeqLeft_933_ = lean_ctor_get(v_toApplicative_930_, 3);
v_toSeqRight_934_ = lean_ctor_get(v_toApplicative_930_, 4);
lean_inc_ref_n(v_toFunctor_931_, 2);
v___f_935_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_935_, 0, v_toFunctor_931_);
v___f_936_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_936_, 0, v_toFunctor_931_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___f_935_);
lean_ctor_set(v___x_937_, 1, v___f_936_);
lean_inc(v_toSeqRight_934_);
v___f_938_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_938_, 0, v_toSeqRight_934_);
lean_inc(v_toSeqLeft_933_);
v___f_939_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_939_, 0, v_toSeqLeft_933_);
lean_inc(v_toSeq_932_);
v___f_940_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_940_, 0, v_toSeq_932_);
v___x_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_941_, 0, v___x_937_);
lean_ctor_set(v___x_941_, 1, v___f_896_);
lean_ctor_set(v___x_941_, 2, v___f_940_);
lean_ctor_set(v___x_941_, 3, v___f_939_);
lean_ctor_set(v___x_941_, 4, v___f_938_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___f_897_);
v___x_943_ = l_StateRefT_x27_instMonad___redArg(v___x_942_);
v___x_944_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_944_, 0, lean_box(0));
lean_closure_set(v___x_944_, 1, lean_box(0));
lean_closure_set(v___x_944_, 2, v___x_943_);
v___x_945_ = l_instMonadControlTOfPure___redArg(v___x_944_);
switch(lean_obj_tag(v_info_887_))
{
case 0:
{
lean_object* v_toBind_946_; lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec_ref_known(v_info_887_, 1);
lean_dec_ref(v___x_945_);
lean_dec_ref(v___x_929_);
v_toBind_946_ = lean_ctor_get(v_inst_886_, 1);
lean_inc_ref(v_inst_886_);
lean_inc_ref(v_inst_885_);
lean_inc(v_toBind_946_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_947_, 0, v_resTy_888_);
lean_closure_set(v___f_947_, 1, v_k_889_);
lean_closure_set(v___f_947_, 2, v_inst_884_);
lean_closure_set(v___f_947_, 3, v_toBind_946_);
lean_closure_set(v___f_947_, 4, v_inst_885_);
lean_closure_set(v___f_947_, 5, v_inst_886_);
v___x_948_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_949_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_950_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_885_, v_inst_886_, v___x_948_, v___x_949_, v___f_947_);
return v___x_950_;
}
case 1:
{
lean_object* v_toBind_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec_ref_known(v_info_887_, 1);
lean_dec_ref(v___x_945_);
lean_dec_ref(v___x_929_);
v_toBind_951_ = lean_ctor_get(v_inst_886_, 1);
lean_inc_ref(v_inst_886_);
lean_inc_ref(v_inst_885_);
lean_inc(v_toBind_951_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_952_, 0, v_resTy_888_);
lean_closure_set(v___f_952_, 1, v_k_889_);
lean_closure_set(v___f_952_, 2, v_inst_884_);
lean_closure_set(v___f_952_, 3, v_toBind_951_);
lean_closure_set(v___f_952_, 4, v_inst_885_);
lean_closure_set(v___f_952_, 5, v_inst_886_);
v___x_953_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_954_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_955_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_885_, v_inst_886_, v___x_953_, v___x_954_, v___f_952_);
return v___x_955_;
}
case 2:
{
lean_object* v_toBind_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___f_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref_known(v_info_887_, 1);
lean_dec_ref(v___x_945_);
lean_dec_ref(v___x_929_);
v_toBind_956_ = lean_ctor_get(v_inst_886_, 1);
v___x_957_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_958_ = lean_box(0);
lean_inc_ref(v_inst_886_);
lean_inc_ref(v_inst_885_);
lean_inc(v_toBind_956_);
v___f_959_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17), 8, 7);
lean_closure_set(v___f_959_, 0, v___x_958_);
lean_closure_set(v___f_959_, 1, v_resTy_888_);
lean_closure_set(v___f_959_, 2, v_k_889_);
lean_closure_set(v___f_959_, 3, v_inst_884_);
lean_closure_set(v___f_959_, 4, v_toBind_956_);
lean_closure_set(v___f_959_, 5, v_inst_885_);
lean_closure_set(v___f_959_, 6, v_inst_886_);
v___x_960_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12);
v___x_961_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_885_, v_inst_886_, v___x_957_, v___x_960_, v___f_959_);
return v___x_961_;
}
default: 
{
lean_object* v_toApplicative_962_; lean_object* v_matcherApp_963_; lean_object* v_toBind_964_; lean_object* v_toPure_965_; lean_object* v_toMatcherInfo_966_; lean_object* v_matcherName_967_; lean_object* v_matcherLevels_968_; lean_object* v_params_969_; lean_object* v_motive_970_; lean_object* v_discrs_971_; lean_object* v_alts_972_; lean_object* v___f_973_; lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___x_978_; size_t v_sz_979_; size_t v___x_980_; lean_object* v_discrDecls_981_; uint8_t v___x_982_; lean_object* v___x_983_; 
v_toApplicative_962_ = lean_ctor_get(v_inst_886_, 0);
v_matcherApp_963_ = lean_ctor_get(v_info_887_, 0);
lean_inc_ref(v_matcherApp_963_);
lean_dec_ref_known(v_info_887_, 1);
v_toBind_964_ = lean_ctor_get(v_inst_886_, 1);
v_toPure_965_ = lean_ctor_get(v_toApplicative_962_, 1);
v_toMatcherInfo_966_ = lean_ctor_get(v_matcherApp_963_, 0);
lean_inc_ref(v_toMatcherInfo_966_);
v_matcherName_967_ = lean_ctor_get(v_matcherApp_963_, 1);
lean_inc(v_matcherName_967_);
v_matcherLevels_968_ = lean_ctor_get(v_matcherApp_963_, 2);
lean_inc_ref(v_matcherLevels_968_);
v_params_969_ = lean_ctor_get(v_matcherApp_963_, 3);
lean_inc_ref(v_params_969_);
v_motive_970_ = lean_ctor_get(v_matcherApp_963_, 4);
lean_inc_ref(v_motive_970_);
v_discrs_971_ = lean_ctor_get(v_matcherApp_963_, 5);
lean_inc_ref_n(v_discrs_971_, 3);
v_alts_972_ = lean_ctor_get(v_matcherApp_963_, 6);
lean_inc_ref(v_alts_972_);
lean_dec_ref(v_matcherApp_963_);
lean_inc_ref(v_resTy_888_);
v___f_973_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed), 8, 1);
lean_closure_set(v___f_973_, 0, v_resTy_888_);
v___f_974_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13));
v___x_975_ = l_Lean_instInhabitedExpr;
lean_inc(v_inst_884_);
v___f_976_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23), 6, 3);
lean_closure_set(v___f_976_, 0, v___x_975_);
lean_closure_set(v___f_976_, 1, v_discrs_971_);
lean_closure_set(v___f_976_, 2, v_inst_884_);
lean_inc(v_toPure_965_);
lean_inc_ref(v_inst_886_);
lean_inc_ref(v_inst_885_);
lean_inc(v_toBind_964_);
v___f_977_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_977_, 0, v_toMatcherInfo_966_);
lean_closure_set(v___f_977_, 1, v_matcherName_967_);
lean_closure_set(v___f_977_, 2, v_params_969_);
lean_closure_set(v___f_977_, 3, v_k_889_);
lean_closure_set(v___f_977_, 4, v___x_929_);
lean_closure_set(v___f_977_, 5, v_inst_884_);
lean_closure_set(v___f_977_, 6, v_toBind_964_);
lean_closure_set(v___f_977_, 7, v___f_974_);
lean_closure_set(v___f_977_, 8, v_inst_885_);
lean_closure_set(v___f_977_, 9, v_inst_886_);
lean_closure_set(v___f_977_, 10, v_alts_972_);
lean_closure_set(v___f_977_, 11, v_toPure_965_);
lean_closure_set(v___f_977_, 12, v_matcherLevels_968_);
lean_closure_set(v___f_977_, 13, v_resTy_888_);
lean_closure_set(v___f_977_, 14, v___x_945_);
lean_closure_set(v___f_977_, 15, v_motive_970_);
lean_closure_set(v___f_977_, 16, v___f_973_);
v___x_978_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_979_ = lean_array_size(v_discrs_971_);
v___x_980_ = ((size_t)0ULL);
v_discrDecls_981_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_978_, v_discrs_971_, v___f_976_, v_sz_979_, v___x_980_, v_discrs_971_);
lean_dec_ref(v_discrs_971_);
v___x_982_ = 0;
v___x_983_ = l_Lean_Meta_withLocalDeclsD___redArg(v_inst_885_, v_inst_886_, v_discrDecls_981_, v___f_977_, v___x_982_);
return v___x_983_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_990_, lean_object* v_00_u03b1_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_info_996_, lean_object* v_resTy_997_, lean_object* v_k_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_992_, v_inst_993_, v_inst_994_, v_info_996_, v_resTy_997_, v_k_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_1000_, lean_object* v_00_u03b1_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_info_1006_, lean_object* v_resTy_1007_, lean_object* v_k_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_1000_, v_00_u03b1_1001_, v_inst_1002_, v_inst_1003_, v_inst_1004_, v_inst_1005_, v_info_1006_, v_resTy_1007_, v_k_1008_);
lean_dec(v_inst_1005_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_1010_, lean_object* v_resTy_1011_, lean_object* v_c_1012_, lean_object* v_h_1013_, lean_object* v_t_1014_, lean_object* v_toPure_1015_, lean_object* v_e_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1017_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__1));
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_u_1010_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_mkConst(v___x_1017_, v___x_1019_);
v___x_1021_ = l_Lean_mkApp5(v___x_1020_, v_resTy_1011_, v_c_1012_, v_h_1013_, v_t_1014_, v_e_1016_);
v___x_1022_ = lean_apply_2(v_toPure_1015_, lean_box(0), v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_1026_, lean_object* v_resTy_1027_, lean_object* v_c_1028_, lean_object* v_h_1029_, lean_object* v_toPure_1030_, lean_object* v_onAlt_1031_, lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v_toBind_1034_, lean_object* v_t_1035_){
_start:
{
lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_inc_ref(v_resTy_1027_);
v___f_1036_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1036_, 0, v_u_1026_);
lean_closure_set(v___f_1036_, 1, v_resTy_1027_);
lean_closure_set(v___f_1036_, 2, v_c_1028_);
lean_closure_set(v___f_1036_, 3, v_h_1029_);
lean_closure_set(v___f_1036_, 4, v_t_1035_);
lean_closure_set(v___f_1036_, 5, v_toPure_1030_);
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1038_ = lean_apply_4(v_onAlt_1031_, v___x_1037_, v_resTy_1027_, v___x_1032_, v___x_1033_);
v___x_1039_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v___x_1038_, v___f_1036_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_1040_, uint8_t v_useSplitter_1041_, lean_object* v_inst_1042_, lean_object* v_____do__lift_1043_){
_start:
{
uint8_t v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1044_ = 0;
v___x_1045_ = 1;
v___x_1046_ = lean_box(v___x_1044_);
v___x_1047_ = lean_box(v_useSplitter_1041_);
v___x_1048_ = lean_box(v___x_1044_);
v___x_1049_ = lean_box(v_useSplitter_1041_);
v___x_1050_ = lean_box(v___x_1045_);
v___x_1051_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1051_, 0, v___x_1040_);
lean_closure_set(v___x_1051_, 1, v_____do__lift_1043_);
lean_closure_set(v___x_1051_, 2, v___x_1046_);
lean_closure_set(v___x_1051_, 3, v___x_1047_);
lean_closure_set(v___x_1051_, 4, v___x_1048_);
lean_closure_set(v___x_1051_, 5, v___x_1049_);
lean_closure_set(v___x_1051_, 6, v___x_1050_);
v___x_1052_ = lean_apply_2(v_inst_1042_, lean_box(0), v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_1053_, lean_object* v_useSplitter_1054_, lean_object* v_inst_1055_, lean_object* v_____do__lift_1056_){
_start:
{
uint8_t v_useSplitter_boxed_1057_; lean_object* v_res_1058_; 
v_useSplitter_boxed_1057_ = lean_unbox(v_useSplitter_1054_);
v_res_1058_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_1053_, v_useSplitter_boxed_1057_, v_inst_1055_, v_____do__lift_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_1062_, uint8_t v_useSplitter_1063_, lean_object* v_inst_1064_, lean_object* v_onAlt_1065_, lean_object* v_resTy_1066_, lean_object* v_toBind_1067_, lean_object* v_h_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1072_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1073_ = lean_array_push(v___x_1072_, v_h_1068_);
v___x_1074_ = lean_box(v_useSplitter_1063_);
lean_inc_ref(v___x_1073_);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1075_, 0, v___x_1073_);
lean_closure_set(v___f_1075_, 1, v___x_1074_);
lean_closure_set(v___f_1075_, 2, v_inst_1064_);
v___x_1076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1071_);
lean_ctor_set(v___x_1076_, 1, v___x_1073_);
lean_ctor_set(v___x_1076_, 2, v___x_1071_);
lean_ctor_set(v___x_1076_, 3, v___x_1071_);
lean_ctor_set(v___x_1076_, 4, v___x_1071_);
v___x_1077_ = lean_apply_4(v_onAlt_1065_, v___x_1069_, v_resTy_1066_, v___x_1070_, v___x_1076_);
v___x_1078_ = lean_apply_4(v_toBind_1067_, lean_box(0), lean_box(0), v___x_1077_, v___f_1075_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_1079_, lean_object* v_useSplitter_1080_, lean_object* v_inst_1081_, lean_object* v_onAlt_1082_, lean_object* v_resTy_1083_, lean_object* v_toBind_1084_, lean_object* v_h_1085_){
_start:
{
uint8_t v_useSplitter_boxed_1086_; lean_object* v_res_1087_; 
v_useSplitter_boxed_1086_ = lean_unbox(v_useSplitter_1080_);
v_res_1087_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_1079_, v_useSplitter_boxed_1086_, v_inst_1081_, v_onAlt_1082_, v_resTy_1083_, v_toBind_1084_, v_h_1085_);
lean_dec(v___x_1079_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_1088_, uint8_t v_useSplitter_1089_, lean_object* v_inst_1090_, lean_object* v_onAlt_1091_, lean_object* v_resTy_1092_, lean_object* v_toBind_1093_, lean_object* v_h_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1096_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1097_ = lean_mk_empty_array_with_capacity(v___x_1088_);
v___x_1098_ = lean_array_push(v___x_1097_, v_h_1094_);
v___x_1099_ = lean_box(v_useSplitter_1089_);
lean_inc_ref(v___x_1098_);
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1100_, 0, v___x_1098_);
lean_closure_set(v___f_1100_, 1, v___x_1099_);
lean_closure_set(v___f_1100_, 2, v_inst_1090_);
v___x_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1096_);
lean_ctor_set(v___x_1101_, 1, v___x_1098_);
lean_ctor_set(v___x_1101_, 2, v___x_1096_);
lean_ctor_set(v___x_1101_, 3, v___x_1096_);
lean_ctor_set(v___x_1101_, 4, v___x_1096_);
v___x_1102_ = lean_apply_4(v_onAlt_1091_, v___x_1095_, v_resTy_1092_, v___x_1088_, v___x_1101_);
v___x_1103_ = lean_apply_4(v_toBind_1093_, lean_box(0), lean_box(0), v___x_1102_, v___f_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_1104_, lean_object* v_useSplitter_1105_, lean_object* v_inst_1106_, lean_object* v_onAlt_1107_, lean_object* v_resTy_1108_, lean_object* v_toBind_1109_, lean_object* v_h_1110_){
_start:
{
uint8_t v_useSplitter_boxed_1111_; lean_object* v_res_1112_; 
v_useSplitter_boxed_1111_ = lean_unbox(v_useSplitter_1105_);
v_res_1112_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_1104_, v_useSplitter_boxed_1111_, v_inst_1106_, v_onAlt_1107_, v_resTy_1108_, v_toBind_1109_, v_h_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_1113_, lean_object* v_resTy_1114_, lean_object* v_c_1115_, lean_object* v_h_1116_, lean_object* v_t_1117_, lean_object* v_toPure_1118_, lean_object* v_e_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__3));
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_u_1113_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_mkConst(v___x_1120_, v___x_1122_);
v___x_1124_ = l_Lean_mkApp5(v___x_1123_, v_resTy_1114_, v_c_1115_, v_h_1116_, v_t_1117_, v_e_1119_);
v___x_1125_ = lean_apply_2(v_toPure_1118_, lean_box(0), v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_1126_, lean_object* v_resTy_1127_, lean_object* v_c_1128_, lean_object* v_h_1129_, lean_object* v_toPure_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_n_1133_, uint8_t v___x_1134_, lean_object* v___f_1135_, uint8_t v___x_1136_, lean_object* v_toBind_1137_, lean_object* v_t_1138_){
_start:
{
lean_object* v___f_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc_ref(v_c_1128_);
v___f_1139_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1139_, 0, v_u_1126_);
lean_closure_set(v___f_1139_, 1, v_resTy_1127_);
lean_closure_set(v___f_1139_, 2, v_c_1128_);
lean_closure_set(v___f_1139_, 3, v_h_1129_);
lean_closure_set(v___f_1139_, 4, v_t_1138_);
lean_closure_set(v___f_1139_, 5, v_toPure_1130_);
v___x_1140_ = l_Lean_mkNot(v_c_1128_);
v___x_1141_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1131_, v_inst_1132_, v_n_1133_, v___x_1134_, v___x_1140_, v___f_1135_, v___x_1136_);
v___x_1142_ = lean_apply_4(v_toBind_1137_, lean_box(0), lean_box(0), v___x_1141_, v___f_1139_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_1143_, lean_object* v_resTy_1144_, lean_object* v_c_1145_, lean_object* v_h_1146_, lean_object* v_toPure_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_n_1150_, lean_object* v___x_1151_, lean_object* v___f_1152_, lean_object* v___x_1153_, lean_object* v_toBind_1154_, lean_object* v_t_1155_){
_start:
{
uint8_t v___x_1668__boxed_1156_; uint8_t v___x_1670__boxed_1157_; lean_object* v_res_1158_; 
v___x_1668__boxed_1156_ = lean_unbox(v___x_1151_);
v___x_1670__boxed_1157_ = lean_unbox(v___x_1153_);
v_res_1158_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_1143_, v_resTy_1144_, v_c_1145_, v_h_1146_, v_toPure_1147_, v_inst_1148_, v_inst_1149_, v_n_1150_, v___x_1668__boxed_1156_, v___f_1152_, v___x_1670__boxed_1157_, v_toBind_1154_, v_t_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_1159_, lean_object* v_resTy_1160_, lean_object* v_c_1161_, lean_object* v_h_1162_, lean_object* v_toPure_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v___f_1166_, lean_object* v_toBind_1167_, lean_object* v___f_1168_, lean_object* v_n_1169_){
_start:
{
uint8_t v___x_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1170_ = 0;
v___x_1171_ = 0;
v___x_1172_ = lean_box(v___x_1170_);
v___x_1173_ = lean_box(v___x_1171_);
lean_inc(v_toBind_1167_);
lean_inc(v_n_1169_);
lean_inc_ref(v_inst_1165_);
lean_inc_ref(v_inst_1164_);
lean_inc_ref(v_c_1161_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1174_, 0, v_u_1159_);
lean_closure_set(v___f_1174_, 1, v_resTy_1160_);
lean_closure_set(v___f_1174_, 2, v_c_1161_);
lean_closure_set(v___f_1174_, 3, v_h_1162_);
lean_closure_set(v___f_1174_, 4, v_toPure_1163_);
lean_closure_set(v___f_1174_, 5, v_inst_1164_);
lean_closure_set(v___f_1174_, 6, v_inst_1165_);
lean_closure_set(v___f_1174_, 7, v_n_1169_);
lean_closure_set(v___f_1174_, 8, v___x_1172_);
lean_closure_set(v___f_1174_, 9, v___f_1166_);
lean_closure_set(v___f_1174_, 10, v___x_1173_);
lean_closure_set(v___f_1174_, 11, v_toBind_1167_);
v___x_1175_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1164_, v_inst_1165_, v_n_1169_, v___x_1170_, v_c_1161_, v___f_1168_, v___x_1171_);
v___x_1176_ = lean_apply_4(v_toBind_1167_, lean_box(0), lean_box(0), v___x_1175_, v___f_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Core_mkFreshUserName(v___x_1177_, v___y_1180_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1198_, uint8_t v_useSplitter_1199_, lean_object* v_resTy_1200_, lean_object* v_toPure_1201_, lean_object* v_onAlt_1202_, lean_object* v_toBind_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_u_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_c_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_h_1216_; 
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = l_Lean_Expr_getAppNumArgs(v_e_1198_);
v___x_1210_ = lean_nat_sub(v___x_1209_, v___x_1208_);
v___x_1211_ = lean_nat_sub(v___x_1210_, v___x_1208_);
lean_dec(v___x_1210_);
v_c_1212_ = l_Lean_Expr_getRevArg_x21(v_e_1198_, v___x_1211_);
v___x_1213_ = lean_unsigned_to_nat(2u);
v___x_1214_ = lean_nat_sub(v___x_1209_, v___x_1213_);
lean_dec(v___x_1209_);
v___x_1215_ = lean_nat_sub(v___x_1214_, v___x_1208_);
lean_dec(v___x_1214_);
v_h_1216_ = l_Lean_Expr_getRevArg_x21(v_e_1198_, v___x_1215_);
if (v_useSplitter_1199_ == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec_ref(v_inst_1206_);
lean_dec_ref(v_inst_1205_);
lean_dec(v_inst_1204_);
v___x_1217_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1203_);
lean_inc(v_onAlt_1202_);
lean_inc_ref(v_resTy_1200_);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1220_, 0, v_u_1207_);
lean_closure_set(v___f_1220_, 1, v_resTy_1200_);
lean_closure_set(v___f_1220_, 2, v_c_1212_);
lean_closure_set(v___f_1220_, 3, v_h_1216_);
lean_closure_set(v___f_1220_, 4, v_toPure_1201_);
lean_closure_set(v___f_1220_, 5, v_onAlt_1202_);
lean_closure_set(v___f_1220_, 6, v___x_1208_);
lean_closure_set(v___f_1220_, 7, v___x_1219_);
lean_closure_set(v___f_1220_, 8, v_toBind_1203_);
v___x_1221_ = lean_apply_4(v_onAlt_1202_, v___x_1217_, v_resTy_1200_, v___x_1218_, v___x_1219_);
v___x_1222_ = lean_apply_4(v_toBind_1203_, lean_box(0), lean_box(0), v___x_1221_, v___f_1220_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1223_ = lean_box(v_useSplitter_1199_);
lean_inc_n(v_toBind_1203_, 3);
lean_inc_ref_n(v_resTy_1200_, 2);
lean_inc(v_onAlt_1202_);
lean_inc_n(v_inst_1204_, 2);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1224_, 0, v___x_1208_);
lean_closure_set(v___f_1224_, 1, v___x_1223_);
lean_closure_set(v___f_1224_, 2, v_inst_1204_);
lean_closure_set(v___f_1224_, 3, v_onAlt_1202_);
lean_closure_set(v___f_1224_, 4, v_resTy_1200_);
lean_closure_set(v___f_1224_, 5, v_toBind_1203_);
v___x_1225_ = lean_box(v_useSplitter_1199_);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1226_, 0, v___x_1208_);
lean_closure_set(v___f_1226_, 1, v___x_1225_);
lean_closure_set(v___f_1226_, 2, v_inst_1204_);
lean_closure_set(v___f_1226_, 3, v_onAlt_1202_);
lean_closure_set(v___f_1226_, 4, v_resTy_1200_);
lean_closure_set(v___f_1226_, 5, v_toBind_1203_);
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1227_, 0, v_u_1207_);
lean_closure_set(v___f_1227_, 1, v_resTy_1200_);
lean_closure_set(v___f_1227_, 2, v_c_1212_);
lean_closure_set(v___f_1227_, 3, v_h_1216_);
lean_closure_set(v___f_1227_, 4, v_toPure_1201_);
lean_closure_set(v___f_1227_, 5, v_inst_1205_);
lean_closure_set(v___f_1227_, 6, v_inst_1206_);
lean_closure_set(v___f_1227_, 7, v___f_1226_);
lean_closure_set(v___f_1227_, 8, v_toBind_1203_);
lean_closure_set(v___f_1227_, 9, v___f_1224_);
v___f_1228_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1229_ = lean_apply_2(v_inst_1204_, lean_box(0), v___f_1228_);
v___x_1230_ = lean_apply_4(v_toBind_1203_, lean_box(0), lean_box(0), v___x_1229_, v___f_1227_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1231_, lean_object* v_useSplitter_1232_, lean_object* v_resTy_1233_, lean_object* v_toPure_1234_, lean_object* v_onAlt_1235_, lean_object* v_toBind_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_u_1240_){
_start:
{
uint8_t v_useSplitter_boxed_1241_; lean_object* v_res_1242_; 
v_useSplitter_boxed_1241_ = lean_unbox(v_useSplitter_1232_);
v_res_1242_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1231_, v_useSplitter_boxed_1241_, v_resTy_1233_, v_toPure_1234_, v_onAlt_1235_, v_toBind_1236_, v_inst_1237_, v_inst_1238_, v_inst_1239_, v_u_1240_);
lean_dec_ref(v_e_1231_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1243_, lean_object* v_inst_1244_, lean_object* v_____do__lift_1245_){
_start:
{
uint8_t v___x_1246_; uint8_t v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1246_ = 0;
v___x_1247_ = 1;
v___x_1248_ = 1;
v___x_1249_ = lean_box(v___x_1246_);
v___x_1250_ = lean_box(v___x_1247_);
v___x_1251_ = lean_box(v___x_1246_);
v___x_1252_ = lean_box(v___x_1247_);
v___x_1253_ = lean_box(v___x_1248_);
v___x_1254_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1254_, 0, v___x_1243_);
lean_closure_set(v___x_1254_, 1, v_____do__lift_1245_);
lean_closure_set(v___x_1254_, 2, v___x_1249_);
lean_closure_set(v___x_1254_, 3, v___x_1250_);
lean_closure_set(v___x_1254_, 4, v___x_1251_);
lean_closure_set(v___x_1254_, 5, v___x_1252_);
lean_closure_set(v___x_1254_, 6, v___x_1253_);
v___x_1255_ = lean_apply_2(v_inst_1244_, lean_box(0), v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1256_, lean_object* v_onAlt_1257_, lean_object* v_resTy_1258_, lean_object* v_toBind_1259_, lean_object* v_h_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_mk_empty_array_with_capacity(v___x_1263_);
v___x_1265_ = lean_array_push(v___x_1264_, v_h_1260_);
lean_inc_ref_n(v___x_1265_, 2);
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1266_, 0, v___x_1265_);
lean_closure_set(v___f_1266_, 1, v_inst_1256_);
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1265_);
lean_ctor_set(v___x_1268_, 1, v___x_1265_);
lean_ctor_set(v___x_1268_, 2, v___x_1267_);
lean_ctor_set(v___x_1268_, 3, v___x_1267_);
lean_ctor_set(v___x_1268_, 4, v___x_1267_);
v___x_1269_ = lean_apply_4(v_onAlt_1257_, v___x_1261_, v_resTy_1258_, v___x_1262_, v___x_1268_);
v___x_1270_ = lean_apply_4(v_toBind_1259_, lean_box(0), lean_box(0), v___x_1269_, v___f_1266_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1271_, lean_object* v_inst_1272_, lean_object* v_onAlt_1273_, lean_object* v_resTy_1274_, lean_object* v_toBind_1275_, lean_object* v_h_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1278_ = lean_mk_empty_array_with_capacity(v___x_1271_);
v___x_1279_ = lean_array_push(v___x_1278_, v_h_1276_);
lean_inc_ref_n(v___x_1279_, 2);
v___f_1280_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1280_, 0, v___x_1279_);
lean_closure_set(v___f_1280_, 1, v_inst_1272_);
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1279_);
lean_ctor_set(v___x_1282_, 1, v___x_1279_);
lean_ctor_set(v___x_1282_, 2, v___x_1281_);
lean_ctor_set(v___x_1282_, 3, v___x_1281_);
lean_ctor_set(v___x_1282_, 4, v___x_1281_);
v___x_1283_ = lean_apply_4(v_onAlt_1273_, v___x_1277_, v_resTy_1274_, v___x_1271_, v___x_1282_);
v___x_1284_ = lean_apply_4(v_toBind_1275_, lean_box(0), lean_box(0), v___x_1283_, v___f_1280_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1285_, lean_object* v_onAlt_1286_, lean_object* v_resTy_1287_, lean_object* v_toBind_1288_, lean_object* v_e_1289_, lean_object* v_toPure_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v___f_1293_, lean_object* v_u_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_c_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v_h_1304_; lean_object* v___f_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_toBind_1288_, 2);
lean_inc_ref(v_resTy_1287_);
lean_inc(v_inst_1285_);
v___f_1296_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1296_, 0, v___x_1295_);
lean_closure_set(v___f_1296_, 1, v_inst_1285_);
lean_closure_set(v___f_1296_, 2, v_onAlt_1286_);
lean_closure_set(v___f_1296_, 3, v_resTy_1287_);
lean_closure_set(v___f_1296_, 4, v_toBind_1288_);
v___x_1297_ = l_Lean_Expr_getAppNumArgs(v_e_1289_);
v___x_1298_ = lean_nat_sub(v___x_1297_, v___x_1295_);
v___x_1299_ = lean_nat_sub(v___x_1298_, v___x_1295_);
lean_dec(v___x_1298_);
v_c_1300_ = l_Lean_Expr_getRevArg_x21(v_e_1289_, v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(2u);
v___x_1302_ = lean_nat_sub(v___x_1297_, v___x_1301_);
lean_dec(v___x_1297_);
v___x_1303_ = lean_nat_sub(v___x_1302_, v___x_1295_);
lean_dec(v___x_1302_);
v_h_1304_ = l_Lean_Expr_getRevArg_x21(v_e_1289_, v___x_1303_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1305_, 0, v_u_1294_);
lean_closure_set(v___f_1305_, 1, v_resTy_1287_);
lean_closure_set(v___f_1305_, 2, v_c_1300_);
lean_closure_set(v___f_1305_, 3, v_h_1304_);
lean_closure_set(v___f_1305_, 4, v_toPure_1290_);
lean_closure_set(v___f_1305_, 5, v_inst_1291_);
lean_closure_set(v___f_1305_, 6, v_inst_1292_);
lean_closure_set(v___f_1305_, 7, v___f_1296_);
lean_closure_set(v___f_1305_, 8, v_toBind_1288_);
lean_closure_set(v___f_1305_, 9, v___f_1293_);
v___f_1306_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1307_ = lean_apply_2(v_inst_1285_, lean_box(0), v___f_1306_);
v___x_1308_ = lean_apply_4(v_toBind_1288_, lean_box(0), lean_box(0), v___x_1307_, v___f_1305_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1309_, lean_object* v_onAlt_1310_, lean_object* v_resTy_1311_, lean_object* v_toBind_1312_, lean_object* v_e_1313_, lean_object* v_toPure_1314_, lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v___f_1317_, lean_object* v_u_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1309_, v_onAlt_1310_, v_resTy_1311_, v_toBind_1312_, v_e_1313_, v_toPure_1314_, v_inst_1315_, v_inst_1316_, v___f_1317_, v_u_1318_);
lean_dec_ref(v_e_1313_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_u_1320_, lean_object* v_resTy_1321_, lean_object* v_c_1322_, lean_object* v_t_1323_, lean_object* v_toPure_1324_, lean_object* v_e_1325_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__5));
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_u_1320_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_mkConst(v___x_1326_, v___x_1328_);
v___x_1330_ = l_Lean_mkApp4(v___x_1329_, v_resTy_1321_, v_c_1322_, v_t_1323_, v_e_1325_);
v___x_1331_ = lean_apply_2(v_toPure_1324_, lean_box(0), v___x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_u_1332_, lean_object* v_resTy_1333_, lean_object* v_c_1334_, lean_object* v_toPure_1335_, lean_object* v_onAlt_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v_toBind_1339_, lean_object* v_t_1340_){
_start:
{
lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_inc_ref(v_resTy_1333_);
v___f_1341_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12), 6, 5);
lean_closure_set(v___f_1341_, 0, v_u_1332_);
lean_closure_set(v___f_1341_, 1, v_resTy_1333_);
lean_closure_set(v___f_1341_, 2, v_c_1334_);
lean_closure_set(v___f_1341_, 3, v_t_1340_);
lean_closure_set(v___f_1341_, 4, v_toPure_1335_);
v___x_1342_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1343_ = lean_apply_4(v_onAlt_1336_, v___x_1342_, v_resTy_1333_, v___x_1337_, v___x_1338_);
v___x_1344_ = lean_apply_4(v_toBind_1339_, lean_box(0), lean_box(0), v___x_1343_, v___f_1341_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20(lean_object* v___x_1346_, lean_object* v_u_1347_, lean_object* v___x_1348_, lean_object* v_resTy_1349_, lean_object* v_c_1350_, lean_object* v_t_1351_, lean_object* v_toPure_1352_, lean_object* v_e_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1354_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0));
v___x_1355_ = l_Lean_Name_mkStr2(v___x_1346_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_u_1347_);
lean_ctor_set(v___x_1356_, 1, v___x_1348_);
v___x_1357_ = l_Lean_mkConst(v___x_1355_, v___x_1356_);
v___x_1358_ = l_Lean_mkApp4(v___x_1357_, v_resTy_1349_, v_c_1350_, v_t_1351_, v_e_1353_);
v___x_1359_ = lean_apply_2(v_toPure_1352_, lean_box(0), v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v___x_1360_, lean_object* v_u_1361_, lean_object* v___x_1362_, lean_object* v_resTy_1363_, lean_object* v_c_1364_, lean_object* v_toPure_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_n_1368_, uint8_t v___x_1369_, lean_object* v_hFalse_1370_, lean_object* v___f_1371_, uint8_t v___x_1372_, lean_object* v_toBind_1373_, lean_object* v_t_1374_){
_start:
{
lean_object* v___f_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___f_1375_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20), 8, 7);
lean_closure_set(v___f_1375_, 0, v___x_1360_);
lean_closure_set(v___f_1375_, 1, v_u_1361_);
lean_closure_set(v___f_1375_, 2, v___x_1362_);
lean_closure_set(v___f_1375_, 3, v_resTy_1363_);
lean_closure_set(v___f_1375_, 4, v_c_1364_);
lean_closure_set(v___f_1375_, 5, v_t_1374_);
lean_closure_set(v___f_1375_, 6, v_toPure_1365_);
v___x_1376_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1366_, v_inst_1367_, v_n_1368_, v___x_1369_, v_hFalse_1370_, v___f_1371_, v___x_1372_);
v___x_1377_ = lean_apply_4(v_toBind_1373_, lean_box(0), lean_box(0), v___x_1376_, v___f_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v___x_1378_, lean_object* v_u_1379_, lean_object* v___x_1380_, lean_object* v_resTy_1381_, lean_object* v_c_1382_, lean_object* v_toPure_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_n_1386_, lean_object* v___x_1387_, lean_object* v_hFalse_1388_, lean_object* v___f_1389_, lean_object* v___x_1390_, lean_object* v_toBind_1391_, lean_object* v_t_1392_){
_start:
{
uint8_t v___x_2001__boxed_1393_; uint8_t v___x_2003__boxed_1394_; lean_object* v_res_1395_; 
v___x_2001__boxed_1393_ = lean_unbox(v___x_1387_);
v___x_2003__boxed_1394_ = lean_unbox(v___x_1390_);
v_res_1395_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v___x_1378_, v_u_1379_, v___x_1380_, v_resTy_1381_, v_c_1382_, v_toPure_1383_, v_inst_1384_, v_inst_1385_, v_n_1386_, v___x_2001__boxed_1393_, v_hFalse_1388_, v___f_1389_, v___x_2003__boxed_1394_, v_toBind_1391_, v_t_1392_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(lean_object* v___x_1396_, lean_object* v_u_1397_, lean_object* v___x_1398_, lean_object* v_resTy_1399_, lean_object* v_c_1400_, lean_object* v_toPure_1401_, lean_object* v_inst_1402_, lean_object* v_inst_1403_, lean_object* v_n_1404_, lean_object* v___f_1405_, lean_object* v_toBind_1406_, lean_object* v_hTrue_1407_, lean_object* v___f_1408_, lean_object* v_hFalse_1409_){
_start:
{
uint8_t v___x_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1410_ = 0;
v___x_1411_ = 0;
v___x_1412_ = lean_box(v___x_1410_);
v___x_1413_ = lean_box(v___x_1411_);
lean_inc(v_toBind_1406_);
lean_inc(v_n_1404_);
lean_inc_ref(v_inst_1403_);
lean_inc_ref(v_inst_1402_);
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 15, 14);
lean_closure_set(v___f_1414_, 0, v___x_1396_);
lean_closure_set(v___f_1414_, 1, v_u_1397_);
lean_closure_set(v___f_1414_, 2, v___x_1398_);
lean_closure_set(v___f_1414_, 3, v_resTy_1399_);
lean_closure_set(v___f_1414_, 4, v_c_1400_);
lean_closure_set(v___f_1414_, 5, v_toPure_1401_);
lean_closure_set(v___f_1414_, 6, v_inst_1402_);
lean_closure_set(v___f_1414_, 7, v_inst_1403_);
lean_closure_set(v___f_1414_, 8, v_n_1404_);
lean_closure_set(v___f_1414_, 9, v___x_1412_);
lean_closure_set(v___f_1414_, 10, v_hFalse_1409_);
lean_closure_set(v___f_1414_, 11, v___f_1405_);
lean_closure_set(v___f_1414_, 12, v___x_1413_);
lean_closure_set(v___f_1414_, 13, v_toBind_1406_);
v___x_1415_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1402_, v_inst_1403_, v_n_1404_, v___x_1410_, v_hTrue_1407_, v___f_1408_, v___x_1411_);
v___x_1416_ = lean_apply_4(v_toBind_1406_, lean_box(0), lean_box(0), v___x_1415_, v___f_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18(lean_object* v___x_1418_, lean_object* v_u_1419_, lean_object* v___x_1420_, lean_object* v_resTy_1421_, lean_object* v_c_1422_, lean_object* v_toPure_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_n_1426_, lean_object* v___f_1427_, lean_object* v_toBind_1428_, lean_object* v___f_1429_, lean_object* v_inst_1430_, lean_object* v_hTrue_1431_){
_start:
{
lean_object* v___f_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_inc(v_toBind_1428_);
lean_inc_ref(v_c_1422_);
lean_inc(v___x_1420_);
lean_inc_ref(v___x_1418_);
v___f_1432_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16), 14, 13);
lean_closure_set(v___f_1432_, 0, v___x_1418_);
lean_closure_set(v___f_1432_, 1, v_u_1419_);
lean_closure_set(v___f_1432_, 2, v___x_1420_);
lean_closure_set(v___f_1432_, 3, v_resTy_1421_);
lean_closure_set(v___f_1432_, 4, v_c_1422_);
lean_closure_set(v___f_1432_, 5, v_toPure_1423_);
lean_closure_set(v___f_1432_, 6, v_inst_1424_);
lean_closure_set(v___f_1432_, 7, v_inst_1425_);
lean_closure_set(v___f_1432_, 8, v_n_1426_);
lean_closure_set(v___f_1432_, 9, v___f_1427_);
lean_closure_set(v___f_1432_, 10, v_toBind_1428_);
lean_closure_set(v___f_1432_, 11, v_hTrue_1431_);
lean_closure_set(v___f_1432_, 12, v___f_1429_);
v___x_1433_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0));
v___x_1434_ = l_Lean_Name_mkStr2(v___x_1418_, v___x_1433_);
v___x_1435_ = l_Lean_mkConst(v___x_1434_, v___x_1420_);
v___x_1436_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_1436_, 0, v_c_1422_);
lean_closure_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_apply_2(v_inst_1430_, lean_box(0), v___x_1436_);
v___x_1438_ = lean_apply_4(v_toBind_1428_, lean_box(0), lean_box(0), v___x_1437_, v___f_1432_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_box(0);
v___x_1444_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1));
v___x_1445_ = l_Lean_mkConst(v___x_1444_, v___x_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19(lean_object* v_u_1446_, lean_object* v_resTy_1447_, lean_object* v_c_1448_, lean_object* v_toPure_1449_, lean_object* v_inst_1450_, lean_object* v_inst_1451_, lean_object* v___f_1452_, lean_object* v_toBind_1453_, lean_object* v___f_1454_, lean_object* v_inst_1455_, lean_object* v_n_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1457_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
v___x_1458_ = lean_box(0);
lean_inc(v_inst_1455_);
lean_inc(v_toBind_1453_);
lean_inc_ref(v_c_1448_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18), 14, 13);
lean_closure_set(v___f_1459_, 0, v___x_1457_);
lean_closure_set(v___f_1459_, 1, v_u_1446_);
lean_closure_set(v___f_1459_, 2, v___x_1458_);
lean_closure_set(v___f_1459_, 3, v_resTy_1447_);
lean_closure_set(v___f_1459_, 4, v_c_1448_);
lean_closure_set(v___f_1459_, 5, v_toPure_1449_);
lean_closure_set(v___f_1459_, 6, v_inst_1450_);
lean_closure_set(v___f_1459_, 7, v_inst_1451_);
lean_closure_set(v___f_1459_, 8, v_n_1456_);
lean_closure_set(v___f_1459_, 9, v___f_1452_);
lean_closure_set(v___f_1459_, 10, v_toBind_1453_);
lean_closure_set(v___f_1459_, 11, v___f_1454_);
lean_closure_set(v___f_1459_, 12, v_inst_1455_);
v___x_1460_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2, &l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2);
v___x_1461_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_1461_, 0, v_c_1448_);
lean_closure_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_apply_2(v_inst_1455_, lean_box(0), v___x_1461_);
v___x_1463_ = lean_apply_4(v_toBind_1453_, lean_box(0), lean_box(0), v___x_1462_, v___f_1459_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(lean_object* v_e_1464_, uint8_t v_useSplitter_1465_, lean_object* v_resTy_1466_, lean_object* v_toPure_1467_, lean_object* v_onAlt_1468_, lean_object* v_toBind_1469_, lean_object* v_inst_1470_, lean_object* v_inst_1471_, lean_object* v_inst_1472_, lean_object* v_u_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_c_1478_; 
v___x_1474_ = lean_unsigned_to_nat(1u);
v___x_1475_ = l_Lean_Expr_getAppNumArgs(v_e_1464_);
v___x_1476_ = lean_nat_sub(v___x_1475_, v___x_1474_);
lean_dec(v___x_1475_);
v___x_1477_ = lean_nat_sub(v___x_1476_, v___x_1474_);
lean_dec(v___x_1476_);
v_c_1478_ = l_Lean_Expr_getRevArg_x21(v_e_1464_, v___x_1477_);
if (v_useSplitter_1465_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___f_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec_ref(v_inst_1472_);
lean_dec_ref(v_inst_1471_);
lean_dec(v_inst_1470_);
v___x_1479_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1480_ = lean_unsigned_to_nat(0u);
v___x_1481_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1469_);
lean_inc(v_onAlt_1468_);
lean_inc_ref(v_resTy_1466_);
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14), 9, 8);
lean_closure_set(v___f_1482_, 0, v_u_1473_);
lean_closure_set(v___f_1482_, 1, v_resTy_1466_);
lean_closure_set(v___f_1482_, 2, v_c_1478_);
lean_closure_set(v___f_1482_, 3, v_toPure_1467_);
lean_closure_set(v___f_1482_, 4, v_onAlt_1468_);
lean_closure_set(v___f_1482_, 5, v___x_1474_);
lean_closure_set(v___f_1482_, 6, v___x_1481_);
lean_closure_set(v___f_1482_, 7, v_toBind_1469_);
v___x_1483_ = lean_apply_4(v_onAlt_1468_, v___x_1479_, v_resTy_1466_, v___x_1480_, v___x_1481_);
v___x_1484_ = lean_apply_4(v_toBind_1469_, lean_box(0), lean_box(0), v___x_1483_, v___f_1482_);
return v___x_1484_;
}
else
{
lean_object* v___x_1485_; lean_object* v___f_1486_; lean_object* v___x_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; lean_object* v___f_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1485_ = lean_box(v_useSplitter_1465_);
lean_inc_n(v_toBind_1469_, 3);
lean_inc_ref_n(v_resTy_1466_, 2);
lean_inc(v_onAlt_1468_);
lean_inc_n(v_inst_1470_, 3);
v___f_1486_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1486_, 0, v___x_1474_);
lean_closure_set(v___f_1486_, 1, v___x_1485_);
lean_closure_set(v___f_1486_, 2, v_inst_1470_);
lean_closure_set(v___f_1486_, 3, v_onAlt_1468_);
lean_closure_set(v___f_1486_, 4, v_resTy_1466_);
lean_closure_set(v___f_1486_, 5, v_toBind_1469_);
v___x_1487_ = lean_box(v_useSplitter_1465_);
v___f_1488_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1488_, 0, v___x_1474_);
lean_closure_set(v___f_1488_, 1, v___x_1487_);
lean_closure_set(v___f_1488_, 2, v_inst_1470_);
lean_closure_set(v___f_1488_, 3, v_onAlt_1468_);
lean_closure_set(v___f_1488_, 4, v_resTy_1466_);
lean_closure_set(v___f_1488_, 5, v_toBind_1469_);
v___f_1489_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19), 11, 10);
lean_closure_set(v___f_1489_, 0, v_u_1473_);
lean_closure_set(v___f_1489_, 1, v_resTy_1466_);
lean_closure_set(v___f_1489_, 2, v_c_1478_);
lean_closure_set(v___f_1489_, 3, v_toPure_1467_);
lean_closure_set(v___f_1489_, 4, v_inst_1471_);
lean_closure_set(v___f_1489_, 5, v_inst_1472_);
lean_closure_set(v___f_1489_, 6, v___f_1488_);
lean_closure_set(v___f_1489_, 7, v_toBind_1469_);
lean_closure_set(v___f_1489_, 8, v___f_1486_);
lean_closure_set(v___f_1489_, 9, v_inst_1470_);
v___f_1490_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1491_ = lean_apply_2(v_inst_1470_, lean_box(0), v___f_1490_);
v___x_1492_ = lean_apply_4(v_toBind_1469_, lean_box(0), lean_box(0), v___x_1491_, v___f_1489_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed(lean_object* v_e_1493_, lean_object* v_useSplitter_1494_, lean_object* v_resTy_1495_, lean_object* v_toPure_1496_, lean_object* v_onAlt_1497_, lean_object* v_toBind_1498_, lean_object* v_inst_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_u_1502_){
_start:
{
uint8_t v_useSplitter_boxed_1503_; lean_object* v_res_1504_; 
v_useSplitter_boxed_1503_ = lean_unbox(v_useSplitter_1494_);
v_res_1504_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(v_e_1493_, v_useSplitter_boxed_1503_, v_resTy_1495_, v_toPure_1496_, v_onAlt_1497_, v_toBind_1498_, v_inst_1499_, v_inst_1500_, v_inst_1501_, v_u_1502_);
lean_dec_ref(v_e_1493_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(lean_object* v_onAlt_1505_, lean_object* v_idx_1506_, lean_object* v_expAltType_1507_, lean_object* v_altFVars_1508_, lean_object* v___alt_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1510_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1511_ = lean_unsigned_to_nat(1u);
v___x_1512_ = lean_nat_add(v_idx_1506_, v___x_1511_);
v___x_1513_ = lean_name_append_index_after(v___x_1510_, v___x_1512_);
v___x_1514_ = lean_apply_4(v_onAlt_1505_, v___x_1513_, v_expAltType_1507_, v_idx_1506_, v_altFVars_1508_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed(lean_object* v_onAlt_1515_, lean_object* v_idx_1516_, lean_object* v_expAltType_1517_, lean_object* v_altFVars_1518_, lean_object* v___alt_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(v_onAlt_1515_, v_idx_1516_, v_expAltType_1517_, v_altFVars_1518_, v___alt_1519_);
lean_dec_ref(v___alt_1519_);
return v_res_1520_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(lean_object* v_toMatcherInfo_1521_, lean_object* v_i_1522_, lean_object* v_a_1523_, lean_object* v_x_1524_){
_start:
{
uint8_t v___x_1525_; 
v___x_1525_ = l_Lean_Expr_isFVar(v_a_1523_);
if (v___x_1525_ == 0)
{
return v___x_1525_;
}
else
{
lean_object* v_discrInfos_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_discrInfos_1526_ = lean_ctor_get(v_toMatcherInfo_1521_, 4);
v___x_1527_ = lean_array_get_size(v_discrInfos_1526_);
v___x_1528_ = lean_nat_dec_lt(v_i_1522_, v___x_1527_);
if (v___x_1528_ == 0)
{
return v___x_1525_;
}
else
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_array_fget_borrowed(v_discrInfos_1526_, v_i_1522_);
if (lean_obj_tag(v___x_1529_) == 0)
{
return v___x_1525_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = 0;
return v___x_1530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed(lean_object* v_toMatcherInfo_1531_, lean_object* v_i_1532_, lean_object* v_a_1533_, lean_object* v_x_1534_){
_start:
{
uint8_t v_res_1535_; lean_object* v_r_1536_; 
v_res_1535_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(v_toMatcherInfo_1531_, v_i_1532_, v_a_1533_, v_x_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_i_1532_);
lean_dec_ref(v_toMatcherInfo_1531_);
v_r_1536_ = lean_box(v_res_1535_);
return v_r_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(lean_object* v_mask_1537_, lean_object* v_absMotiveBody_1538_, lean_object* v_toPure_1539_, lean_object* v_xs_1540_, lean_object* v___body_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = l_Lean_Array_mask___redArg(v_mask_1537_, v_xs_1540_);
v___x_1543_ = lean_expr_instantiate_rev(v_absMotiveBody_1538_, v___x_1542_);
lean_dec(v___x_1542_);
v___x_1544_ = lean_apply_2(v_toPure_1539_, lean_box(0), v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed(lean_object* v_mask_1545_, lean_object* v_absMotiveBody_1546_, lean_object* v_toPure_1547_, lean_object* v_xs_1548_, lean_object* v___body_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(v_mask_1545_, v_absMotiveBody_1546_, v_toPure_1547_, v_xs_1548_, v___body_1549_);
lean_dec_ref(v___body_1549_);
lean_dec_ref(v_absMotiveBody_1546_);
lean_dec_ref(v_mask_1545_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(lean_object* v_toFunctor_1551_, lean_object* v_mask_1552_, lean_object* v_toPure_1553_, lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_matcherApp_1559_, uint8_t v_useSplitter_1560_, lean_object* v___f_1561_, lean_object* v___f_1562_, lean_object* v_absMotiveBody_1563_){
_start:
{
lean_object* v_map_1564_; lean_object* v___f_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_map_1564_ = lean_ctor_get(v_toFunctor_1551_, 0);
lean_inc(v_map_1564_);
lean_dec_ref(v_toFunctor_1551_);
lean_inc(v_toPure_1553_);
v___f_1565_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1565_, 0, v_mask_1552_);
lean_closure_set(v___f_1565_, 1, v_absMotiveBody_1563_);
lean_closure_set(v___f_1565_, 2, v_toPure_1553_);
v___x_1566_ = lean_apply_1(v_toPure_1553_, lean_box(0));
lean_inc(v___x_1566_);
v___x_1567_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1554_, v_inst_1555_, v_inst_1556_, v_inst_1557_, v_inst_1558_, v_matcherApp_1559_, v_useSplitter_1560_, v_useSplitter_1560_, v___x_1566_, v___f_1565_, v___f_1561_, v___x_1566_);
v___x_1568_ = lean_apply_4(v_map_1564_, lean_box(0), lean_box(0), v___f_1562_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed(lean_object* v_toFunctor_1569_, lean_object* v_mask_1570_, lean_object* v_toPure_1571_, lean_object* v_inst_1572_, lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_matcherApp_1577_, lean_object* v_useSplitter_1578_, lean_object* v___f_1579_, lean_object* v___f_1580_, lean_object* v_absMotiveBody_1581_){
_start:
{
uint8_t v_useSplitter_boxed_1582_; lean_object* v_res_1583_; 
v_useSplitter_boxed_1582_ = lean_unbox(v_useSplitter_1578_);
v_res_1583_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(v_toFunctor_1569_, v_mask_1570_, v_toPure_1571_, v_inst_1572_, v_inst_1573_, v_inst_1574_, v_inst_1575_, v_inst_1576_, v_matcherApp_1577_, v_useSplitter_boxed_1582_, v___f_1579_, v___f_1580_, v_absMotiveBody_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_inst_1589_, lean_object* v_info_1590_, lean_object* v_resTy_1591_, lean_object* v_onAlt_1592_, uint8_t v_useSplitter_1593_){
_start:
{
switch(lean_obj_tag(v_info_1590_))
{
case 0:
{
lean_object* v_toApplicative_1594_; lean_object* v_toBind_1595_; lean_object* v_toPure_1596_; lean_object* v_e_1597_; lean_object* v___x_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_toApplicative_1594_ = lean_ctor_get(v_inst_1587_, 0);
lean_dec_ref(v_inst_1589_);
lean_dec_ref(v_inst_1588_);
v_toBind_1595_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc_n(v_toBind_1595_, 2);
v_toPure_1596_ = lean_ctor_get(v_toApplicative_1594_, 1);
lean_inc(v_toPure_1596_);
v_e_1597_ = lean_ctor_get(v_info_1590_, 0);
lean_inc_ref(v_e_1597_);
lean_dec_ref_known(v_info_1590_, 1);
v___x_1598_ = lean_box(v_useSplitter_1593_);
lean_inc(v_inst_1585_);
lean_inc_ref(v_resTy_1591_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1599_, 0, v_e_1597_);
lean_closure_set(v___f_1599_, 1, v___x_1598_);
lean_closure_set(v___f_1599_, 2, v_resTy_1591_);
lean_closure_set(v___f_1599_, 3, v_toPure_1596_);
lean_closure_set(v___f_1599_, 4, v_onAlt_1592_);
lean_closure_set(v___f_1599_, 5, v_toBind_1595_);
lean_closure_set(v___f_1599_, 6, v_inst_1585_);
lean_closure_set(v___f_1599_, 7, v_inst_1586_);
lean_closure_set(v___f_1599_, 8, v_inst_1587_);
v___x_1600_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1600_, 0, v_resTy_1591_);
v___x_1601_ = lean_apply_2(v_inst_1585_, lean_box(0), v___x_1600_);
v___x_1602_ = lean_apply_4(v_toBind_1595_, lean_box(0), lean_box(0), v___x_1601_, v___f_1599_);
return v___x_1602_;
}
case 1:
{
lean_object* v_toApplicative_1603_; lean_object* v_toBind_1604_; lean_object* v_toPure_1605_; lean_object* v_e_1606_; lean_object* v___f_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v_toApplicative_1603_ = lean_ctor_get(v_inst_1587_, 0);
lean_dec_ref(v_inst_1589_);
lean_dec_ref(v_inst_1588_);
v_toBind_1604_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc_n(v_toBind_1604_, 3);
v_toPure_1605_ = lean_ctor_get(v_toApplicative_1603_, 1);
lean_inc(v_toPure_1605_);
v_e_1606_ = lean_ctor_get(v_info_1590_, 0);
lean_inc_ref(v_e_1606_);
lean_dec_ref_known(v_info_1590_, 1);
lean_inc_ref_n(v_resTy_1591_, 2);
lean_inc(v_onAlt_1592_);
lean_inc_n(v_inst_1585_, 2);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1607_, 0, v_inst_1585_);
lean_closure_set(v___f_1607_, 1, v_onAlt_1592_);
lean_closure_set(v___f_1607_, 2, v_resTy_1591_);
lean_closure_set(v___f_1607_, 3, v_toBind_1604_);
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1608_, 0, v_inst_1585_);
lean_closure_set(v___f_1608_, 1, v_onAlt_1592_);
lean_closure_set(v___f_1608_, 2, v_resTy_1591_);
lean_closure_set(v___f_1608_, 3, v_toBind_1604_);
lean_closure_set(v___f_1608_, 4, v_e_1606_);
lean_closure_set(v___f_1608_, 5, v_toPure_1605_);
lean_closure_set(v___f_1608_, 6, v_inst_1586_);
lean_closure_set(v___f_1608_, 7, v_inst_1587_);
lean_closure_set(v___f_1608_, 8, v___f_1607_);
v___x_1609_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1609_, 0, v_resTy_1591_);
v___x_1610_ = lean_apply_2(v_inst_1585_, lean_box(0), v___x_1609_);
v___x_1611_ = lean_apply_4(v_toBind_1604_, lean_box(0), lean_box(0), v___x_1610_, v___f_1608_);
return v___x_1611_;
}
case 2:
{
lean_object* v_toApplicative_1612_; lean_object* v_toBind_1613_; lean_object* v_toPure_1614_; lean_object* v_e_1615_; lean_object* v___x_1616_; lean_object* v___f_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_toApplicative_1612_ = lean_ctor_get(v_inst_1587_, 0);
lean_dec_ref(v_inst_1589_);
lean_dec_ref(v_inst_1588_);
v_toBind_1613_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc_n(v_toBind_1613_, 2);
v_toPure_1614_ = lean_ctor_get(v_toApplicative_1612_, 1);
lean_inc(v_toPure_1614_);
v_e_1615_ = lean_ctor_get(v_info_1590_, 0);
lean_inc_ref(v_e_1615_);
lean_dec_ref_known(v_info_1590_, 1);
v___x_1616_ = lean_box(v_useSplitter_1593_);
lean_inc(v_inst_1585_);
lean_inc_ref(v_resTy_1591_);
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed), 10, 9);
lean_closure_set(v___f_1617_, 0, v_e_1615_);
lean_closure_set(v___f_1617_, 1, v___x_1616_);
lean_closure_set(v___f_1617_, 2, v_resTy_1591_);
lean_closure_set(v___f_1617_, 3, v_toPure_1614_);
lean_closure_set(v___f_1617_, 4, v_onAlt_1592_);
lean_closure_set(v___f_1617_, 5, v_toBind_1613_);
lean_closure_set(v___f_1617_, 6, v_inst_1585_);
lean_closure_set(v___f_1617_, 7, v_inst_1586_);
lean_closure_set(v___f_1617_, 8, v_inst_1587_);
v___x_1618_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1618_, 0, v_resTy_1591_);
v___x_1619_ = lean_apply_2(v_inst_1585_, lean_box(0), v___x_1618_);
v___x_1620_ = lean_apply_4(v_toBind_1613_, lean_box(0), lean_box(0), v___x_1619_, v___f_1617_);
return v___x_1620_;
}
default: 
{
lean_object* v_toApplicative_1621_; lean_object* v_matcherApp_1622_; lean_object* v_toBind_1623_; lean_object* v_toFunctor_1624_; lean_object* v_toPure_1625_; lean_object* v_toMatcherInfo_1626_; lean_object* v_discrs_1627_; lean_object* v___f_1628_; lean_object* v___f_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; size_t v_sz_1632_; size_t v___x_1633_; lean_object* v_mask_1634_; lean_object* v___x_1635_; lean_object* v___f_1636_; lean_object* v_maskedDiscrs_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_toApplicative_1621_ = lean_ctor_get(v_inst_1587_, 0);
v_matcherApp_1622_ = lean_ctor_get(v_info_1590_, 0);
lean_inc_ref(v_matcherApp_1622_);
lean_dec_ref_known(v_info_1590_, 1);
v_toBind_1623_ = lean_ctor_get(v_inst_1587_, 1);
lean_inc(v_toBind_1623_);
v_toFunctor_1624_ = lean_ctor_get(v_toApplicative_1621_, 0);
lean_inc_ref(v_toFunctor_1624_);
v_toPure_1625_ = lean_ctor_get(v_toApplicative_1621_, 1);
lean_inc(v_toPure_1625_);
v_toMatcherInfo_1626_ = lean_ctor_get(v_matcherApp_1622_, 0);
v_discrs_1627_ = lean_ctor_get(v_matcherApp_1622_, 5);
lean_inc_ref_n(v_discrs_1627_, 2);
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed), 5, 1);
lean_closure_set(v___f_1628_, 0, v_onAlt_1592_);
v___f_1629_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
lean_inc_ref(v_toMatcherInfo_1626_);
v___f_1630_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed), 4, 1);
lean_closure_set(v___f_1630_, 0, v_toMatcherInfo_1626_);
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_1632_ = lean_array_size(v_discrs_1627_);
v___x_1633_ = ((size_t)0ULL);
v_mask_1634_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1631_, v_discrs_1627_, v___f_1630_, v_sz_1632_, v___x_1633_, v_discrs_1627_);
v___x_1635_ = lean_box(v_useSplitter_1593_);
lean_inc(v_inst_1585_);
lean_inc(v_mask_1634_);
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed), 13, 12);
lean_closure_set(v___f_1636_, 0, v_toFunctor_1624_);
lean_closure_set(v___f_1636_, 1, v_mask_1634_);
lean_closure_set(v___f_1636_, 2, v_toPure_1625_);
lean_closure_set(v___f_1636_, 3, v_inst_1585_);
lean_closure_set(v___f_1636_, 4, v_inst_1586_);
lean_closure_set(v___f_1636_, 5, v_inst_1587_);
lean_closure_set(v___f_1636_, 6, v_inst_1588_);
lean_closure_set(v___f_1636_, 7, v_inst_1589_);
lean_closure_set(v___f_1636_, 8, v_matcherApp_1622_);
lean_closure_set(v___f_1636_, 9, v___x_1635_);
lean_closure_set(v___f_1636_, 10, v___f_1628_);
lean_closure_set(v___f_1636_, 11, v___f_1629_);
v_maskedDiscrs_1637_ = l_Lean_Array_mask___redArg(v_mask_1634_, v_discrs_1627_);
lean_dec(v_mask_1634_);
v___x_1638_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1638_, 0, v_resTy_1591_);
lean_closure_set(v___x_1638_, 1, v_maskedDiscrs_1637_);
v___x_1639_ = lean_apply_2(v_inst_1585_, lean_box(0), v___x_1638_);
v___x_1640_ = lean_apply_4(v_toBind_1623_, lean_box(0), lean_box(0), v___x_1639_, v___f_1636_);
return v___x_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_info_1646_, lean_object* v_resTy_1647_, lean_object* v_onAlt_1648_, lean_object* v_useSplitter_1649_){
_start:
{
uint8_t v_useSplitter_boxed_1650_; lean_object* v_res_1651_; 
v_useSplitter_boxed_1650_ = lean_unbox(v_useSplitter_1649_);
v_res_1651_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1641_, v_inst_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_info_1646_, v_resTy_1647_, v_onAlt_1648_, v_useSplitter_boxed_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_info_1661_, lean_object* v_resTy_1662_, lean_object* v_onAlt_1663_, uint8_t v_useSplitter_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v_inst_1657_, v_info_1661_, v_resTy_1662_, v_onAlt_1663_, v_useSplitter_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1666_, lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_info_1675_, lean_object* v_resTy_1676_, lean_object* v_onAlt_1677_, lean_object* v_useSplitter_1678_){
_start:
{
uint8_t v_useSplitter_boxed_1679_; lean_object* v_res_1680_; 
v_useSplitter_boxed_1679_ = lean_unbox(v_useSplitter_1678_);
v_res_1680_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1666_, v_inst_1667_, v_inst_1668_, v_inst_1669_, v_inst_1670_, v_inst_1671_, v_inst_1672_, v_inst_1673_, v_inst_1674_, v_info_1675_, v_resTy_1676_, v_onAlt_1677_, v_useSplitter_boxed_1679_);
lean_dec_ref(v_inst_1674_);
lean_dec(v_inst_1673_);
lean_dec_ref(v_inst_1672_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1681_, lean_object* v_e_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
if (lean_obj_tag(v_info_1681_) == 3)
{
lean_object* v_matcherApp_1691_; lean_object* v_toMatcherInfo_1692_; lean_object* v___x_1693_; 
v_matcherApp_1691_ = lean_ctor_get(v_info_1681_, 0);
lean_inc_ref(v_matcherApp_1691_);
lean_dec_ref_known(v_info_1681_, 1);
v_toMatcherInfo_1692_ = lean_ctor_get(v_matcherApp_1691_, 0);
lean_inc_ref(v_toMatcherInfo_1692_);
lean_dec_ref(v_matcherApp_1691_);
v___x_1693_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1692_, v_e_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
return v___x_1693_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec_ref(v_e_1682_);
lean_dec_ref(v_info_1681_);
v___x_1694_ = lean_box(0);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1696_, lean_object* v_e_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1696_, v_e_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; lean_object* v_env_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1710_ = lean_st_ref_get(v___y_1708_);
v_env_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc_ref(v_env_1711_);
lean_dec(v___x_1710_);
v___x_1712_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1711_, v_declName_1707_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1714_, v___y_1715_);
lean_dec(v___y_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; lean_object* v_env_1725_; uint8_t v___x_1726_; lean_object* v_env_1727_; lean_object* v___x_1728_; lean_object* v_toCold_1729_; lean_object* v_mctx_1730_; lean_object* v_lctx_1731_; lean_object* v_options_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1724_ = lean_st_ref_get(v___y_1722_);
v_env_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc_ref(v_env_1725_);
lean_dec(v___x_1724_);
v___x_1726_ = 0;
v_env_1727_ = l_Lean_Environment_setRecordingDeps(v_env_1725_, v___x_1726_);
v___x_1728_ = lean_st_ref_get(v___y_1720_);
v_toCold_1729_ = lean_ctor_get(v___y_1721_, 0);
v_mctx_1730_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_ref(v_mctx_1730_);
lean_dec(v___x_1728_);
v_lctx_1731_ = lean_ctor_get(v___y_1719_, 2);
v_options_1732_ = lean_ctor_get(v_toCold_1729_, 2);
lean_inc_ref(v_options_1732_);
lean_inc_ref(v_lctx_1731_);
v___x_1733_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1733_, 0, v_env_1727_);
lean_ctor_set(v___x_1733_, 1, v_mctx_1730_);
lean_ctor_set(v___x_1733_, 2, v_lctx_1731_);
lean_ctor_set(v___x_1733_, 3, v_options_1732_);
v___x_1734_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_ctor_set(v___x_1734_, 1, v_msgData_1718_);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_ref_1749_; lean_object* v___x_1750_; lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1759_; 
v_ref_1749_ = lean_ctor_get(v___y_1746_, 2);
v___x_1750_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1759_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_inc(v_ref_1749_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_ref_1749_);
lean_ctor_set(v___x_1755_, 1, v_a_1751_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set_tag(v___x_1753_, 1);
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_toCold_1774_; lean_object* v_currRecDepth_1775_; lean_object* v_ref_1776_; uint16_t v_optionFlags_1777_; uint8_t v_suppressElabErrors_1778_; uint8_t v_checkDeprecated_1779_; uint8_t v_isRecordingDeps_1780_; lean_object* v_ref_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_toCold_1774_ = lean_ctor_get(v___y_1771_, 0);
v_currRecDepth_1775_ = lean_ctor_get(v___y_1771_, 1);
v_ref_1776_ = lean_ctor_get(v___y_1771_, 2);
v_optionFlags_1777_ = lean_ctor_get_uint16(v___y_1771_, sizeof(void*)*3);
v_suppressElabErrors_1778_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*3 + 2);
v_checkDeprecated_1779_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1780_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*3 + 4);
v_ref_1781_ = l_Lean_replaceRef(v_ref_1767_, v_ref_1776_);
lean_inc(v_currRecDepth_1775_);
lean_inc_ref(v_toCold_1774_);
v___x_1782_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1782_, 0, v_toCold_1774_);
lean_ctor_set(v___x_1782_, 1, v_currRecDepth_1775_);
lean_ctor_set(v___x_1782_, 2, v_ref_1781_);
lean_ctor_set_uint16(v___x_1782_, sizeof(void*)*3, v_optionFlags_1777_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*3 + 2, v_suppressElabErrors_1778_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*3 + 3, v_checkDeprecated_1779_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*3 + 4, v_isRecordingDeps_1780_);
v___x_1783_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1768_, v___y_1769_, v___y_1770_, v___x_1782_, v___y_1772_);
lean_dec_ref_known(v___x_1782_, 3);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1784_, lean_object* v_msg_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1784_, v_msg_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v_ref_1784_);
return v_res_1791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
lean_ctor_set(v___x_1797_, 2, v___x_1796_);
lean_ctor_set(v___x_1797_, 3, v___x_1796_);
lean_ctor_set(v___x_1797_, 4, v___x_1795_);
lean_ctor_set(v___x_1797_, 5, v___x_1795_);
lean_ctor_set(v___x_1797_, 6, v___x_1795_);
lean_ctor_set(v___x_1797_, 7, v___x_1795_);
lean_ctor_set(v___x_1797_, 8, v___x_1795_);
lean_ctor_set(v___x_1797_, 9, v___x_1795_);
lean_ctor_set(v___x_1797_, 10, v___x_1795_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_unsigned_to_nat(32u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1801_ = ((size_t)5ULL);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_unsigned_to_nat(32u);
v___x_1804_ = lean_mk_empty_array_with_capacity(v___x_1803_);
v___x_1805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1806_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v___x_1804_);
lean_ctor_set(v___x_1806_, 2, v___x_1802_);
lean_ctor_set(v___x_1806_, 3, v___x_1802_);
lean_ctor_set_usize(v___x_1806_, 4, v___x_1801_);
return v___x_1806_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = lean_box(1);
v___x_1808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
lean_ctor_set(v___x_1810_, 1, v___x_1808_);
lean_ctor_set(v___x_1810_, 2, v___x_1807_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1844_, lean_object* v_declHint_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_env_1850_; uint8_t v___x_1851_; 
v___x_1848_ = lean_box(0);
v___x_1849_ = lean_st_ref_get(v___y_1846_);
v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_ref(v_env_1850_);
lean_dec(v___x_1849_);
v___x_1851_ = l_Lean_Name_isAnonymous(v_declHint_1845_);
if (v___x_1851_ == 0)
{
uint8_t v_isExporting_1852_; 
v_isExporting_1852_ = lean_ctor_get_uint8(v_env_1850_, sizeof(void*)*13);
if (v_isExporting_1852_ == 0)
{
lean_object* v___x_1853_; 
lean_dec_ref(v_env_1850_);
lean_dec(v_declHint_1845_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_msg_1844_);
return v___x_1853_;
}
else
{
lean_object* v___x_1854_; uint8_t v___x_1855_; 
lean_inc_ref(v_env_1850_);
v___x_1854_ = l_Lean_Environment_setExporting(v_env_1850_, v___x_1851_);
lean_inc(v_declHint_1845_);
lean_inc_ref(v___x_1854_);
v___x_1855_ = l_Lean_Environment_contains(v___x_1854_, v_declHint_1845_, v_isExporting_1852_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
lean_dec_ref(v___x_1854_);
lean_dec_ref(v_env_1850_);
lean_dec(v_declHint_1845_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_msg_1844_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v_c_1862_; lean_object* v___x_1863_; 
v___x_1857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1858_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1859_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1854_);
v___x_1860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1854_);
lean_ctor_set(v___x_1860_, 1, v___x_1857_);
lean_ctor_set(v___x_1860_, 2, v___x_1858_);
lean_ctor_set(v___x_1860_, 3, v___x_1859_);
lean_inc(v_declHint_1845_);
v___x_1861_ = l_Lean_MessageData_ofConstName(v_declHint_1845_, v___x_1851_);
v_c_1862_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1862_, 0, v___x_1860_);
lean_ctor_set(v_c_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1854_, v_declHint_1845_);
lean_dec_ref(v___x_1854_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_dec_ref(v_env_1850_);
lean_dec(v_declHint_1845_);
v___x_1864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v_c_1862_);
v___x_1866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_MessageData_note(v___x_1867_);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_msg_1844_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
else
{
lean_object* v_val_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1924_; 
v_val_1871_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1873_ = v___x_1863_;
v_isShared_1874_ = v_isSharedCheck_1924_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_val_1871_);
lean_dec(v___x_1863_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1924_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v_modules_1876_; lean_object* v_moduleNames_1877_; lean_object* v_mod_1878_; uint8_t v___x_1893_; 
v___x_1875_ = l_Lean_Environment_header(v_env_1850_);
lean_dec_ref(v_env_1850_);
v_modules_1876_ = lean_ctor_get(v___x_1875_, 3);
lean_inc_ref(v_modules_1876_);
v_moduleNames_1877_ = lean_ctor_get(v___x_1875_, 4);
lean_inc_ref(v_moduleNames_1877_);
lean_dec_ref(v___x_1875_);
v_mod_1878_ = lean_array_get(v___x_1848_, v_moduleNames_1877_, v_val_1871_);
lean_dec_ref(v_moduleNames_1877_);
v___x_1893_ = l_Lean_isPrivateName(v_declHint_1845_);
lean_dec(v_declHint_1845_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = lean_array_get_size(v_modules_1876_);
v___x_1895_ = lean_nat_dec_lt(v_val_1871_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_dec_ref(v_modules_1876_);
lean_dec(v_val_1871_);
goto v___jp_1879_;
}
else
{
lean_object* v___x_1896_; lean_object* v_toImport_1897_; uint8_t v_isExported_1898_; 
v___x_1896_ = lean_array_fget(v_modules_1876_, v_val_1871_);
lean_dec(v_val_1871_);
lean_dec_ref(v_modules_1876_);
v_toImport_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc_ref(v_toImport_1897_);
lean_dec(v___x_1896_);
v_isExported_1898_ = lean_ctor_get_uint8(v_toImport_1897_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1897_);
if (v_isExported_1898_ == 0)
{
goto v___jp_1879_;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_del_object(v___x_1873_);
v___x_1899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
lean_ctor_set(v___x_1900_, 1, v_c_1862_);
v___x_1901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l_Lean_MessageData_ofName(v_mod_1878_);
lean_inc_ref(v___x_1903_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21);
v___x_1906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1903_);
v___x_1908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_MessageData_note(v___x_1909_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_msg_1844_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec_ref(v_modules_1876_);
lean_del_object(v___x_1873_);
lean_dec(v_val_1871_);
v___x_1913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v_c_1862_);
v___x_1915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_MessageData_ofName(v_mod_1878_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_MessageData_note(v___x_1920_);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_msg_1844_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
return v___x_1923_;
}
v___jp_1879_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v_c_1862_);
v___x_1882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = l_Lean_MessageData_ofName(v_mod_1878_);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = l_Lean_MessageData_note(v___x_1887_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v_msg_1844_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1889_);
v___x_1891_ = v___x_1873_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1925_; 
lean_dec_ref(v_env_1850_);
lean_dec(v_declHint_1845_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_msg_1844_);
return v___x_1925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1926_, lean_object* v_declHint_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1926_, v_declHint_1927_, v___y_1928_);
lean_dec(v___y_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1931_, lean_object* v_declHint_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1948_; 
v___x_1938_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1931_, v_declHint_1932_, v___y_1936_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1943_ = l_Lean_unknownIdentifierMessageTag;
v___x_1944_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v_a_1939_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1944_);
v___x_1946_ = v___x_1941_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1949_, lean_object* v_declHint_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1949_, v_declHint_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1957_, lean_object* v_msg_1958_, lean_object* v_declHint_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v_a_1966_; lean_object* v___x_1967_; 
v___x_1965_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1958_, v_declHint_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1957_, v_a_1966_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1968_, lean_object* v_msg_1969_, lean_object* v_declHint_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1968_, v_msg_1969_, v_declHint_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v_ref_1968_);
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1983_, lean_object* v_constName_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1990_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1991_ = 0;
lean_inc(v_constName_1984_);
v___x_1992_ = l_Lean_MessageData_ofConstName(v_constName_1984_, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1990_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1983_, v___x_1995_, v_constName_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1997_, lean_object* v_constName_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1997_, v_constName_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v_ref_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_ref_2011_; lean_object* v___x_2012_; 
v_ref_2011_ = lean_ctor_get(v___y_2008_, 2);
v___x_2012_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2011_, v_constName_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v_env_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2026_ = lean_st_ref_get(v___y_2024_);
v_env_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc_ref(v_env_2027_);
lean_dec(v___x_2026_);
v___x_2028_ = 0;
lean_inc(v_constName_2020_);
v___x_2029_ = l_Lean_Environment_find_x3f(v_env_2027_, v_constName_2020_, v___x_2028_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2030_;
}
else
{
lean_object* v_val_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_constName_2020_);
v_val_2031_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2029_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_val_2031_);
lean_dec(v___x_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 0);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_val_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v_toApplicative_2053_; lean_object* v_toFunctor_2054_; lean_object* v_toSeq_2055_; lean_object* v_toSeqLeft_2056_; lean_object* v_toSeqRight_2057_; lean_object* v___f_2058_; lean_object* v___f_2059_; lean_object* v___f_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___f_2063_; lean_object* v___f_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_toApplicative_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2100_; 
v___x_2052_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_2053_ = lean_ctor_get(v___x_2052_, 0);
v_toFunctor_2054_ = lean_ctor_get(v_toApplicative_2053_, 0);
v_toSeq_2055_ = lean_ctor_get(v_toApplicative_2053_, 2);
v_toSeqLeft_2056_ = lean_ctor_get(v_toApplicative_2053_, 3);
v_toSeqRight_2057_ = lean_ctor_get(v_toApplicative_2053_, 4);
v___f_2058_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_2059_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2054_, 2);
v___f_2060_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2060_, 0, v_toFunctor_2054_);
v___f_2061_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2061_, 0, v_toFunctor_2054_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___f_2060_);
lean_ctor_set(v___x_2062_, 1, v___f_2061_);
lean_inc(v_toSeqRight_2057_);
v___f_2063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2063_, 0, v_toSeqRight_2057_);
lean_inc(v_toSeqLeft_2056_);
v___f_2064_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2064_, 0, v_toSeqLeft_2056_);
lean_inc(v_toSeq_2055_);
v___f_2065_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2065_, 0, v_toSeq_2055_);
v___x_2066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2062_);
lean_ctor_set(v___x_2066_, 1, v___f_2058_);
lean_ctor_set(v___x_2066_, 2, v___f_2065_);
lean_ctor_set(v___x_2066_, 3, v___f_2064_);
lean_ctor_set(v___x_2066_, 4, v___f_2063_);
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___f_2059_);
v___x_2068_ = l_StateRefT_x27_instMonad___redArg(v___x_2067_);
v_toApplicative_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2100_ == 0)
{
lean_object* v_unused_2101_; 
v_unused_2101_ = lean_ctor_get(v___x_2068_, 1);
lean_dec(v_unused_2101_);
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2100_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_toApplicative_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2100_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v_toFunctor_2073_; lean_object* v_toSeq_2074_; lean_object* v_toSeqLeft_2075_; lean_object* v_toSeqRight_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2098_; 
v_toFunctor_2073_ = lean_ctor_get(v_toApplicative_2069_, 0);
v_toSeq_2074_ = lean_ctor_get(v_toApplicative_2069_, 2);
v_toSeqLeft_2075_ = lean_ctor_get(v_toApplicative_2069_, 3);
v_toSeqRight_2076_ = lean_ctor_get(v_toApplicative_2069_, 4);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_toApplicative_2069_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; 
v_unused_2099_ = lean_ctor_get(v_toApplicative_2069_, 1);
lean_dec(v_unused_2099_);
v___x_2078_ = v_toApplicative_2069_;
v_isShared_2079_ = v_isSharedCheck_2098_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_toSeqRight_2076_);
lean_inc(v_toSeqLeft_2075_);
lean_inc(v_toSeq_2074_);
lean_inc(v_toFunctor_2073_);
lean_dec(v_toApplicative_2069_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2098_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___f_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___f_2087_; lean_object* v___x_2089_; 
v___f_2080_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_2081_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_2073_);
v___f_2082_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2082_, 0, v_toFunctor_2073_);
v___f_2083_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2083_, 0, v_toFunctor_2073_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___f_2082_);
lean_ctor_set(v___x_2084_, 1, v___f_2083_);
v___f_2085_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2085_, 0, v_toSeqRight_2076_);
v___f_2086_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2086_, 0, v_toSeqLeft_2075_);
v___f_2087_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2087_, 0, v_toSeq_2074_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 4, v___f_2085_);
lean_ctor_set(v___x_2078_, 3, v___f_2086_);
lean_ctor_set(v___x_2078_, 2, v___f_2087_);
lean_ctor_set(v___x_2078_, 1, v___f_2080_);
lean_ctor_set(v___x_2078_, 0, v___x_2084_);
v___x_2089_ = v___x_2078_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___f_2080_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v___f_2087_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v___f_2086_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v___f_2085_);
v___x_2089_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2091_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___f_2081_);
lean_ctor_set(v___x_2071_, 0, v___x_2089_);
v___x_2091_ = v___x_2071_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v___f_2081_);
v___x_2091_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2756__overap_2094_; lean_object* v___x_2095_; 
v___x_2092_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2093_ = l_instInhabitedOfMonad___redArg(v___x_2091_, v___x_2092_);
v___x_2756__overap_2094_ = lean_panic_fn_borrowed(v___x_2093_, v_msg_2046_);
lean_dec(v___x_2093_);
lean_inc(v___y_2050_);
lean_inc_ref(v___y_2049_);
lean_inc(v___y_2048_);
lean_inc_ref(v___y_2047_);
v___x_2095_ = lean_apply_5(v___x_2756__overap_2094_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, lean_box(0));
return v___x_2095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
return v_res_2108_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_2113_ = lean_unsigned_to_nat(53u);
v___x_2114_ = lean_unsigned_to_nat(62u);
v___x_2115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_2116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_2117_ = l_mkPanicMessageWithDecl(v___x_2116_, v___x_2115_, v___x_2114_, v___x_2113_, v___x_2112_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_2118_, size_t v_i_2119_, lean_object* v_bs_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_usize_dec_lt(v_i_2119_, v_sz_2118_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v_bs_2120_);
return v___x_2127_;
}
else
{
lean_object* v_v_2128_; lean_object* v___x_2129_; lean_object* v_bs_x27_2130_; lean_object* v_a_2132_; lean_object* v___x_2137_; 
v_v_2128_ = lean_array_uget(v_bs_2120_, v_i_2119_);
v___x_2129_ = lean_unsigned_to_nat(0u);
v_bs_x27_2130_ = lean_array_uset(v_bs_2120_, v_i_2119_, v___x_2129_);
v___x_2137_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_2128_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
if (lean_obj_tag(v_a_2138_) == 6)
{
lean_object* v_val_2139_; lean_object* v_numFields_2140_; uint8_t v___x_2141_; lean_object* v___x_2142_; 
v_val_2139_ = lean_ctor_get(v_a_2138_, 0);
lean_inc_ref(v_val_2139_);
lean_dec_ref_known(v_a_2138_, 1);
v_numFields_2140_ = lean_ctor_get(v_val_2139_, 4);
lean_inc(v_numFields_2140_);
lean_dec_ref(v_val_2139_);
v___x_2141_ = 0;
v___x_2142_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2142_, 0, v_numFields_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2129_);
lean_ctor_set_uint8(v___x_2142_, sizeof(void*)*2, v___x_2141_);
v_a_2132_ = v___x_2142_;
goto v___jp_2131_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec(v_a_2138_);
v___x_2143_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
v___x_2144_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_2143_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v_a_2132_ = v_a_2145_;
goto v___jp_2131_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v_bs_x27_2130_);
v_a_2146_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_bs_x27_2130_);
v_a_2154_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2137_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2137_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
v___jp_2131_:
{
size_t v___x_2133_; size_t v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = ((size_t)1ULL);
v___x_2134_ = lean_usize_add(v_i_2119_, v___x_2133_);
v___x_2135_ = lean_array_uset(v_bs_x27_2130_, v_i_2119_, v_a_2132_);
v_i_2119_ = v___x_2134_;
v_bs_2120_ = v___x_2135_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_2162_, lean_object* v_i_2163_, lean_object* v_bs_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
size_t v_sz_boxed_2170_; size_t v_i_boxed_2171_; lean_object* v_res_2172_; 
v_sz_boxed_2170_ = lean_unbox_usize(v_sz_2162_);
lean_dec(v_sz_2162_);
v_i_boxed_2171_ = lean_unbox_usize(v_i_2163_);
lean_dec(v_i_2163_);
v_res_2172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_2170_, v_i_boxed_2171_, v_bs_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2172_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_box(0);
v___x_2174_ = lean_unsigned_to_nat(16u);
v___x_2175_ = lean_mk_array(v___x_2174_, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v___x_2177_ = lean_unsigned_to_nat(0u);
v___x_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_2181_, uint8_t v_alsoCasesOn_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = l_Lean_Expr_isApp(v_e_2181_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec_ref(v_e_2181_);
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Expr_getAppFn(v_e_2181_);
if (lean_obj_tag(v___x_2194_) == 4)
{
lean_object* v_declName_2195_; lean_object* v_us_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2351_; 
v_declName_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc_n(v_declName_2195_, 2);
v_us_2196_ = lean_ctor_get(v___x_2194_, 1);
lean_inc(v_us_2196_);
lean_dec_ref_known(v___x_2194_, 2);
v___x_2197_ = l_Lean_instInhabitedExpr;
v___x_2198_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2195_, v___y_2186_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2351_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2351_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
if (lean_obj_tag(v_a_2199_) == 1)
{
lean_object* v_val_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2244_; 
v_val_2203_ = lean_ctor_get(v_a_2199_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v_a_2199_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2205_ = v_a_2199_;
v_isShared_2206_ = v_isSharedCheck_2244_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_val_2203_);
lean_dec(v_a_2199_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2244_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_dummy_2207_; lean_object* v_nargs_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_args_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v_dummy_2207_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0);
v_nargs_2208_ = l_Lean_Expr_getAppNumArgs(v_e_2181_);
lean_inc(v_nargs_2208_);
v___x_2209_ = lean_mk_array(v_nargs_2208_, v_dummy_2207_);
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_sub(v_nargs_2208_, v___x_2210_);
lean_dec(v_nargs_2208_);
v_args_2212_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2181_, v___x_2209_, v___x_2211_);
v___x_2213_ = lean_array_get_size(v_args_2212_);
v___x_2214_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2203_);
v___x_2215_ = lean_nat_dec_lt(v___x_2213_, v___x_2214_);
lean_dec(v___x_2214_);
if (v___x_2215_ == 0)
{
lean_object* v_numParams_2216_; lean_object* v_numDiscrs_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v_numParams_2216_ = lean_ctor_get(v_val_2203_, 0);
v_numDiscrs_2217_ = lean_ctor_get(v_val_2203_, 1);
v___x_2218_ = lean_array_mk(v_us_2196_);
v___x_2219_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2216_);
v___x_2220_ = l_Array_extract___redArg(v_args_2212_, v___x_2219_, v_numParams_2216_);
v___x_2221_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2203_);
v___x_2222_ = lean_array_get(v___x_2197_, v_args_2212_, v___x_2221_);
lean_dec(v___x_2221_);
v___x_2223_ = lean_nat_add(v_numParams_2216_, v___x_2210_);
v___x_2224_ = lean_nat_add(v___x_2223_, v_numDiscrs_2217_);
lean_inc(v___x_2224_);
lean_inc_ref_n(v_args_2212_, 2);
v___x_2225_ = l_Array_toSubarray___redArg(v_args_2212_, v___x_2223_, v___x_2224_);
v___x_2226_ = l_Subarray_copy___redArg(v___x_2225_);
v___x_2227_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2203_);
v___x_2228_ = lean_nat_add(v___x_2224_, v___x_2227_);
lean_dec(v___x_2227_);
lean_inc(v___x_2228_);
v___x_2229_ = l_Array_toSubarray___redArg(v_args_2212_, v___x_2224_, v___x_2228_);
v___x_2230_ = l_Subarray_copy___redArg(v___x_2229_);
v___x_2231_ = l_Array_toSubarray___redArg(v_args_2212_, v___x_2228_, v___x_2213_);
v___x_2232_ = l_Subarray_copy___redArg(v___x_2231_);
v___x_2233_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2233_, 0, v_val_2203_);
lean_ctor_set(v___x_2233_, 1, v_declName_2195_);
lean_ctor_set(v___x_2233_, 2, v___x_2218_);
lean_ctor_set(v___x_2233_, 3, v___x_2220_);
lean_ctor_set(v___x_2233_, 4, v___x_2222_);
lean_ctor_set(v___x_2233_, 5, v___x_2226_);
lean_ctor_set(v___x_2233_, 6, v___x_2230_);
lean_ctor_set(v___x_2233_, 7, v___x_2232_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2233_);
v___x_2235_ = v___x_2205_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2235_);
v___x_2237_ = v___x_2201_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
lean_dec_ref(v_args_2212_);
lean_del_object(v___x_2205_);
lean_dec(v_val_2203_);
lean_dec(v_us_2196_);
lean_dec(v_declName_2195_);
v___x_2240_ = lean_box(0);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2240_);
v___x_2242_ = v___x_2201_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v___x_2245_; 
lean_del_object(v___x_2201_);
lean_dec(v_a_2199_);
v___x_2245_ = lean_st_ref_get(v___y_2186_);
if (v_alsoCasesOn_2182_ == 0)
{
lean_dec(v___x_2245_);
lean_dec(v_us_2196_);
lean_dec(v_declName_2195_);
lean_dec_ref(v_e_2181_);
goto v___jp_2188_;
}
else
{
lean_object* v_env_2246_; uint8_t v___x_2247_; 
v_env_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc_ref(v_env_2246_);
lean_dec(v___x_2245_);
lean_inc(v_declName_2195_);
v___x_2247_ = l_Lean_isCasesOnRecursor(v_env_2246_, v_declName_2195_);
if (v___x_2247_ == 0)
{
lean_dec(v_us_2196_);
lean_dec(v_declName_2195_);
lean_dec_ref(v_e_2181_);
goto v___jp_2188_;
}
else
{
lean_object* v_indName_2248_; lean_object* v___x_2249_; 
v_indName_2248_ = l_Lean_Name_getPrefix(v_declName_2195_);
v___x_2249_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_2248_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2342_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2342_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2342_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
if (lean_obj_tag(v_a_2250_) == 5)
{
lean_object* v_val_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2337_; 
v_val_2254_ = lean_ctor_get(v_a_2250_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_a_2250_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2256_ = v_a_2250_;
v_isShared_2257_ = v_isSharedCheck_2337_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_val_2254_);
lean_dec(v_a_2250_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2337_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_toConstantVal_2258_; lean_object* v_numParams_2259_; lean_object* v_numIndices_2260_; lean_object* v_ctors_2261_; lean_object* v_nargs_2262_; lean_object* v_dummy_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v_args_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_toConstantVal_2258_ = lean_ctor_get(v_val_2254_, 0);
lean_inc_ref(v_toConstantVal_2258_);
v_numParams_2259_ = lean_ctor_get(v_val_2254_, 1);
lean_inc(v_numParams_2259_);
v_numIndices_2260_ = lean_ctor_get(v_val_2254_, 2);
lean_inc(v_numIndices_2260_);
v_ctors_2261_ = lean_ctor_get(v_val_2254_, 4);
lean_inc(v_ctors_2261_);
v_nargs_2262_ = l_Lean_Expr_getAppNumArgs(v_e_2181_);
v_dummy_2263_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_extraArgs___closed__0);
lean_inc(v_nargs_2262_);
v___x_2264_ = lean_mk_array(v_nargs_2262_, v_dummy_2263_);
v___x_2265_ = lean_unsigned_to_nat(1u);
v___x_2266_ = lean_nat_sub(v_nargs_2262_, v___x_2265_);
lean_dec(v_nargs_2262_);
v_args_2267_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2181_, v___x_2264_, v___x_2266_);
v___x_2268_ = lean_nat_add(v_numParams_2259_, v___x_2265_);
v___x_2269_ = lean_nat_add(v___x_2268_, v_numIndices_2260_);
v___x_2270_ = lean_nat_add(v___x_2269_, v___x_2265_);
lean_dec(v___x_2269_);
v___x_2271_ = l_Lean_InductiveVal_numCtors(v_val_2254_);
lean_dec_ref(v_val_2254_);
v___x_2272_ = lean_nat_add(v___x_2270_, v___x_2271_);
lean_dec(v___x_2271_);
v___x_2273_ = lean_array_get_size(v_args_2267_);
v___x_2274_ = lean_nat_dec_le(v___x_2272_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_dec(v___x_2272_);
lean_dec(v___x_2270_);
lean_dec(v___x_2268_);
lean_dec_ref(v_args_2267_);
lean_dec(v_ctors_2261_);
lean_dec(v_numIndices_2260_);
lean_dec(v_numParams_2259_);
lean_dec_ref(v_toConstantVal_2258_);
lean_del_object(v___x_2256_);
lean_dec(v_us_2196_);
lean_dec(v_declName_2195_);
v___x_2275_ = lean_box(0);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2275_);
v___x_2277_ = v___x_2252_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
else
{
lean_object* v___x_2279_; lean_object* v_params_2280_; lean_object* v_motive_2281_; lean_object* v_discrs_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v_discrInfos_2285_; lean_object* v_alts_2286_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v_lower_2328_; lean_object* v_upper_2329_; uint8_t v___x_2336_; 
lean_del_object(v___x_2252_);
v___x_2279_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2259_);
lean_inc_ref_n(v_args_2267_, 3);
v_params_2280_ = l_Array_toSubarray___redArg(v_args_2267_, v___x_2279_, v_numParams_2259_);
v_motive_2281_ = lean_array_get(v___x_2197_, v_args_2267_, v_numParams_2259_);
lean_dec(v_numParams_2259_);
lean_inc(v___x_2270_);
v_discrs_2282_ = l_Array_toSubarray___redArg(v_args_2267_, v___x_2268_, v___x_2270_);
v___x_2283_ = lean_nat_add(v_numIndices_2260_, v___x_2265_);
lean_dec(v_numIndices_2260_);
v___x_2284_ = lean_box(0);
v_discrInfos_2285_ = lean_mk_array(v___x_2283_, v___x_2284_);
lean_inc(v___x_2272_);
v_alts_2286_ = l_Array_toSubarray___redArg(v_args_2267_, v___x_2270_, v___x_2272_);
v___x_2336_ = lean_nat_dec_le(v___x_2272_, v___x_2279_);
if (v___x_2336_ == 0)
{
v_lower_2328_ = v___x_2272_;
v_upper_2329_ = v___x_2273_;
goto v___jp_2327_;
}
else
{
lean_dec(v___x_2272_);
v_lower_2328_ = v___x_2279_;
v_upper_2329_ = v___x_2273_;
goto v___jp_2327_;
}
v___jp_2287_:
{
lean_object* v___x_2290_; size_t v_sz_2291_; size_t v___x_2292_; lean_object* v___x_2293_; 
v___x_2290_ = lean_array_mk(v_ctors_2261_);
v_sz_2291_ = lean_array_size(v___x_2290_);
v___x_2292_ = ((size_t)0ULL);
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_2291_, v___x_2292_, v___x_2290_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2318_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2318_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2318_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_start_2298_; lean_object* v_stop_2299_; lean_object* v_start_2300_; lean_object* v_stop_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v_start_2298_ = lean_ctor_get(v_params_2280_, 1);
v_stop_2299_ = lean_ctor_get(v_params_2280_, 2);
v_start_2300_ = lean_ctor_get(v_discrs_2282_, 1);
v_stop_2301_ = lean_ctor_get(v_discrs_2282_, 2);
v___x_2302_ = lean_nat_sub(v_stop_2299_, v_start_2298_);
v___x_2303_ = lean_nat_sub(v_stop_2301_, v_start_2300_);
v___x_2304_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_2305_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2302_);
lean_ctor_set(v___x_2305_, 1, v___x_2303_);
lean_ctor_set(v___x_2305_, 2, v_a_2294_);
lean_ctor_set(v___x_2305_, 3, v___y_2289_);
lean_ctor_set(v___x_2305_, 4, v_discrInfos_2285_);
lean_ctor_set(v___x_2305_, 5, v___x_2304_);
v___x_2306_ = lean_array_mk(v_us_2196_);
v___x_2307_ = l_Subarray_copy___redArg(v_params_2280_);
v___x_2308_ = l_Subarray_copy___redArg(v_discrs_2282_);
v___x_2309_ = l_Subarray_copy___redArg(v_alts_2286_);
v___x_2310_ = l_Subarray_copy___redArg(v___y_2288_);
v___x_2311_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2305_);
lean_ctor_set(v___x_2311_, 1, v_declName_2195_);
lean_ctor_set(v___x_2311_, 2, v___x_2306_);
lean_ctor_set(v___x_2311_, 3, v___x_2307_);
lean_ctor_set(v___x_2311_, 4, v_motive_2281_);
lean_ctor_set(v___x_2311_, 5, v___x_2308_);
lean_ctor_set(v___x_2311_, 6, v___x_2309_);
lean_ctor_set(v___x_2311_, 7, v___x_2310_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 1);
lean_ctor_set(v___x_2256_, 0, v___x_2311_);
v___x_2313_ = v___x_2256_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2315_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2313_);
v___x_2315_ = v___x_2296_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v_alts_2286_);
lean_dec_ref(v_discrInfos_2285_);
lean_dec_ref(v_discrs_2282_);
lean_dec(v_motive_2281_);
lean_dec_ref(v_params_2280_);
lean_del_object(v___x_2256_);
lean_dec(v_us_2196_);
lean_dec(v_declName_2195_);
v_a_2319_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2293_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2293_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
v___jp_2327_:
{
lean_object* v_levelParams_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_levelParams_2330_ = lean_ctor_get(v_toConstantVal_2258_, 1);
lean_inc(v_levelParams_2330_);
lean_dec_ref(v_toConstantVal_2258_);
v___x_2331_ = l_Array_toSubarray___redArg(v_args_2267_, v_lower_2328_, v_upper_2329_);
v___x_2332_ = l_List_lengthTR___redArg(v_levelParams_2330_);
lean_dec(v_levelParams_2330_);
v___x_2333_ = l_List_lengthTR___redArg(v_us_2196_);
v___x_2334_ = lean_nat_dec_eq(v___x_2332_, v___x_2333_);
lean_dec(v___x_2333_);
lean_dec(v___x_2332_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; 
v___x_2335_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2));
v___y_2288_ = v___x_2331_;
v___y_2289_ = v___x_2335_;
goto v___jp_2287_;
}
else
{
v___y_2288_ = v___x_2331_;
v___y_2289_ = v___x_2284_;
goto v___jp_2287_;
}
}
}
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_dec(v_a_2250_);
lean_dec(v_us_2196_);
lean_dec(v_declName_2195_);
lean_dec_ref(v_e_2181_);
v___x_2338_ = lean_box(0);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2338_);
v___x_2340_ = v___x_2252_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_us_2196_);
lean_dec(v_declName_2195_);
lean_dec_ref(v_e_2181_);
v_a_2343_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2249_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2249_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
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
lean_dec_ref(v___x_2194_);
lean_dec_ref(v_e_2181_);
goto v___jp_2188_;
}
}
v___jp_2188_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_box(0);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_2352_, lean_object* v_alsoCasesOn_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2359_; lean_object* v_res_2360_; 
v_alsoCasesOn_boxed_2359_ = lean_unbox(v_alsoCasesOn_2353_);
v_res_2360_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2352_, v_alsoCasesOn_boxed_2359_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___x_2367_; uint8_t v___x_2368_; 
v___x_2367_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__1));
v___x_2368_ = l_Lean_Expr_isAppOf(v_e_2361_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__3));
v___x_2370_ = l_Lean_Expr_isAppOf(v_e_2361_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__5));
v___x_2372_ = l_Lean_Expr_isAppOf(v_e_2361_, v___x_2371_);
if (v___x_2372_ == 0)
{
uint8_t v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = 1;
v___x_2374_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2361_, v___x_2373_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2395_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2395_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2395_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
if (lean_obj_tag(v_a_2375_) == 1)
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2390_; 
v_val_2379_ = lean_ctor_get(v_a_2375_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_a_2375_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2381_ = v_a_2375_;
v_isShared_2382_ = v_isSharedCheck_2390_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v_a_2375_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2390_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_val_2379_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2385_);
v___x_2387_ = v___x_2377_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
lean_dec(v_a_2375_);
v___x_2391_ = lean_box(0);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 0, v___x_2391_);
v___x_2393_ = v___x_2377_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
v_a_2396_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2374_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2374_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2404_, 0, v_e_2361_);
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2407_, 0, v_e_2361_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
return v___x_2409_;
}
}
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v_e_2361_);
v___x_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
return v___x_2412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2420_, v___y_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2434_, lean_object* v_constName_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_constName_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2442_, v_constName_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2450_, lean_object* v_ref_2451_, lean_object* v_constName_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2451_, v_constName_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2459_, lean_object* v_ref_2460_, lean_object* v_constName_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2459_, v_ref_2460_, v_constName_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v_ref_2460_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2468_, lean_object* v_ref_2469_, lean_object* v_msg_2470_, lean_object* v_declHint_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2469_, v_msg_2470_, v_declHint_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2478_, lean_object* v_ref_2479_, lean_object* v_msg_2480_, lean_object* v_declHint_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2478_, v_ref_2479_, v_msg_2480_, v_declHint_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v_ref_2479_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2488_, lean_object* v_declHint_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2488_, v_declHint_2489_, v___y_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2496_, lean_object* v_declHint_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2496_, v_declHint_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2504_, lean_object* v_ref_2505_, lean_object* v_msg_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2505_, v_msg_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2513_, lean_object* v_ref_2514_, lean_object* v_msg_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2513_, v_ref_2514_, v_msg_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v_ref_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2522_, lean_object* v_msg_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2530_, lean_object* v_msg_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2530_, v_msg_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
return v_res_2537_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2547_, lean_object* v_e_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___y_2555_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__1));
v___x_2583_ = l_Lean_Expr_isAppOf(v_e_2548_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___x_2584_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__3));
v___x_2585_ = l_Lean_Expr_isAppOf(v_e_2548_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2586_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitterName___closed__5));
v___x_2587_ = l_Lean_Expr_isAppOf(v_e_2548_, v___x_2586_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Meta_rwMatcher(v_idx_2547_, v_e_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2588_;
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v_c_2593_; lean_object* v___y_2595_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2589_ = lean_unsigned_to_nat(1u);
v___x_2590_ = l_Lean_Expr_getAppNumArgs(v_e_2548_);
v___x_2591_ = lean_nat_sub(v___x_2590_, v___x_2589_);
lean_dec(v___x_2590_);
v___x_2592_ = lean_nat_sub(v___x_2591_, v___x_2589_);
lean_dec(v___x_2591_);
v_c_2593_ = l_Lean_Expr_getRevArg_x21(v_e_2548_, v___x_2592_);
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = lean_nat_dec_eq(v_idx_2547_, v___x_2625_);
lean_dec(v_idx_2547_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4));
v___y_2595_ = v___x_2627_;
goto v___jp_2594_;
}
else
{
lean_object* v___x_2628_; 
v___x_2628_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1));
v___y_2595_ = v___x_2628_;
goto v___jp_2594_;
}
v___jp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_box(0);
lean_inc(v___y_2595_);
v___x_2597_ = l_Lean_mkConst(v___y_2595_, v___x_2596_);
v___x_2598_ = l_Lean_Meta_mkEq(v_c_2593_, v___x_2597_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc_n(v_a_2599_, 2);
lean_dec_ref_known(v___x_2598_, 1);
v___x_2600_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_a_2599_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
if (lean_obj_tag(v_a_2601_) == 1)
{
lean_object* v_val_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec(v_a_2599_);
v_val_2602_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_val_2602_);
lean_dec_ref_known(v_a_2601_, 1);
v___x_2603_ = l_Lean_mkFVar(v_val_2602_);
v___x_2604_ = l_Lean_Meta_rwIfWith(v___x_2603_, v_e_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2604_;
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec(v_a_2601_);
lean_dec_ref(v_e_2548_);
v___x_2605_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3);
v___x_2606_ = l_Lean_MessageData_ofExpr(v_a_2599_);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2607_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2608_;
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_a_2599_);
lean_dec_ref(v_e_2548_);
v_a_2609_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2600_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2600_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_e_2548_);
v_a_2617_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2598_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2598_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
}
else
{
goto v___jp_2573_;
}
}
else
{
goto v___jp_2573_;
}
v___jp_2554_:
{
lean_object* v___x_2556_; 
lean_inc_ref(v___y_2555_);
v___x_2556_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2555_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
if (lean_obj_tag(v_a_2557_) == 1)
{
lean_object* v_val_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec_ref(v___y_2555_);
v_val_2558_ = lean_ctor_get(v_a_2557_, 0);
lean_inc(v_val_2558_);
lean_dec_ref_known(v_a_2557_, 1);
v___x_2559_ = l_Lean_mkFVar(v_val_2558_);
v___x_2560_ = l_Lean_Meta_rwIfWith(v___x_2559_, v_e_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2560_;
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_dec(v_a_2557_);
lean_dec_ref(v_e_2548_);
v___x_2561_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2562_ = l_Lean_MessageData_ofExpr(v___y_2555_);
v___x_2563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2563_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2564_;
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v___y_2555_);
lean_dec_ref(v_e_2548_);
v_a_2565_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2556_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2556_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
v___jp_2573_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v_c_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2574_ = lean_unsigned_to_nat(1u);
v___x_2575_ = l_Lean_Expr_getAppNumArgs(v_e_2548_);
v___x_2576_ = lean_nat_sub(v___x_2575_, v___x_2574_);
lean_dec(v___x_2575_);
v___x_2577_ = lean_nat_sub(v___x_2576_, v___x_2574_);
lean_dec(v___x_2576_);
v_c_2578_ = l_Lean_Expr_getRevArg_x21(v_e_2548_, v___x_2577_);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_nat_dec_eq(v_idx_2547_, v___x_2579_);
lean_dec(v_idx_2547_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_mkNot(v_c_2578_);
v___y_2555_ = v___x_2581_;
goto v___jp_2554_;
}
else
{
v___y_2555_ = v_c_2578_;
goto v___jp_2554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2629_, lean_object* v_e_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2629_, v_e_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
return v_res_2636_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default = _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default);
l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo = _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* initialize_Lean_Data_Array(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
}
#ifdef __cplusplus
}
#endif
