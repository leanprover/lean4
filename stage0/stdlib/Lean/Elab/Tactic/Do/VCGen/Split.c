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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsDND___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mask___redArg(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withLocalDeclsD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_rwIfWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_rwMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_resTy(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1_value;
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
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 128, 245, 49, 225, 62, 36, 86)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "discr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 61, 20, 168, 108, 94, 13, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_etaExpand___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object**);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value;
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MatcherApp_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isFVar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1_value;
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19;
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
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
lean_object* v_e_9_; lean_object* v___x_10_; 
v_e_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_e_9_);
lean_dec_ref(v_t_7_);
v___x_10_ = lean_apply_1(v_k_8_, v_e_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(lean_object* v_t_23_, lean_object* v_ite_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_23_, v_ite_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_ite_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_27_, v_ite_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(lean_object* v_t_31_, lean_object* v_dite_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_31_, v_dite_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_dite_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_35_, v_dite_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(lean_object* v_t_39_, lean_object* v_matcher_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_39_, v_matcher_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_matcher_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_43_, v_matcher_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1));
v___x_52_ = l_Lean_Expr_const___override(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_zero_59_; uint8_t v_isZero_60_; 
v_zero_59_ = lean_unsigned_to_nat(0u);
v_isZero_60_ = lean_nat_dec_eq(v_x_57_, v_zero_59_);
if (v_isZero_60_ == 1)
{
lean_dec(v_x_57_);
return v_x_58_;
}
else
{
lean_object* v_one_61_; lean_object* v_n_62_; 
v_one_61_ = lean_unsigned_to_nat(1u);
v_n_62_ = lean_nat_sub(v_x_57_, v_one_61_);
lean_dec(v_x_57_);
if (lean_obj_tag(v_x_58_) == 1)
{
lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_74_; 
v_val_63_ = lean_ctor_get(v_x_58_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_74_ == 0)
{
v___x_65_ = v_x_58_;
v_isShared_66_ = v_isSharedCheck_74_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_dec(v_x_58_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_74_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
if (lean_obj_tag(v_val_63_) == 6)
{
lean_object* v_body_67_; lean_object* v___x_69_; 
v_body_67_ = lean_ctor_get(v_val_63_, 2);
lean_inc_ref(v_body_67_);
lean_dec_ref_known(v_val_63_, 3);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v_body_67_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_body_67_);
v___x_69_ = v_reuseFailAlloc_71_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
v_x_57_ = v_n_62_;
v_x_58_ = v___x_69_;
goto _start;
}
}
else
{
lean_object* v___x_72_; 
lean_del_object(v___x_65_);
lean_dec(v_val_63_);
v___x_72_ = lean_box(0);
v_x_57_ = v_n_62_;
v_x_58_ = v___x_72_;
goto _start;
}
}
}
else
{
lean_object* v___x_75_; 
lean_dec(v_x_58_);
v___x_75_ = lean_box(0);
v_x_57_ = v_n_62_;
v_x_58_ = v___x_75_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_resTy(lean_object* v_info_77_){
_start:
{
lean_object* v_e_79_; 
if (lean_obj_tag(v_info_77_) == 2)
{
lean_object* v_matcherApp_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_102_; 
v_matcherApp_85_ = lean_ctor_get(v_info_77_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v_info_77_);
if (v_isSharedCheck_102_ == 0)
{
v___x_87_ = v_info_77_;
v_isShared_88_ = v_isSharedCheck_102_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_matcherApp_85_);
lean_dec(v_info_77_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_102_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_toMatcherInfo_89_; lean_object* v_motive_90_; lean_object* v_discrInfos_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v_toMatcherInfo_89_ = lean_ctor_get(v_matcherApp_85_, 0);
lean_inc_ref(v_toMatcherInfo_89_);
v_motive_90_ = lean_ctor_get(v_matcherApp_85_, 4);
lean_inc_ref_n(v_motive_90_, 2);
lean_dec_ref(v_matcherApp_85_);
v_discrInfos_91_ = lean_ctor_get(v_toMatcherInfo_89_, 4);
lean_inc_ref(v_discrInfos_91_);
lean_dec_ref(v_toMatcherInfo_89_);
v___x_92_ = lean_array_get_size(v_discrInfos_91_);
lean_dec_ref(v_discrInfos_91_);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
lean_ctor_set(v___x_87_, 0, v_motive_90_);
v___x_94_ = v___x_87_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_motive_90_);
v___x_94_ = v_reuseFailAlloc_101_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(v___x_92_, v___x_94_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_dec_ref(v_motive_90_);
return v___x_95_;
}
else
{
lean_object* v_val_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_val_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_val_96_);
v___x_97_ = l_Lean_Expr_looseBVarRange(v_val_96_);
lean_dec(v_val_96_);
v___x_98_ = l_Lean_Expr_looseBVarRange(v_motive_90_);
lean_dec_ref(v_motive_90_);
v___x_99_ = lean_nat_dec_eq(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
lean_dec(v___x_97_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref_known(v___x_95_, 1);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
return v___x_95_;
}
}
}
}
}
else
{
lean_object* v_e_103_; 
v_e_103_ = lean_ctor_get(v_info_77_, 0);
lean_inc_ref(v_e_103_);
lean_dec_ref(v_info_77_);
v_e_79_ = v_e_103_;
goto v___jp_78_;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = l_Lean_Expr_getAppNumArgs(v_e_79_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_sub(v___x_80_, v___x_81_);
lean_dec(v___x_80_);
v___x_83_ = l_Lean_Expr_getRevArg_x21(v_e_79_, v___x_82_);
lean_dec_ref(v_e_79_);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object* v_matcherApp_104_, lean_object* v_as_105_, lean_object* v_i_106_, lean_object* v_j_107_, lean_object* v_bs_108_){
_start:
{
lean_object* v_zero_109_; uint8_t v_isZero_110_; 
v_zero_109_ = lean_unsigned_to_nat(0u);
v_isZero_110_ = lean_nat_dec_eq(v_i_106_, v_zero_109_);
if (v_isZero_110_ == 1)
{
lean_dec(v_j_107_);
lean_dec(v_i_106_);
return v_bs_108_;
}
else
{
lean_object* v_alts_111_; lean_object* v___x_112_; lean_object* v_one_113_; lean_object* v_n_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_alts_111_ = lean_ctor_get(v_matcherApp_104_, 6);
v___x_112_ = l_Lean_instInhabitedExpr;
v_one_113_ = lean_unsigned_to_nat(1u);
v_n_114_ = lean_nat_sub(v_i_106_, v_one_113_);
lean_dec(v_i_106_);
v___x_115_ = lean_array_fget_borrowed(v_as_105_, v_j_107_);
v___x_116_ = lean_array_get_borrowed(v___x_112_, v_alts_111_, v_j_107_);
lean_inc(v___x_116_);
lean_inc(v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = lean_nat_add(v_j_107_, v_one_113_);
lean_dec(v_j_107_);
v___x_119_ = lean_array_push(v_bs_108_, v___x_117_);
v_i_106_ = v_n_114_;
v_j_107_ = v___x_118_;
v_bs_108_ = v___x_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object* v_matcherApp_121_, lean_object* v_as_122_, lean_object* v_i_123_, lean_object* v_j_124_, lean_object* v_bs_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_121_, v_as_122_, v_i_123_, v_j_124_, v_bs_125_);
lean_dec_ref(v_as_122_);
lean_dec_ref(v_matcherApp_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object* v_info_127_){
_start:
{
switch(lean_obj_tag(v_info_127_))
{
case 0:
{
lean_object* v_e_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_e_128_ = lean_ctor_get(v_info_127_, 0);
lean_inc_ref(v_e_128_);
lean_dec_ref_known(v_info_127_, 1);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_unsigned_to_nat(3u);
v___x_131_ = l_Lean_Expr_getAppNumArgs(v_e_128_);
v___x_132_ = lean_nat_sub(v___x_131_, v___x_130_);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_nat_sub(v___x_132_, v___x_133_);
lean_dec(v___x_132_);
v___x_135_ = l_Lean_Expr_getRevArg_x21(v_e_128_, v___x_134_);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_129_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(4u);
v___x_138_ = lean_nat_sub(v___x_131_, v___x_137_);
lean_dec(v___x_131_);
v___x_139_ = lean_nat_sub(v___x_138_, v___x_133_);
lean_dec(v___x_138_);
v___x_140_ = l_Lean_Expr_getRevArg_x21(v_e_128_, v___x_139_);
lean_dec_ref(v_e_128_);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_129_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = lean_unsigned_to_nat(2u);
v___x_143_ = lean_mk_empty_array_with_capacity(v___x_142_);
v___x_144_ = lean_array_push(v___x_143_, v___x_136_);
v___x_145_ = lean_array_push(v___x_144_, v___x_141_);
return v___x_145_;
}
case 1:
{
lean_object* v_e_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_e_146_ = lean_ctor_get(v_info_127_, 0);
lean_inc_ref(v_e_146_);
lean_dec_ref_known(v_info_127_, 1);
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_unsigned_to_nat(3u);
v___x_149_ = l_Lean_Expr_getAppNumArgs(v_e_146_);
v___x_150_ = lean_nat_sub(v___x_149_, v___x_148_);
v___x_151_ = lean_nat_sub(v___x_150_, v___x_147_);
lean_dec(v___x_150_);
v___x_152_ = l_Lean_Expr_getRevArg_x21(v_e_146_, v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_147_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(4u);
v___x_155_ = lean_nat_sub(v___x_149_, v___x_154_);
lean_dec(v___x_149_);
v___x_156_ = lean_nat_sub(v___x_155_, v___x_147_);
lean_dec(v___x_155_);
v___x_157_ = l_Lean_Expr_getRevArg_x21(v_e_146_, v___x_156_);
lean_dec_ref(v_e_146_);
v___x_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_147_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(2u);
v___x_160_ = lean_mk_empty_array_with_capacity(v___x_159_);
v___x_161_ = lean_array_push(v___x_160_, v___x_153_);
v___x_162_ = lean_array_push(v___x_161_, v___x_158_);
return v___x_162_;
}
default: 
{
lean_object* v_matcherApp_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_matcherApp_163_ = lean_ctor_get(v_info_127_, 0);
lean_inc_ref_n(v_matcherApp_163_, 2);
lean_dec_ref_known(v_info_127_, 1);
v___x_164_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_163_);
v___x_165_ = lean_array_get_size(v___x_164_);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_165_);
v___x_168_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_163_, v___x_164_, v___x_165_, v___x_166_, v___x_167_);
lean_dec_ref(v___x_164_);
lean_dec_ref(v_matcherApp_163_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object* v_matcherApp_169_, lean_object* v_as_170_, lean_object* v_i_171_, lean_object* v_j_172_, lean_object* v_inv_173_, lean_object* v_bs_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_169_, v_as_170_, v_i_171_, v_j_172_, v_bs_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object* v_matcherApp_176_, lean_object* v_as_177_, lean_object* v_i_178_, lean_object* v_j_179_, lean_object* v_inv_180_, lean_object* v_bs_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(v_matcherApp_176_, v_as_177_, v_i_178_, v_j_179_, v_inv_180_, v_bs_181_);
lean_dec_ref(v_as_177_);
lean_dec_ref(v_matcherApp_176_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 2)
{
lean_object* v_matcherApp_184_; lean_object* v___x_185_; 
v_matcherApp_184_ = lean_ctor_get(v_x_183_, 0);
lean_inc_ref(v_matcherApp_184_);
lean_dec_ref_known(v_x_183_, 1);
v___x_185_ = l_Lean_Meta_MatcherApp_toExpr(v_matcherApp_184_);
return v___x_185_;
}
else
{
lean_object* v_e_186_; 
v_e_186_ = lean_ctor_get(v_x_183_, 0);
lean_inc_ref(v_e_186_);
lean_dec_ref(v_x_183_);
return v_e_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(lean_object* v___x_190_, lean_object* v_resTy_191_, lean_object* v_c_192_, lean_object* v_dec_193_, lean_object* v_t_194_, lean_object* v_e_195_, lean_object* v_k_196_, lean_object* v_u_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_198_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v_u_197_);
lean_ctor_set(v___x_199_, 1, v___x_190_);
v___x_200_ = l_Lean_mkConst(v___x_198_, v___x_199_);
lean_inc_ref(v_e_195_);
lean_inc_ref(v_t_194_);
lean_inc_ref(v_dec_193_);
lean_inc_ref(v_c_192_);
v___x_201_ = l_Lean_mkApp5(v___x_200_, v_resTy_191_, v_c_192_, v_dec_193_, v_t_194_, v_e_195_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
v___x_203_ = lean_unsigned_to_nat(4u);
v___x_204_ = lean_mk_empty_array_with_capacity(v___x_203_);
v___x_205_ = lean_array_push(v___x_204_, v_c_192_);
v___x_206_ = lean_array_push(v___x_205_, v_dec_193_);
v___x_207_ = lean_array_push(v___x_206_, v_t_194_);
v___x_208_ = lean_array_push(v___x_207_, v_e_195_);
v___x_209_ = lean_apply_2(v_k_196_, v___x_202_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(lean_object* v___x_210_, lean_object* v_resTy_211_, lean_object* v_c_212_, lean_object* v_dec_213_, lean_object* v_t_214_, lean_object* v_k_215_, lean_object* v_inst_216_, lean_object* v_toBind_217_, lean_object* v_e_218_){
_start:
{
lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
lean_inc_ref(v_resTy_211_);
v___f_219_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0), 8, 7);
lean_closure_set(v___f_219_, 0, v___x_210_);
lean_closure_set(v___f_219_, 1, v_resTy_211_);
lean_closure_set(v___f_219_, 2, v_c_212_);
lean_closure_set(v___f_219_, 3, v_dec_213_);
lean_closure_set(v___f_219_, 4, v_t_214_);
lean_closure_set(v___f_219_, 5, v_e_218_);
lean_closure_set(v___f_219_, 6, v_k_215_);
v___x_220_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_220_, 0, v_resTy_211_);
v___x_221_ = lean_apply_2(v_inst_216_, lean_box(0), v___x_220_);
v___x_222_ = lean_apply_4(v_toBind_217_, lean_box(0), lean_box(0), v___x_221_, v___f_219_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(lean_object* v___x_226_, lean_object* v_resTy_227_, lean_object* v_c_228_, lean_object* v_dec_229_, lean_object* v_k_230_, lean_object* v_inst_231_, lean_object* v_toBind_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_t_235_){
_start:
{
lean_object* v___f_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_inc_ref(v_resTy_227_);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1), 9, 8);
lean_closure_set(v___f_236_, 0, v___x_226_);
lean_closure_set(v___f_236_, 1, v_resTy_227_);
lean_closure_set(v___f_236_, 2, v_c_228_);
lean_closure_set(v___f_236_, 3, v_dec_229_);
lean_closure_set(v___f_236_, 4, v_t_235_);
lean_closure_set(v___f_236_, 5, v_k_230_);
lean_closure_set(v___f_236_, 6, v_inst_231_);
lean_closure_set(v___f_236_, 7, v_toBind_232_);
v___x_237_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_238_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_233_, v_inst_234_, v___x_237_, v_resTy_227_, v___f_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(lean_object* v___x_242_, lean_object* v_resTy_243_, lean_object* v_c_244_, lean_object* v_k_245_, lean_object* v_inst_246_, lean_object* v_toBind_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_dec_250_){
_start:
{
lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_inc_ref(v_inst_249_);
lean_inc_ref(v_inst_248_);
lean_inc_ref(v_resTy_243_);
v___f_251_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2), 10, 9);
lean_closure_set(v___f_251_, 0, v___x_242_);
lean_closure_set(v___f_251_, 1, v_resTy_243_);
lean_closure_set(v___f_251_, 2, v_c_244_);
lean_closure_set(v___f_251_, 3, v_dec_250_);
lean_closure_set(v___f_251_, 4, v_k_245_);
lean_closure_set(v___f_251_, 5, v_inst_246_);
lean_closure_set(v___f_251_, 6, v_toBind_247_);
lean_closure_set(v___f_251_, 7, v_inst_248_);
lean_closure_set(v___f_251_, 8, v_inst_249_);
v___x_252_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_253_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_248_, v_inst_249_, v___x_252_, v_resTy_243_, v___f_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_box(0);
v___x_261_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3));
v___x_262_ = l_Lean_mkConst(v___x_261_, v___x_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(lean_object* v_resTy_263_, lean_object* v_k_264_, lean_object* v_inst_265_, lean_object* v_toBind_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_c_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_270_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_271_ = lean_box(0);
lean_inc_ref(v_inst_268_);
lean_inc_ref(v_inst_267_);
lean_inc_ref(v_c_269_);
v___f_272_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3), 9, 8);
lean_closure_set(v___f_272_, 0, v___x_271_);
lean_closure_set(v___f_272_, 1, v_resTy_263_);
lean_closure_set(v___f_272_, 2, v_c_269_);
lean_closure_set(v___f_272_, 3, v_k_264_);
lean_closure_set(v___f_272_, 4, v_inst_265_);
lean_closure_set(v___f_272_, 5, v_toBind_266_);
lean_closure_set(v___f_272_, 6, v_inst_267_);
lean_closure_set(v___f_272_, 7, v_inst_268_);
v___x_273_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_274_ = l_Lean_Expr_app___override(v___x_273_, v_c_269_);
v___x_275_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_267_, v_inst_268_, v___x_270_, v___x_274_, v___f_272_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(lean_object* v_c_276_, lean_object* v_resTy_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_mkArrow(v_c_276_, v_resTy_277_, v___y_280_, v___y_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(lean_object* v_c_284_, lean_object* v_resTy_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(v_c_284_, v_resTy_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(lean_object* v___x_295_, lean_object* v_resTy_296_, lean_object* v_c_297_, lean_object* v_dec_298_, lean_object* v_t_299_, lean_object* v_e_300_, lean_object* v_k_301_, lean_object* v_u_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v_u_302_);
lean_ctor_set(v___x_304_, 1, v___x_295_);
v___x_305_ = l_Lean_mkConst(v___x_303_, v___x_304_);
lean_inc_ref(v_e_300_);
lean_inc_ref(v_t_299_);
lean_inc_ref(v_dec_298_);
lean_inc_ref(v_c_297_);
v___x_306_ = l_Lean_mkApp5(v___x_305_, v_resTy_296_, v_c_297_, v_dec_298_, v_t_299_, v_e_300_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_mk_empty_array_with_capacity(v___x_308_);
v___x_310_ = lean_array_push(v___x_309_, v_c_297_);
v___x_311_ = lean_array_push(v___x_310_, v_dec_298_);
v___x_312_ = lean_array_push(v___x_311_, v_t_299_);
v___x_313_ = lean_array_push(v___x_312_, v_e_300_);
v___x_314_ = lean_apply_2(v_k_301_, v___x_307_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(lean_object* v___x_315_, lean_object* v_resTy_316_, lean_object* v_c_317_, lean_object* v_dec_318_, lean_object* v_t_319_, lean_object* v_k_320_, lean_object* v_inst_321_, lean_object* v_toBind_322_, lean_object* v_e_323_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_inc_ref(v_resTy_316_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6), 8, 7);
lean_closure_set(v___f_324_, 0, v___x_315_);
lean_closure_set(v___f_324_, 1, v_resTy_316_);
lean_closure_set(v___f_324_, 2, v_c_317_);
lean_closure_set(v___f_324_, 3, v_dec_318_);
lean_closure_set(v___f_324_, 4, v_t_319_);
lean_closure_set(v___f_324_, 5, v_e_323_);
lean_closure_set(v___f_324_, 6, v_k_320_);
v___x_325_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_325_, 0, v_resTy_316_);
v___x_326_ = lean_apply_2(v_inst_321_, lean_box(0), v___x_325_);
v___x_327_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_326_, v___f_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(lean_object* v___x_328_, lean_object* v_resTy_329_, lean_object* v_c_330_, lean_object* v_dec_331_, lean_object* v_k_332_, lean_object* v_inst_333_, lean_object* v_toBind_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_eTy_337_, lean_object* v_t_338_){
_start:
{
lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___f_339_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7), 9, 8);
lean_closure_set(v___f_339_, 0, v___x_328_);
lean_closure_set(v___f_339_, 1, v_resTy_329_);
lean_closure_set(v___f_339_, 2, v_c_330_);
lean_closure_set(v___f_339_, 3, v_dec_331_);
lean_closure_set(v___f_339_, 4, v_t_338_);
lean_closure_set(v___f_339_, 5, v_k_332_);
lean_closure_set(v___f_339_, 6, v_inst_333_);
lean_closure_set(v___f_339_, 7, v_toBind_334_);
v___x_340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_341_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_335_, v_inst_336_, v___x_340_, v_eTy_337_, v___f_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(lean_object* v___x_342_, lean_object* v_resTy_343_, lean_object* v_c_344_, lean_object* v_dec_345_, lean_object* v_k_346_, lean_object* v_inst_347_, lean_object* v_toBind_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_tTy_351_, lean_object* v_eTy_352_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_inc_ref(v_inst_350_);
lean_inc_ref(v_inst_349_);
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8), 11, 10);
lean_closure_set(v___f_353_, 0, v___x_342_);
lean_closure_set(v___f_353_, 1, v_resTy_343_);
lean_closure_set(v___f_353_, 2, v_c_344_);
lean_closure_set(v___f_353_, 3, v_dec_345_);
lean_closure_set(v___f_353_, 4, v_k_346_);
lean_closure_set(v___f_353_, 5, v_inst_347_);
lean_closure_set(v___f_353_, 6, v_toBind_348_);
lean_closure_set(v___f_353_, 7, v_inst_349_);
lean_closure_set(v___f_353_, 8, v_inst_350_);
lean_closure_set(v___f_353_, 9, v_eTy_352_);
v___x_354_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_355_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_349_, v_inst_350_, v___x_354_, v_tTy_351_, v___f_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object* v___x_356_, lean_object* v_resTy_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_mkArrow(v___x_356_, v_resTy_357_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object* v___x_364_, lean_object* v_resTy_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(v___x_364_, v_resTy_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object* v___x_372_, lean_object* v_resTy_373_, lean_object* v_c_374_, lean_object* v_dec_375_, lean_object* v_k_376_, lean_object* v_inst_377_, lean_object* v_toBind_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_tTy_381_){
_start:
{
lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_inc(v_toBind_378_);
lean_inc(v_inst_377_);
lean_inc_ref(v_c_374_);
lean_inc_ref(v_resTy_373_);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9), 11, 10);
lean_closure_set(v___f_382_, 0, v___x_372_);
lean_closure_set(v___f_382_, 1, v_resTy_373_);
lean_closure_set(v___f_382_, 2, v_c_374_);
lean_closure_set(v___f_382_, 3, v_dec_375_);
lean_closure_set(v___f_382_, 4, v_k_376_);
lean_closure_set(v___f_382_, 5, v_inst_377_);
lean_closure_set(v___f_382_, 6, v_toBind_378_);
lean_closure_set(v___f_382_, 7, v_inst_379_);
lean_closure_set(v___f_382_, 8, v_inst_380_);
lean_closure_set(v___f_382_, 9, v_tTy_381_);
v___x_383_ = l_Lean_mkNot(v_c_374_);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed), 7, 2);
lean_closure_set(v___f_384_, 0, v___x_383_);
lean_closure_set(v___f_384_, 1, v_resTy_373_);
v___x_385_ = lean_apply_2(v_inst_377_, lean_box(0), v___f_384_);
v___x_386_ = lean_apply_4(v_toBind_378_, lean_box(0), lean_box(0), v___x_385_, v___f_382_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object* v___x_387_, lean_object* v_resTy_388_, lean_object* v_c_389_, lean_object* v_k_390_, lean_object* v_inst_391_, lean_object* v_toBind_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v___f_395_, lean_object* v_dec_396_){
_start:
{
lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_inc(v_toBind_392_);
lean_inc(v_inst_391_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11), 10, 9);
lean_closure_set(v___f_397_, 0, v___x_387_);
lean_closure_set(v___f_397_, 1, v_resTy_388_);
lean_closure_set(v___f_397_, 2, v_c_389_);
lean_closure_set(v___f_397_, 3, v_dec_396_);
lean_closure_set(v___f_397_, 4, v_k_390_);
lean_closure_set(v___f_397_, 5, v_inst_391_);
lean_closure_set(v___f_397_, 6, v_toBind_392_);
lean_closure_set(v___f_397_, 7, v_inst_393_);
lean_closure_set(v___f_397_, 8, v_inst_394_);
v___x_398_ = lean_apply_2(v_inst_391_, lean_box(0), v___f_395_);
v___x_399_ = lean_apply_4(v_toBind_392_, lean_box(0), lean_box(0), v___x_398_, v___f_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object* v_resTy_400_, lean_object* v_k_401_, lean_object* v_inst_402_, lean_object* v_toBind_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_c_406_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_inc_ref(v_resTy_400_);
lean_inc_ref_n(v_c_406_, 2);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed), 7, 2);
lean_closure_set(v___f_407_, 0, v_c_406_);
lean_closure_set(v___f_407_, 1, v_resTy_400_);
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_409_ = lean_box(0);
lean_inc_ref(v_inst_405_);
lean_inc_ref(v_inst_404_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12), 10, 9);
lean_closure_set(v___f_410_, 0, v___x_409_);
lean_closure_set(v___f_410_, 1, v_resTy_400_);
lean_closure_set(v___f_410_, 2, v_c_406_);
lean_closure_set(v___f_410_, 3, v_k_401_);
lean_closure_set(v___f_410_, 4, v_inst_402_);
lean_closure_set(v___f_410_, 5, v_toBind_403_);
lean_closure_set(v___f_410_, 6, v_inst_404_);
lean_closure_set(v___f_410_, 7, v_inst_405_);
lean_closure_set(v___f_410_, 8, v___f_407_);
v___x_411_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_412_ = l_Lean_Expr_app___override(v___x_411_, v_c_406_);
v___x_413_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_404_, v_inst_405_, v___x_408_, v___x_412_, v___f_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object* v_i_417_, lean_object* v_a_418_, lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_i_417_, v___x_421_);
v___x_423_ = lean_name_append_index_after(v___x_420_, v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v_a_418_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed(lean_object* v_i_425_, lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(v_i_425_, v_a_426_, v_x_427_);
lean_dec(v_i_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object* v_resTy_429_, lean_object* v_motiveArgs_430_, lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
uint8_t v___x_437_; uint8_t v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; 
v___x_437_ = 0;
v___x_438_ = 1;
v___x_439_ = 1;
v___x_440_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_430_, v_resTy_429_, v___x_437_, v___x_438_, v___x_437_, v___x_438_, v___x_439_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed(lean_object* v_resTy_441_, lean_object* v_motiveArgs_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(v_resTy_441_, v_motiveArgs_442_, v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec_ref(v_x_443_);
lean_dec_ref(v_motiveArgs_442_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object* v_i_450_, lean_object* v___x_451_, lean_object* v_discrs_452_, lean_object* v_prior_453_, lean_object* v_next_454_, lean_object* v_acc_455_, lean_object* v_h_456_, lean_object* v_G_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_a_464_; uint8_t v___x_468_; 
v___x_468_ = lean_nat_dec_lt(v_next_454_, v_i_450_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_dec_ref(v_G_457_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_acc_455_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_array_get_borrowed(v___x_451_, v_discrs_452_, v_next_454_);
v___x_471_ = l_Lean_Expr_isFVar(v___x_470_);
if (v___x_471_ == 0)
{
v_a_464_ = v_acc_455_;
goto v___jp_463_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_array_get_borrowed(v___x_451_, v_prior_453_, v_next_454_);
lean_inc(v___x_470_);
v___x_473_ = l_Lean_Expr_replaceFVar(v_acc_455_, v___x_470_, v___x_472_);
lean_dec_ref(v_acc_455_);
v_a_464_ = v___x_473_;
goto v___jp_463_;
}
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v_next_454_, v___x_465_);
lean_inc(v___y_461_);
lean_inc_ref(v___y_460_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
v___x_467_ = lean_apply_9(v_G_457_, v___x_466_, v_a_464_, lean_box(0), lean_box(0), v___y_458_, v___y_459_, v___y_460_, v___y_461_, lean_box(0));
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed(lean_object* v_i_474_, lean_object* v___x_475_, lean_object* v_discrs_476_, lean_object* v_prior_477_, lean_object* v_next_478_, lean_object* v_acc_479_, lean_object* v_h_480_, lean_object* v_G_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(v_i_474_, v___x_475_, v_discrs_476_, v_prior_477_, v_next_478_, v_acc_479_, v_h_480_, v_G_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v_next_478_);
lean_dec_ref(v_prior_477_);
lean_dec_ref(v_discrs_476_);
lean_dec_ref(v___x_475_);
lean_dec(v_i_474_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object* v_a_488_, lean_object* v___f_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
v___x_495_ = lean_infer_type(v_a_488_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v___x_2366__overap_498_; lean_object* v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_2366__overap_498_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_489_, v___x_497_, v_a_496_, lean_box(0));
v___x_499_ = lean_apply_5(v___x_2366__overap_498_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, lean_box(0));
return v___x_499_;
}
else
{
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec_ref(v___f_489_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17___boxed(lean_object* v_a_500_, lean_object* v___f_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(v_a_500_, v___f_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object* v_i_508_, lean_object* v___x_509_, lean_object* v_discrs_510_, lean_object* v_a_511_, lean_object* v_inst_512_, lean_object* v_prior_513_){
_start:
{
lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed), 13, 4);
lean_closure_set(v___f_514_, 0, v_i_508_);
lean_closure_set(v___f_514_, 1, v___x_509_);
lean_closure_set(v___f_514_, 2, v_discrs_510_);
lean_closure_set(v___f_514_, 3, v_prior_513_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17___boxed), 7, 2);
lean_closure_set(v___f_515_, 0, v_a_511_);
lean_closure_set(v___f_515_, 1, v___f_514_);
v___x_516_ = lean_apply_2(v_inst_512_, lean_box(0), v___f_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object* v___x_520_, lean_object* v_discrs_521_, lean_object* v_inst_522_, lean_object* v_i_523_, lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
lean_inc(v_i_523_);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18), 6, 5);
lean_closure_set(v___f_526_, 0, v_i_523_);
lean_closure_set(v___f_526_, 1, v___x_520_);
lean_closure_set(v___f_526_, 2, v_discrs_521_);
lean_closure_set(v___f_526_, 3, v_a_524_);
lean_closure_set(v___f_526_, 4, v_inst_522_);
v___x_527_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1));
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v_i_523_, v___x_528_);
lean_dec(v_i_523_);
v___x_530_ = lean_name_append_index_after(v___x_527_, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___f_526_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object* v_toMatcherInfo_534_, lean_object* v_matcherName_535_, lean_object* v_matcherLevels_536_, lean_object* v_params_537_, lean_object* v_motive_538_, lean_object* v_discrs_539_, lean_object* v_alts_540_, lean_object* v_k_541_, lean_object* v_____do__lift_542_){
_start:
{
lean_object* v___x_543_; lean_object* v_abstractMatcherApp_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_543_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
lean_inc_ref(v_discrs_539_);
v_abstractMatcherApp_544_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_abstractMatcherApp_544_, 0, v_toMatcherInfo_534_);
lean_ctor_set(v_abstractMatcherApp_544_, 1, v_matcherName_535_);
lean_ctor_set(v_abstractMatcherApp_544_, 2, v_matcherLevels_536_);
lean_ctor_set(v_abstractMatcherApp_544_, 3, v_params_537_);
lean_ctor_set(v_abstractMatcherApp_544_, 4, v_motive_538_);
lean_ctor_set(v_abstractMatcherApp_544_, 5, v_discrs_539_);
lean_ctor_set(v_abstractMatcherApp_544_, 6, v_____do__lift_542_);
lean_ctor_set(v_abstractMatcherApp_544_, 7, v___x_543_);
v___x_545_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_545_, 0, v_abstractMatcherApp_544_);
v___x_546_ = l_Array_append___redArg(v_discrs_539_, v_alts_540_);
v___x_547_ = lean_apply_2(v_k_541_, v___x_545_, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object* v_toMatcherInfo_548_, lean_object* v_matcherName_549_, lean_object* v_matcherLevels_550_, lean_object* v_params_551_, lean_object* v_motive_552_, lean_object* v_discrs_553_, lean_object* v_alts_554_, lean_object* v_k_555_, lean_object* v_____do__lift_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(v_toMatcherInfo_548_, v_matcherName_549_, v_matcherLevels_550_, v_params_551_, v_motive_552_, v_discrs_553_, v_alts_554_, v_k_555_, v_____do__lift_556_);
lean_dec_ref(v_alts_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object* v_toMatcherInfo_559_, lean_object* v_matcherName_560_, lean_object* v_matcherLevels_561_, lean_object* v_params_562_, lean_object* v_motive_563_, lean_object* v_discrs_564_, lean_object* v_k_565_, lean_object* v___x_566_, lean_object* v_inst_567_, lean_object* v_toBind_568_, lean_object* v_alts_569_){
_start:
{
lean_object* v___f_570_; lean_object* v___x_571_; size_t v_sz_572_; size_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_inc_ref(v_alts_569_);
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_570_, 0, v_toMatcherInfo_559_);
lean_closure_set(v___f_570_, 1, v_matcherName_560_);
lean_closure_set(v___f_570_, 2, v_matcherLevels_561_);
lean_closure_set(v___f_570_, 3, v_params_562_);
lean_closure_set(v___f_570_, 4, v_motive_563_);
lean_closure_set(v___f_570_, 5, v_discrs_564_);
lean_closure_set(v___f_570_, 6, v_alts_569_);
lean_closure_set(v___f_570_, 7, v_k_565_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___closed__0));
v_sz_572_ = lean_array_size(v_alts_569_);
v___x_573_ = ((size_t)0ULL);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_566_, v___x_571_, v_sz_572_, v___x_573_, v_alts_569_);
v___x_575_ = lean_apply_2(v_inst_567_, lean_box(0), v___x_574_);
v___x_576_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v___x_575_, v___f_570_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object* v___f_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v___f_599_, lean_object* v_origAltTypes_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_altNamesTypes_605_; uint8_t v___x_606_; lean_object* v___x_607_; 
v___x_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v___x_602_ = lean_array_get_size(v_origAltTypes_600_);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_mk_empty_array_with_capacity(v___x_602_);
v_altNamesTypes_605_ = l_Array_mapFinIdxM_map___redArg(v___x_601_, v_origAltTypes_600_, v___f_596_, v___x_602_, v___x_603_, v___x_604_);
v___x_606_ = 0;
v___x_607_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_597_, v_inst_598_, v_altNamesTypes_605_, v___f_599_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object* v_toMatcherInfo_608_, lean_object* v_matcherName_609_, lean_object* v_params_610_, lean_object* v_motive_611_, lean_object* v_discrs_612_, lean_object* v_k_613_, lean_object* v___x_614_, lean_object* v_inst_615_, lean_object* v_toBind_616_, lean_object* v___f_617_, lean_object* v_inst_618_, lean_object* v_inst_619_, lean_object* v_alts_620_, lean_object* v_matcherLevels_621_){
_start:
{
lean_object* v___f_622_; lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_matcherPartial_626_; lean_object* v_matcherPartial_627_; lean_object* v_matcherPartial_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_inc(v_toBind_616_);
lean_inc(v_inst_615_);
lean_inc_ref(v_discrs_612_);
lean_inc_ref(v_motive_611_);
lean_inc_ref(v_params_610_);
lean_inc_ref(v_matcherLevels_621_);
lean_inc(v_matcherName_609_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21), 11, 10);
lean_closure_set(v___f_622_, 0, v_toMatcherInfo_608_);
lean_closure_set(v___f_622_, 1, v_matcherName_609_);
lean_closure_set(v___f_622_, 2, v_matcherLevels_621_);
lean_closure_set(v___f_622_, 3, v_params_610_);
lean_closure_set(v___f_622_, 4, v_motive_611_);
lean_closure_set(v___f_622_, 5, v_discrs_612_);
lean_closure_set(v___f_622_, 6, v_k_613_);
lean_closure_set(v___f_622_, 7, v___x_614_);
lean_closure_set(v___f_622_, 8, v_inst_615_);
lean_closure_set(v___f_622_, 9, v_toBind_616_);
v___f_623_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 5, 4);
lean_closure_set(v___f_623_, 0, v___f_617_);
lean_closure_set(v___f_623_, 1, v_inst_618_);
lean_closure_set(v___f_623_, 2, v_inst_619_);
lean_closure_set(v___f_623_, 3, v___f_622_);
v___x_624_ = lean_array_to_list(v_matcherLevels_621_);
v___x_625_ = l_Lean_mkConst(v_matcherName_609_, v___x_624_);
v_matcherPartial_626_ = l_Lean_mkAppN(v___x_625_, v_params_610_);
lean_dec_ref(v_params_610_);
v_matcherPartial_627_ = l_Lean_Expr_app___override(v_matcherPartial_626_, v_motive_611_);
v_matcherPartial_628_ = l_Lean_mkAppN(v_matcherPartial_627_, v_discrs_612_);
lean_dec_ref(v_discrs_612_);
v___x_629_ = lean_array_get_size(v_alts_620_);
v___x_630_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_630_, 0, v___x_629_);
lean_closure_set(v___x_630_, 1, v_matcherPartial_628_);
v___x_631_ = lean_apply_2(v_inst_615_, lean_box(0), v___x_630_);
v___x_632_ = lean_apply_4(v_toBind_616_, lean_box(0), lean_box(0), v___x_631_, v___f_623_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___boxed(lean_object* v_toMatcherInfo_633_, lean_object* v_matcherName_634_, lean_object* v_params_635_, lean_object* v_motive_636_, lean_object* v_discrs_637_, lean_object* v_k_638_, lean_object* v___x_639_, lean_object* v_inst_640_, lean_object* v_toBind_641_, lean_object* v___f_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_alts_645_, lean_object* v_matcherLevels_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(v_toMatcherInfo_633_, v_matcherName_634_, v_params_635_, v_motive_636_, v_discrs_637_, v_k_638_, v___x_639_, v_inst_640_, v_toBind_641_, v___f_642_, v_inst_643_, v_inst_644_, v_alts_645_, v_matcherLevels_646_);
lean_dec_ref(v_alts_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object* v___f_648_, lean_object* v_matcherLevels_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_apply_1(v___f_648_, v_matcherLevels_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object* v_matcherLevels_651_, lean_object* v_val_652_, lean_object* v_toPure_653_, lean_object* v_toBind_654_, lean_object* v___f_655_, lean_object* v_uElim_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_array_set(v_matcherLevels_651_, v_val_652_, v_uElim_656_);
v___x_658_ = lean_apply_2(v_toPure_653_, lean_box(0), v___x_657_);
v___x_659_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v___x_658_, v___f_655_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___boxed(lean_object* v_matcherLevels_660_, lean_object* v_val_661_, lean_object* v_toPure_662_, lean_object* v_toBind_663_, lean_object* v___f_664_, lean_object* v_uElim_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(v_matcherLevels_660_, v_val_661_, v_toPure_662_, v_toBind_663_, v___f_664_, v_uElim_665_);
lean_dec(v_val_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object* v_toMatcherInfo_667_, lean_object* v_matcherName_668_, lean_object* v_params_669_, lean_object* v_discrs_670_, lean_object* v_k_671_, lean_object* v___x_672_, lean_object* v_inst_673_, lean_object* v_toBind_674_, lean_object* v___f_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_alts_678_, lean_object* v_toPure_679_, lean_object* v_matcherLevels_680_, lean_object* v_resTy_681_, lean_object* v_motive_682_){
_start:
{
lean_object* v_uElimPos_x3f_683_; lean_object* v___f_684_; 
v_uElimPos_x3f_683_ = lean_ctor_get(v_toMatcherInfo_667_, 3);
lean_inc(v_uElimPos_x3f_683_);
lean_inc(v_toBind_674_);
lean_inc(v_inst_673_);
v___f_684_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___boxed), 14, 13);
lean_closure_set(v___f_684_, 0, v_toMatcherInfo_667_);
lean_closure_set(v___f_684_, 1, v_matcherName_668_);
lean_closure_set(v___f_684_, 2, v_params_669_);
lean_closure_set(v___f_684_, 3, v_motive_682_);
lean_closure_set(v___f_684_, 4, v_discrs_670_);
lean_closure_set(v___f_684_, 5, v_k_671_);
lean_closure_set(v___f_684_, 6, v___x_672_);
lean_closure_set(v___f_684_, 7, v_inst_673_);
lean_closure_set(v___f_684_, 8, v_toBind_674_);
lean_closure_set(v___f_684_, 9, v___f_675_);
lean_closure_set(v___f_684_, 10, v_inst_676_);
lean_closure_set(v___f_684_, 11, v_inst_677_);
lean_closure_set(v___f_684_, 12, v_alts_678_);
if (lean_obj_tag(v_uElimPos_x3f_683_) == 0)
{
lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec_ref(v_resTy_681_);
lean_dec(v_inst_673_);
v___f_685_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24), 2, 1);
lean_closure_set(v___f_685_, 0, v___f_684_);
v___x_686_ = lean_apply_2(v_toPure_679_, lean_box(0), v_matcherLevels_680_);
v___x_687_ = lean_apply_4(v_toBind_674_, lean_box(0), lean_box(0), v___x_686_, v___f_685_);
return v___x_687_;
}
else
{
lean_object* v_val_688_; lean_object* v___f_689_; lean_object* v___f_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_val_688_ = lean_ctor_get(v_uElimPos_x3f_683_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_uElimPos_x3f_683_, 1);
v___f_689_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24), 2, 1);
lean_closure_set(v___f_689_, 0, v___f_684_);
lean_inc(v_toBind_674_);
v___f_690_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___boxed), 6, 5);
lean_closure_set(v___f_690_, 0, v_matcherLevels_680_);
lean_closure_set(v___f_690_, 1, v_val_688_);
lean_closure_set(v___f_690_, 2, v_toPure_679_);
lean_closure_set(v___f_690_, 3, v_toBind_674_);
lean_closure_set(v___f_690_, 4, v___f_689_);
v___x_691_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_691_, 0, v_resTy_681_);
v___x_692_ = lean_apply_2(v_inst_673_, lean_box(0), v___x_691_);
v___x_693_ = lean_apply_4(v_toBind_674_, lean_box(0), lean_box(0), v___x_692_, v___f_690_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object* v_toMatcherInfo_694_, lean_object* v_matcherName_695_, lean_object* v_params_696_, lean_object* v_k_697_, lean_object* v___x_698_, lean_object* v_inst_699_, lean_object* v_toBind_700_, lean_object* v___f_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_alts_704_, lean_object* v_toPure_705_, lean_object* v_matcherLevels_706_, lean_object* v_resTy_707_, lean_object* v___x_708_, lean_object* v_motive_709_, lean_object* v___f_710_, lean_object* v_discrs_711_){
_start:
{
lean_object* v___f_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc(v_toBind_700_);
lean_inc(v_inst_699_);
lean_inc_ref(v___x_698_);
v___f_712_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25), 16, 15);
lean_closure_set(v___f_712_, 0, v_toMatcherInfo_694_);
lean_closure_set(v___f_712_, 1, v_matcherName_695_);
lean_closure_set(v___f_712_, 2, v_params_696_);
lean_closure_set(v___f_712_, 3, v_discrs_711_);
lean_closure_set(v___f_712_, 4, v_k_697_);
lean_closure_set(v___f_712_, 5, v___x_698_);
lean_closure_set(v___f_712_, 6, v_inst_699_);
lean_closure_set(v___f_712_, 7, v_toBind_700_);
lean_closure_set(v___f_712_, 8, v___f_701_);
lean_closure_set(v___f_712_, 9, v_inst_702_);
lean_closure_set(v___f_712_, 10, v_inst_703_);
lean_closure_set(v___f_712_, 11, v_alts_704_);
lean_closure_set(v___f_712_, 12, v_toPure_705_);
lean_closure_set(v___f_712_, 13, v_matcherLevels_706_);
lean_closure_set(v___f_712_, 14, v_resTy_707_);
v___x_713_ = 0;
v___x_714_ = l_Lean_Meta_lambdaTelescope___redArg(v___x_708_, v___x_698_, v_motive_709_, v___f_710_, v___x_713_);
v___x_715_ = lean_apply_2(v_inst_699_, lean_box(0), v___x_714_);
v___x_716_ = lean_apply_4(v_toBind_700_, lean_box(0), lean_box(0), v___x_715_, v___f_712_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_717_ = _args[0];
lean_object* v_matcherName_718_ = _args[1];
lean_object* v_params_719_ = _args[2];
lean_object* v_k_720_ = _args[3];
lean_object* v___x_721_ = _args[4];
lean_object* v_inst_722_ = _args[5];
lean_object* v_toBind_723_ = _args[6];
lean_object* v___f_724_ = _args[7];
lean_object* v_inst_725_ = _args[8];
lean_object* v_inst_726_ = _args[9];
lean_object* v_alts_727_ = _args[10];
lean_object* v_toPure_728_ = _args[11];
lean_object* v_matcherLevels_729_ = _args[12];
lean_object* v_resTy_730_ = _args[13];
lean_object* v___x_731_ = _args[14];
lean_object* v_motive_732_ = _args[15];
lean_object* v___f_733_ = _args[16];
lean_object* v_discrs_734_ = _args[17];
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(v_toMatcherInfo_717_, v_matcherName_718_, v_params_719_, v_k_720_, v___x_721_, v_inst_722_, v_toBind_723_, v___f_724_, v_inst_725_, v_inst_726_, v_alts_727_, v_toPure_728_, v_matcherLevels_729_, v_resTy_730_, v___x_731_, v_motive_732_, v___f_733_, v_discrs_734_);
return v_res_735_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0(void){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_instMonadEIO(lean_box(0));
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_738_ = l_StateRefT_x27_instMonad___redArg(v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = l_Lean_Level_ofNat(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8);
v___x_749_ = l_Lean_mkSort(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_info_754_, lean_object* v_resTy_755_, lean_object* v_k_756_){
_start:
{
lean_object* v___x_757_; lean_object* v_toApplicative_758_; lean_object* v_toFunctor_759_; lean_object* v_toSeq_760_; lean_object* v_toSeqLeft_761_; lean_object* v_toSeqRight_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_toApplicative_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_850_; 
v___x_757_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_758_ = lean_ctor_get(v___x_757_, 0);
v_toFunctor_759_ = lean_ctor_get(v_toApplicative_758_, 0);
v_toSeq_760_ = lean_ctor_get(v_toApplicative_758_, 2);
v_toSeqLeft_761_ = lean_ctor_get(v_toApplicative_758_, 3);
v_toSeqRight_762_ = lean_ctor_get(v_toApplicative_758_, 4);
v___f_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_764_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_759_, 2);
v___f_765_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_765_, 0, v_toFunctor_759_);
v___f_766_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_766_, 0, v_toFunctor_759_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___f_765_);
lean_ctor_set(v___x_767_, 1, v___f_766_);
lean_inc(v_toSeqRight_762_);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_768_, 0, v_toSeqRight_762_);
lean_inc(v_toSeqLeft_761_);
v___f_769_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_769_, 0, v_toSeqLeft_761_);
lean_inc(v_toSeq_760_);
v___f_770_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_770_, 0, v_toSeq_760_);
v___x_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_771_, 0, v___x_767_);
lean_ctor_set(v___x_771_, 1, v___f_763_);
lean_ctor_set(v___x_771_, 2, v___f_770_);
lean_ctor_set(v___x_771_, 3, v___f_769_);
lean_ctor_set(v___x_771_, 4, v___f_768_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___f_764_);
v___x_773_ = l_StateRefT_x27_instMonad___redArg(v___x_772_);
v_toApplicative_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_773_, 1);
lean_dec(v_unused_851_);
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_850_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_toApplicative_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_850_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_toFunctor_778_; lean_object* v_toSeq_779_; lean_object* v_toSeqLeft_780_; lean_object* v_toSeqRight_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_848_; 
v_toFunctor_778_ = lean_ctor_get(v_toApplicative_774_, 0);
v_toSeq_779_ = lean_ctor_get(v_toApplicative_774_, 2);
v_toSeqLeft_780_ = lean_ctor_get(v_toApplicative_774_, 3);
v_toSeqRight_781_ = lean_ctor_get(v_toApplicative_774_, 4);
v_isSharedCheck_848_ = !lean_is_exclusive(v_toApplicative_774_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_toApplicative_774_, 1);
lean_dec(v_unused_849_);
v___x_783_ = v_toApplicative_774_;
v_isShared_784_ = v_isSharedCheck_848_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_toSeqRight_781_);
lean_inc(v_toSeqLeft_780_);
lean_inc(v_toSeq_779_);
lean_inc(v_toFunctor_778_);
lean_dec(v_toApplicative_774_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_848_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_794_; 
v___f_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_786_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_778_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_787_, 0, v_toFunctor_778_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_788_, 0, v_toFunctor_778_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___f_787_);
lean_ctor_set(v___x_789_, 1, v___f_788_);
v___f_790_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_790_, 0, v_toSeqRight_781_);
v___f_791_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_791_, 0, v_toSeqLeft_780_);
v___f_792_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_792_, 0, v_toSeq_779_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 4, v___f_790_);
lean_ctor_set(v___x_783_, 3, v___f_791_);
lean_ctor_set(v___x_783_, 2, v___f_792_);
lean_ctor_set(v___x_783_, 1, v___f_785_);
lean_ctor_set(v___x_783_, 0, v___x_789_);
v___x_794_ = v___x_783_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___f_785_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v___f_792_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v___f_791_);
lean_ctor_set(v_reuseFailAlloc_847_, 4, v___f_790_);
v___x_794_ = v_reuseFailAlloc_847_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___f_786_);
lean_ctor_set(v___x_776_, 0, v___x_794_);
v___x_796_ = v___x_776_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___f_786_);
v___x_796_ = v_reuseFailAlloc_846_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v_toApplicative_797_; lean_object* v_toFunctor_798_; lean_object* v_toSeq_799_; lean_object* v_toSeqLeft_800_; lean_object* v_toSeqRight_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_toApplicative_797_ = lean_ctor_get(v___x_757_, 0);
v_toFunctor_798_ = lean_ctor_get(v_toApplicative_797_, 0);
v_toSeq_799_ = lean_ctor_get(v_toApplicative_797_, 2);
v_toSeqLeft_800_ = lean_ctor_get(v_toApplicative_797_, 3);
v_toSeqRight_801_ = lean_ctor_get(v_toApplicative_797_, 4);
lean_inc_ref_n(v_toFunctor_798_, 2);
v___f_802_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_802_, 0, v_toFunctor_798_);
v___f_803_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_803_, 0, v_toFunctor_798_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___f_802_);
lean_ctor_set(v___x_804_, 1, v___f_803_);
lean_inc(v_toSeqRight_801_);
v___f_805_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_805_, 0, v_toSeqRight_801_);
lean_inc(v_toSeqLeft_800_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_806_, 0, v_toSeqLeft_800_);
lean_inc(v_toSeq_799_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_807_, 0, v_toSeq_799_);
v___x_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_808_, 0, v___x_804_);
lean_ctor_set(v___x_808_, 1, v___f_763_);
lean_ctor_set(v___x_808_, 2, v___f_807_);
lean_ctor_set(v___x_808_, 3, v___f_806_);
lean_ctor_set(v___x_808_, 4, v___f_805_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___f_764_);
v___x_810_ = l_StateRefT_x27_instMonad___redArg(v___x_809_);
v___x_811_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_811_, 0, lean_box(0));
lean_closure_set(v___x_811_, 1, lean_box(0));
lean_closure_set(v___x_811_, 2, v___x_810_);
v___x_812_ = l_instMonadControlTOfPure___redArg(v___x_811_);
switch(lean_obj_tag(v_info_754_))
{
case 0:
{
lean_object* v_toBind_813_; lean_object* v___f_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref_known(v_info_754_, 1);
lean_dec_ref(v___x_812_);
lean_dec_ref(v___x_796_);
v_toBind_813_ = lean_ctor_get(v_inst_753_, 1);
lean_inc_ref(v_inst_753_);
lean_inc_ref(v_inst_752_);
lean_inc(v_toBind_813_);
v___f_814_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_814_, 0, v_resTy_755_);
lean_closure_set(v___f_814_, 1, v_k_756_);
lean_closure_set(v___f_814_, 2, v_inst_751_);
lean_closure_set(v___f_814_, 3, v_toBind_813_);
lean_closure_set(v___f_814_, 4, v_inst_752_);
lean_closure_set(v___f_814_, 5, v_inst_753_);
v___x_815_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_816_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_817_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_752_, v_inst_753_, v___x_815_, v___x_816_, v___f_814_);
return v___x_817_;
}
case 1:
{
lean_object* v_toBind_818_; lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref_known(v_info_754_, 1);
lean_dec_ref(v___x_812_);
lean_dec_ref(v___x_796_);
v_toBind_818_ = lean_ctor_get(v_inst_753_, 1);
lean_inc_ref(v_inst_753_);
lean_inc_ref(v_inst_752_);
lean_inc(v_toBind_818_);
v___f_819_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_819_, 0, v_resTy_755_);
lean_closure_set(v___f_819_, 1, v_k_756_);
lean_closure_set(v___f_819_, 2, v_inst_751_);
lean_closure_set(v___f_819_, 3, v_toBind_818_);
lean_closure_set(v___f_819_, 4, v_inst_752_);
lean_closure_set(v___f_819_, 5, v_inst_753_);
v___x_820_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_821_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_822_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_752_, v_inst_753_, v___x_820_, v___x_821_, v___f_819_);
return v___x_822_;
}
default: 
{
lean_object* v_toApplicative_823_; lean_object* v_matcherApp_824_; lean_object* v_toBind_825_; lean_object* v_toPure_826_; lean_object* v_toMatcherInfo_827_; lean_object* v_matcherName_828_; lean_object* v_matcherLevels_829_; lean_object* v_params_830_; lean_object* v_motive_831_; lean_object* v_discrs_832_; lean_object* v_alts_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___f_837_; lean_object* v___f_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v_discrDecls_843_; uint8_t v___x_844_; lean_object* v___x_845_; 
v_toApplicative_823_ = lean_ctor_get(v_inst_753_, 0);
v_matcherApp_824_ = lean_ctor_get(v_info_754_, 0);
lean_inc_ref(v_matcherApp_824_);
lean_dec_ref_known(v_info_754_, 1);
v_toBind_825_ = lean_ctor_get(v_inst_753_, 1);
v_toPure_826_ = lean_ctor_get(v_toApplicative_823_, 1);
v_toMatcherInfo_827_ = lean_ctor_get(v_matcherApp_824_, 0);
lean_inc_ref(v_toMatcherInfo_827_);
v_matcherName_828_ = lean_ctor_get(v_matcherApp_824_, 1);
lean_inc(v_matcherName_828_);
v_matcherLevels_829_ = lean_ctor_get(v_matcherApp_824_, 2);
lean_inc_ref(v_matcherLevels_829_);
v_params_830_ = lean_ctor_get(v_matcherApp_824_, 3);
lean_inc_ref(v_params_830_);
v_motive_831_ = lean_ctor_get(v_matcherApp_824_, 4);
lean_inc_ref(v_motive_831_);
v_discrs_832_ = lean_ctor_get(v_matcherApp_824_, 5);
lean_inc_ref_n(v_discrs_832_, 2);
v_alts_833_ = lean_ctor_get(v_matcherApp_824_, 6);
lean_inc_ref(v_alts_833_);
lean_dec_ref(v_matcherApp_824_);
v___f_834_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
lean_inc_ref(v_resTy_755_);
v___f_835_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed), 8, 1);
lean_closure_set(v___f_835_, 0, v_resTy_755_);
v___x_836_ = l_Lean_instInhabitedExpr;
lean_inc(v_inst_751_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19), 6, 3);
lean_closure_set(v___f_837_, 0, v___x_836_);
lean_closure_set(v___f_837_, 1, v_discrs_832_);
lean_closure_set(v___f_837_, 2, v_inst_751_);
lean_inc(v_toPure_826_);
lean_inc_ref(v_inst_753_);
lean_inc_ref(v_inst_752_);
lean_inc(v_toBind_825_);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed), 18, 17);
lean_closure_set(v___f_838_, 0, v_toMatcherInfo_827_);
lean_closure_set(v___f_838_, 1, v_matcherName_828_);
lean_closure_set(v___f_838_, 2, v_params_830_);
lean_closure_set(v___f_838_, 3, v_k_756_);
lean_closure_set(v___f_838_, 4, v___x_796_);
lean_closure_set(v___f_838_, 5, v_inst_751_);
lean_closure_set(v___f_838_, 6, v_toBind_825_);
lean_closure_set(v___f_838_, 7, v___f_834_);
lean_closure_set(v___f_838_, 8, v_inst_752_);
lean_closure_set(v___f_838_, 9, v_inst_753_);
lean_closure_set(v___f_838_, 10, v_alts_833_);
lean_closure_set(v___f_838_, 11, v_toPure_826_);
lean_closure_set(v___f_838_, 12, v_matcherLevels_829_);
lean_closure_set(v___f_838_, 13, v_resTy_755_);
lean_closure_set(v___f_838_, 14, v___x_812_);
lean_closure_set(v___f_838_, 15, v_motive_831_);
lean_closure_set(v___f_838_, 16, v___f_835_);
v___x_839_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v___x_840_ = lean_array_get_size(v_discrs_832_);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = lean_mk_empty_array_with_capacity(v___x_840_);
v_discrDecls_843_ = l_Array_mapFinIdxM_map___redArg(v___x_839_, v_discrs_832_, v___f_837_, v___x_840_, v___x_841_, v___x_842_);
v___x_844_ = 0;
v___x_845_ = l_Lean_Meta_withLocalDeclsD___redArg(v_inst_752_, v_inst_753_, v_discrDecls_843_, v___f_838_, v___x_844_);
return v___x_845_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_852_, lean_object* v_00_u03b1_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_info_858_, lean_object* v_resTy_859_, lean_object* v_k_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_854_, v_inst_855_, v_inst_856_, v_info_858_, v_resTy_859_, v_k_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_862_, lean_object* v_00_u03b1_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_info_868_, lean_object* v_resTy_869_, lean_object* v_k_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_862_, v_00_u03b1_863_, v_inst_864_, v_inst_865_, v_inst_866_, v_inst_867_, v_info_868_, v_resTy_869_, v_k_870_);
lean_dec(v_inst_867_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_872_, lean_object* v_resTy_873_, lean_object* v_c_874_, lean_object* v_h_875_, lean_object* v_t_876_, lean_object* v_toPure_877_, lean_object* v_e_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_879_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_880_ = lean_box(0);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v_u_872_);
lean_ctor_set(v___x_881_, 1, v___x_880_);
v___x_882_ = l_Lean_mkConst(v___x_879_, v___x_881_);
v___x_883_ = l_Lean_mkApp5(v___x_882_, v_resTy_873_, v_c_874_, v_h_875_, v_t_876_, v_e_878_);
v___x_884_ = lean_apply_2(v_toPure_877_, lean_box(0), v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_888_, lean_object* v_resTy_889_, lean_object* v_c_890_, lean_object* v_h_891_, lean_object* v_toPure_892_, lean_object* v_onAlt_893_, lean_object* v___x_894_, lean_object* v___x_895_, lean_object* v_toBind_896_, lean_object* v_t_897_){
_start:
{
lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_inc_ref(v_resTy_889_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_898_, 0, v_u_888_);
lean_closure_set(v___f_898_, 1, v_resTy_889_);
lean_closure_set(v___f_898_, 2, v_c_890_);
lean_closure_set(v___f_898_, 3, v_h_891_);
lean_closure_set(v___f_898_, 4, v_t_897_);
lean_closure_set(v___f_898_, 5, v_toPure_892_);
v___x_899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_900_ = lean_apply_4(v_onAlt_893_, v___x_899_, v_resTy_889_, v___x_894_, v___x_895_);
v___x_901_ = lean_apply_4(v_toBind_896_, lean_box(0), lean_box(0), v___x_900_, v___f_898_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_902_, uint8_t v_useSplitter_903_, lean_object* v_inst_904_, lean_object* v_____do__lift_905_){
_start:
{
uint8_t v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_906_ = 0;
v___x_907_ = 1;
v___x_908_ = lean_box(v___x_906_);
v___x_909_ = lean_box(v_useSplitter_903_);
v___x_910_ = lean_box(v___x_906_);
v___x_911_ = lean_box(v_useSplitter_903_);
v___x_912_ = lean_box(v___x_907_);
v___x_913_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_913_, 0, v___x_902_);
lean_closure_set(v___x_913_, 1, v_____do__lift_905_);
lean_closure_set(v___x_913_, 2, v___x_908_);
lean_closure_set(v___x_913_, 3, v___x_909_);
lean_closure_set(v___x_913_, 4, v___x_910_);
lean_closure_set(v___x_913_, 5, v___x_911_);
lean_closure_set(v___x_913_, 6, v___x_912_);
v___x_914_ = lean_apply_2(v_inst_904_, lean_box(0), v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_915_, lean_object* v_useSplitter_916_, lean_object* v_inst_917_, lean_object* v_____do__lift_918_){
_start:
{
uint8_t v_useSplitter_boxed_919_; lean_object* v_res_920_; 
v_useSplitter_boxed_919_ = lean_unbox(v_useSplitter_916_);
v_res_920_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_915_, v_useSplitter_boxed_919_, v_inst_917_, v_____do__lift_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_924_, uint8_t v_useSplitter_925_, lean_object* v_inst_926_, lean_object* v_onAlt_927_, lean_object* v_resTy_928_, lean_object* v_toBind_929_, lean_object* v_h_930_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___f_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_931_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_924_);
v___x_935_ = lean_array_push(v___x_934_, v_h_930_);
v___x_936_ = lean_box(v_useSplitter_925_);
lean_inc_ref(v___x_935_);
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_937_, 0, v___x_935_);
lean_closure_set(v___f_937_, 1, v___x_936_);
lean_closure_set(v___f_937_, 2, v_inst_926_);
v___x_938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_938_, 0, v___x_933_);
lean_ctor_set(v___x_938_, 1, v___x_935_);
lean_ctor_set(v___x_938_, 2, v___x_933_);
lean_ctor_set(v___x_938_, 3, v___x_933_);
lean_ctor_set(v___x_938_, 4, v___x_933_);
v___x_939_ = lean_apply_4(v_onAlt_927_, v___x_931_, v_resTy_928_, v___x_932_, v___x_938_);
v___x_940_ = lean_apply_4(v_toBind_929_, lean_box(0), lean_box(0), v___x_939_, v___f_937_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_941_, lean_object* v_useSplitter_942_, lean_object* v_inst_943_, lean_object* v_onAlt_944_, lean_object* v_resTy_945_, lean_object* v_toBind_946_, lean_object* v_h_947_){
_start:
{
uint8_t v_useSplitter_boxed_948_; lean_object* v_res_949_; 
v_useSplitter_boxed_948_ = lean_unbox(v_useSplitter_942_);
v_res_949_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_941_, v_useSplitter_boxed_948_, v_inst_943_, v_onAlt_944_, v_resTy_945_, v_toBind_946_, v_h_947_);
lean_dec(v___x_941_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_950_, uint8_t v_useSplitter_951_, lean_object* v_inst_952_, lean_object* v_onAlt_953_, lean_object* v_resTy_954_, lean_object* v_toBind_955_, lean_object* v_h_956_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___f_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_957_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_958_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_959_ = lean_mk_empty_array_with_capacity(v___x_950_);
v___x_960_ = lean_array_push(v___x_959_, v_h_956_);
v___x_961_ = lean_box(v_useSplitter_951_);
lean_inc_ref(v___x_960_);
v___f_962_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_962_, 0, v___x_960_);
lean_closure_set(v___f_962_, 1, v___x_961_);
lean_closure_set(v___f_962_, 2, v_inst_952_);
v___x_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_963_, 0, v___x_958_);
lean_ctor_set(v___x_963_, 1, v___x_960_);
lean_ctor_set(v___x_963_, 2, v___x_958_);
lean_ctor_set(v___x_963_, 3, v___x_958_);
lean_ctor_set(v___x_963_, 4, v___x_958_);
v___x_964_ = lean_apply_4(v_onAlt_953_, v___x_957_, v_resTy_954_, v___x_950_, v___x_963_);
v___x_965_ = lean_apply_4(v_toBind_955_, lean_box(0), lean_box(0), v___x_964_, v___f_962_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_966_, lean_object* v_useSplitter_967_, lean_object* v_inst_968_, lean_object* v_onAlt_969_, lean_object* v_resTy_970_, lean_object* v_toBind_971_, lean_object* v_h_972_){
_start:
{
uint8_t v_useSplitter_boxed_973_; lean_object* v_res_974_; 
v_useSplitter_boxed_973_ = lean_unbox(v_useSplitter_967_);
v_res_974_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_966_, v_useSplitter_boxed_973_, v_inst_968_, v_onAlt_969_, v_resTy_970_, v_toBind_971_, v_h_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_975_, lean_object* v_resTy_976_, lean_object* v_c_977_, lean_object* v_h_978_, lean_object* v_t_979_, lean_object* v_toPure_980_, lean_object* v_e_981_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_982_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_983_ = lean_box(0);
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v_u_975_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = l_Lean_mkConst(v___x_982_, v___x_984_);
v___x_986_ = l_Lean_mkApp5(v___x_985_, v_resTy_976_, v_c_977_, v_h_978_, v_t_979_, v_e_981_);
v___x_987_ = lean_apply_2(v_toPure_980_, lean_box(0), v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_988_, lean_object* v_resTy_989_, lean_object* v_c_990_, lean_object* v_h_991_, lean_object* v_toPure_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_n_995_, uint8_t v___x_996_, lean_object* v___f_997_, uint8_t v___x_998_, lean_object* v_toBind_999_, lean_object* v_t_1000_){
_start:
{
lean_object* v___f_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_inc_ref(v_c_990_);
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1001_, 0, v_u_988_);
lean_closure_set(v___f_1001_, 1, v_resTy_989_);
lean_closure_set(v___f_1001_, 2, v_c_990_);
lean_closure_set(v___f_1001_, 3, v_h_991_);
lean_closure_set(v___f_1001_, 4, v_t_1000_);
lean_closure_set(v___f_1001_, 5, v_toPure_992_);
v___x_1002_ = l_Lean_mkNot(v_c_990_);
v___x_1003_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_993_, v_inst_994_, v_n_995_, v___x_996_, v___x_1002_, v___f_997_, v___x_998_);
v___x_1004_ = lean_apply_4(v_toBind_999_, lean_box(0), lean_box(0), v___x_1003_, v___f_1001_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_1005_, lean_object* v_resTy_1006_, lean_object* v_c_1007_, lean_object* v_h_1008_, lean_object* v_toPure_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_n_1012_, lean_object* v___x_1013_, lean_object* v___f_1014_, lean_object* v___x_1015_, lean_object* v_toBind_1016_, lean_object* v_t_1017_){
_start:
{
uint8_t v___x_1249__boxed_1018_; uint8_t v___x_1251__boxed_1019_; lean_object* v_res_1020_; 
v___x_1249__boxed_1018_ = lean_unbox(v___x_1013_);
v___x_1251__boxed_1019_ = lean_unbox(v___x_1015_);
v_res_1020_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_1005_, v_resTy_1006_, v_c_1007_, v_h_1008_, v_toPure_1009_, v_inst_1010_, v_inst_1011_, v_n_1012_, v___x_1249__boxed_1018_, v___f_1014_, v___x_1251__boxed_1019_, v_toBind_1016_, v_t_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_1021_, lean_object* v_resTy_1022_, lean_object* v_c_1023_, lean_object* v_h_1024_, lean_object* v_toPure_1025_, lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v___f_1028_, lean_object* v_toBind_1029_, lean_object* v___f_1030_, lean_object* v_n_1031_){
_start:
{
uint8_t v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1032_ = 0;
v___x_1033_ = 0;
v___x_1034_ = lean_box(v___x_1032_);
v___x_1035_ = lean_box(v___x_1033_);
lean_inc(v_toBind_1029_);
lean_inc(v_n_1031_);
lean_inc_ref(v_inst_1027_);
lean_inc_ref(v_inst_1026_);
lean_inc_ref(v_c_1023_);
v___f_1036_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1036_, 0, v_u_1021_);
lean_closure_set(v___f_1036_, 1, v_resTy_1022_);
lean_closure_set(v___f_1036_, 2, v_c_1023_);
lean_closure_set(v___f_1036_, 3, v_h_1024_);
lean_closure_set(v___f_1036_, 4, v_toPure_1025_);
lean_closure_set(v___f_1036_, 5, v_inst_1026_);
lean_closure_set(v___f_1036_, 6, v_inst_1027_);
lean_closure_set(v___f_1036_, 7, v_n_1031_);
lean_closure_set(v___f_1036_, 8, v___x_1034_);
lean_closure_set(v___f_1036_, 9, v___f_1028_);
lean_closure_set(v___f_1036_, 10, v___x_1035_);
lean_closure_set(v___f_1036_, 11, v_toBind_1029_);
v___x_1037_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1026_, v_inst_1027_, v_n_1031_, v___x_1032_, v_c_1023_, v___f_1030_, v___x_1033_);
v___x_1038_ = lean_apply_4(v_toBind_1029_, lean_box(0), lean_box(0), v___x_1037_, v___f_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Core_mkFreshUserName(v___x_1039_, v___y_1042_, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1060_, uint8_t v_useSplitter_1061_, lean_object* v_resTy_1062_, lean_object* v_toPure_1063_, lean_object* v_onAlt_1064_, lean_object* v_toBind_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_u_1069_){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_c_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v_h_1078_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = l_Lean_Expr_getAppNumArgs(v_e_1060_);
v___x_1072_ = lean_nat_sub(v___x_1071_, v___x_1070_);
v___x_1073_ = lean_nat_sub(v___x_1072_, v___x_1070_);
lean_dec(v___x_1072_);
v_c_1074_ = l_Lean_Expr_getRevArg_x21(v_e_1060_, v___x_1073_);
v___x_1075_ = lean_unsigned_to_nat(2u);
v___x_1076_ = lean_nat_sub(v___x_1071_, v___x_1075_);
lean_dec(v___x_1071_);
v___x_1077_ = lean_nat_sub(v___x_1076_, v___x_1070_);
lean_dec(v___x_1076_);
v_h_1078_ = l_Lean_Expr_getRevArg_x21(v_e_1060_, v___x_1077_);
if (v_useSplitter_1061_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref(v_inst_1068_);
lean_dec_ref(v_inst_1067_);
lean_dec(v_inst_1066_);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1065_);
lean_inc(v_onAlt_1064_);
lean_inc_ref(v_resTy_1062_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1082_, 0, v_u_1069_);
lean_closure_set(v___f_1082_, 1, v_resTy_1062_);
lean_closure_set(v___f_1082_, 2, v_c_1074_);
lean_closure_set(v___f_1082_, 3, v_h_1078_);
lean_closure_set(v___f_1082_, 4, v_toPure_1063_);
lean_closure_set(v___f_1082_, 5, v_onAlt_1064_);
lean_closure_set(v___f_1082_, 6, v___x_1070_);
lean_closure_set(v___f_1082_, 7, v___x_1081_);
lean_closure_set(v___f_1082_, 8, v_toBind_1065_);
v___x_1083_ = lean_apply_4(v_onAlt_1064_, v___x_1079_, v_resTy_1062_, v___x_1080_, v___x_1081_);
v___x_1084_ = lean_apply_4(v_toBind_1065_, lean_box(0), lean_box(0), v___x_1083_, v___f_1082_);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1085_ = lean_box(v_useSplitter_1061_);
lean_inc_n(v_toBind_1065_, 3);
lean_inc_ref_n(v_resTy_1062_, 2);
lean_inc(v_onAlt_1064_);
lean_inc_n(v_inst_1066_, 2);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1086_, 0, v___x_1070_);
lean_closure_set(v___f_1086_, 1, v___x_1085_);
lean_closure_set(v___f_1086_, 2, v_inst_1066_);
lean_closure_set(v___f_1086_, 3, v_onAlt_1064_);
lean_closure_set(v___f_1086_, 4, v_resTy_1062_);
lean_closure_set(v___f_1086_, 5, v_toBind_1065_);
v___x_1087_ = lean_box(v_useSplitter_1061_);
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1088_, 0, v___x_1070_);
lean_closure_set(v___f_1088_, 1, v___x_1087_);
lean_closure_set(v___f_1088_, 2, v_inst_1066_);
lean_closure_set(v___f_1088_, 3, v_onAlt_1064_);
lean_closure_set(v___f_1088_, 4, v_resTy_1062_);
lean_closure_set(v___f_1088_, 5, v_toBind_1065_);
v___f_1089_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1089_, 0, v_u_1069_);
lean_closure_set(v___f_1089_, 1, v_resTy_1062_);
lean_closure_set(v___f_1089_, 2, v_c_1074_);
lean_closure_set(v___f_1089_, 3, v_h_1078_);
lean_closure_set(v___f_1089_, 4, v_toPure_1063_);
lean_closure_set(v___f_1089_, 5, v_inst_1067_);
lean_closure_set(v___f_1089_, 6, v_inst_1068_);
lean_closure_set(v___f_1089_, 7, v___f_1088_);
lean_closure_set(v___f_1089_, 8, v_toBind_1065_);
lean_closure_set(v___f_1089_, 9, v___f_1086_);
v___f_1090_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1091_ = lean_apply_2(v_inst_1066_, lean_box(0), v___f_1090_);
v___x_1092_ = lean_apply_4(v_toBind_1065_, lean_box(0), lean_box(0), v___x_1091_, v___f_1089_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1093_, lean_object* v_useSplitter_1094_, lean_object* v_resTy_1095_, lean_object* v_toPure_1096_, lean_object* v_onAlt_1097_, lean_object* v_toBind_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_u_1102_){
_start:
{
uint8_t v_useSplitter_boxed_1103_; lean_object* v_res_1104_; 
v_useSplitter_boxed_1103_ = lean_unbox(v_useSplitter_1094_);
v_res_1104_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1093_, v_useSplitter_boxed_1103_, v_resTy_1095_, v_toPure_1096_, v_onAlt_1097_, v_toBind_1098_, v_inst_1099_, v_inst_1100_, v_inst_1101_, v_u_1102_);
lean_dec_ref(v_e_1093_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1105_, lean_object* v_inst_1106_, lean_object* v_____do__lift_1107_){
_start:
{
uint8_t v___x_1108_; uint8_t v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1108_ = 0;
v___x_1109_ = 1;
v___x_1110_ = 1;
v___x_1111_ = lean_box(v___x_1108_);
v___x_1112_ = lean_box(v___x_1109_);
v___x_1113_ = lean_box(v___x_1108_);
v___x_1114_ = lean_box(v___x_1109_);
v___x_1115_ = lean_box(v___x_1110_);
v___x_1116_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1116_, 0, v___x_1105_);
lean_closure_set(v___x_1116_, 1, v_____do__lift_1107_);
lean_closure_set(v___x_1116_, 2, v___x_1111_);
lean_closure_set(v___x_1116_, 3, v___x_1112_);
lean_closure_set(v___x_1116_, 4, v___x_1113_);
lean_closure_set(v___x_1116_, 5, v___x_1114_);
lean_closure_set(v___x_1116_, 6, v___x_1115_);
v___x_1117_ = lean_apply_2(v_inst_1106_, lean_box(0), v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1118_, lean_object* v_onAlt_1119_, lean_object* v_resTy_1120_, lean_object* v_toBind_1121_, lean_object* v_h_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_mk_empty_array_with_capacity(v___x_1125_);
v___x_1127_ = lean_array_push(v___x_1126_, v_h_1122_);
lean_inc_ref_n(v___x_1127_, 2);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1128_, 0, v___x_1127_);
lean_closure_set(v___f_1128_, 1, v_inst_1118_);
v___x_1129_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_1130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1127_);
lean_ctor_set(v___x_1130_, 1, v___x_1127_);
lean_ctor_set(v___x_1130_, 2, v___x_1129_);
lean_ctor_set(v___x_1130_, 3, v___x_1129_);
lean_ctor_set(v___x_1130_, 4, v___x_1129_);
v___x_1131_ = lean_apply_4(v_onAlt_1119_, v___x_1123_, v_resTy_1120_, v___x_1124_, v___x_1130_);
v___x_1132_ = lean_apply_4(v_toBind_1121_, lean_box(0), lean_box(0), v___x_1131_, v___f_1128_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1133_, lean_object* v_inst_1134_, lean_object* v_onAlt_1135_, lean_object* v_resTy_1136_, lean_object* v_toBind_1137_, lean_object* v_h_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1139_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1140_ = lean_mk_empty_array_with_capacity(v___x_1133_);
v___x_1141_ = lean_array_push(v___x_1140_, v_h_1138_);
lean_inc_ref_n(v___x_1141_, 2);
v___f_1142_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1142_, 0, v___x_1141_);
lean_closure_set(v___f_1142_, 1, v_inst_1134_);
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1141_);
lean_ctor_set(v___x_1144_, 1, v___x_1141_);
lean_ctor_set(v___x_1144_, 2, v___x_1143_);
lean_ctor_set(v___x_1144_, 3, v___x_1143_);
lean_ctor_set(v___x_1144_, 4, v___x_1143_);
v___x_1145_ = lean_apply_4(v_onAlt_1135_, v___x_1139_, v_resTy_1136_, v___x_1133_, v___x_1144_);
v___x_1146_ = lean_apply_4(v_toBind_1137_, lean_box(0), lean_box(0), v___x_1145_, v___f_1142_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1147_, lean_object* v_onAlt_1148_, lean_object* v_resTy_1149_, lean_object* v_toBind_1150_, lean_object* v_e_1151_, lean_object* v_toPure_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v___f_1155_, lean_object* v_u_1156_){
_start:
{
lean_object* v___x_1157_; lean_object* v___f_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_c_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_h_1166_; lean_object* v___f_1167_; lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_toBind_1150_, 2);
lean_inc_ref(v_resTy_1149_);
lean_inc(v_inst_1147_);
v___f_1158_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1158_, 0, v___x_1157_);
lean_closure_set(v___f_1158_, 1, v_inst_1147_);
lean_closure_set(v___f_1158_, 2, v_onAlt_1148_);
lean_closure_set(v___f_1158_, 3, v_resTy_1149_);
lean_closure_set(v___f_1158_, 4, v_toBind_1150_);
v___x_1159_ = l_Lean_Expr_getAppNumArgs(v_e_1151_);
v___x_1160_ = lean_nat_sub(v___x_1159_, v___x_1157_);
v___x_1161_ = lean_nat_sub(v___x_1160_, v___x_1157_);
lean_dec(v___x_1160_);
v_c_1162_ = l_Lean_Expr_getRevArg_x21(v_e_1151_, v___x_1161_);
v___x_1163_ = lean_unsigned_to_nat(2u);
v___x_1164_ = lean_nat_sub(v___x_1159_, v___x_1163_);
lean_dec(v___x_1159_);
v___x_1165_ = lean_nat_sub(v___x_1164_, v___x_1157_);
lean_dec(v___x_1164_);
v_h_1166_ = l_Lean_Expr_getRevArg_x21(v_e_1151_, v___x_1165_);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1167_, 0, v_u_1156_);
lean_closure_set(v___f_1167_, 1, v_resTy_1149_);
lean_closure_set(v___f_1167_, 2, v_c_1162_);
lean_closure_set(v___f_1167_, 3, v_h_1166_);
lean_closure_set(v___f_1167_, 4, v_toPure_1152_);
lean_closure_set(v___f_1167_, 5, v_inst_1153_);
lean_closure_set(v___f_1167_, 6, v_inst_1154_);
lean_closure_set(v___f_1167_, 7, v___f_1158_);
lean_closure_set(v___f_1167_, 8, v_toBind_1150_);
lean_closure_set(v___f_1167_, 9, v___f_1155_);
v___f_1168_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1169_ = lean_apply_2(v_inst_1147_, lean_box(0), v___f_1168_);
v___x_1170_ = lean_apply_4(v_toBind_1150_, lean_box(0), lean_box(0), v___x_1169_, v___f_1167_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1171_, lean_object* v_onAlt_1172_, lean_object* v_resTy_1173_, lean_object* v_toBind_1174_, lean_object* v_e_1175_, lean_object* v_toPure_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v___f_1179_, lean_object* v_u_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1171_, v_onAlt_1172_, v_resTy_1173_, v_toBind_1174_, v_e_1175_, v_toPure_1176_, v_inst_1177_, v_inst_1178_, v___f_1179_, v_u_1180_);
lean_dec_ref(v_e_1175_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_onAlt_1182_, lean_object* v_idx_1183_, lean_object* v_expAltType_1184_, lean_object* v_altFVars_1185_, lean_object* v___alt_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1187_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1188_ = lean_unsigned_to_nat(1u);
v___x_1189_ = lean_nat_add(v_idx_1183_, v___x_1188_);
v___x_1190_ = lean_name_append_index_after(v___x_1187_, v___x_1189_);
v___x_1191_ = lean_apply_4(v_onAlt_1182_, v___x_1190_, v_expAltType_1184_, v_idx_1183_, v_altFVars_1185_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(lean_object* v_onAlt_1192_, lean_object* v_idx_1193_, lean_object* v_expAltType_1194_, lean_object* v_altFVars_1195_, lean_object* v___alt_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(v_onAlt_1192_, v_idx_1193_, v_expAltType_1194_, v_altFVars_1195_, v___alt_1196_);
lean_dec_ref(v___alt_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_mask_1198_, lean_object* v_absMotiveBody_1199_, lean_object* v_toPure_1200_, lean_object* v_xs_1201_, lean_object* v___body_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = l_Array_mask___redArg(v_mask_1198_, v_xs_1201_);
v___x_1204_ = lean_expr_instantiate_rev(v_absMotiveBody_1199_, v___x_1203_);
lean_dec(v___x_1203_);
v___x_1205_ = lean_apply_2(v_toPure_1200_, lean_box(0), v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(lean_object* v_mask_1206_, lean_object* v_absMotiveBody_1207_, lean_object* v_toPure_1208_, lean_object* v_xs_1209_, lean_object* v___body_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(v_mask_1206_, v_absMotiveBody_1207_, v_toPure_1208_, v_xs_1209_, v___body_1210_);
lean_dec_ref(v___body_1210_);
lean_dec_ref(v_absMotiveBody_1207_);
lean_dec_ref(v_mask_1206_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v_toFunctor_1212_, lean_object* v_mask_1213_, lean_object* v_toPure_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_matcherApp_1220_, uint8_t v_useSplitter_1221_, lean_object* v___f_1222_, lean_object* v___f_1223_, lean_object* v_absMotiveBody_1224_){
_start:
{
lean_object* v_map_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_map_1225_ = lean_ctor_get(v_toFunctor_1212_, 0);
lean_inc(v_map_1225_);
lean_dec_ref(v_toFunctor_1212_);
lean_inc(v_toPure_1214_);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_1226_, 0, v_mask_1213_);
lean_closure_set(v___f_1226_, 1, v_absMotiveBody_1224_);
lean_closure_set(v___f_1226_, 2, v_toPure_1214_);
v___x_1227_ = lean_apply_1(v_toPure_1214_, lean_box(0));
lean_inc(v___x_1227_);
v___x_1228_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1215_, v_inst_1216_, v_inst_1217_, v_inst_1218_, v_inst_1219_, v_matcherApp_1220_, v_useSplitter_1221_, v_useSplitter_1221_, v___x_1227_, v___f_1226_, v___f_1222_, v___x_1227_);
v___x_1229_ = lean_apply_4(v_map_1225_, lean_box(0), lean_box(0), v___f_1223_, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v_toFunctor_1230_, lean_object* v_mask_1231_, lean_object* v_toPure_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_matcherApp_1238_, lean_object* v_useSplitter_1239_, lean_object* v___f_1240_, lean_object* v___f_1241_, lean_object* v_absMotiveBody_1242_){
_start:
{
uint8_t v_useSplitter_boxed_1243_; lean_object* v_res_1244_; 
v_useSplitter_boxed_1243_ = lean_unbox(v_useSplitter_1239_);
v_res_1244_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v_toFunctor_1230_, v_mask_1231_, v_toPure_1232_, v_inst_1233_, v_inst_1234_, v_inst_1235_, v_inst_1236_, v_inst_1237_, v_matcherApp_1238_, v_useSplitter_boxed_1243_, v___f_1240_, v___f_1241_, v_absMotiveBody_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_info_1252_, lean_object* v_resTy_1253_, lean_object* v_onAlt_1254_, uint8_t v_useSplitter_1255_){
_start:
{
switch(lean_obj_tag(v_info_1252_))
{
case 0:
{
lean_object* v_toApplicative_1256_; lean_object* v_toBind_1257_; lean_object* v_toPure_1258_; lean_object* v_e_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_toApplicative_1256_ = lean_ctor_get(v_inst_1249_, 0);
lean_dec_ref(v_inst_1251_);
lean_dec_ref(v_inst_1250_);
v_toBind_1257_ = lean_ctor_get(v_inst_1249_, 1);
lean_inc_n(v_toBind_1257_, 2);
v_toPure_1258_ = lean_ctor_get(v_toApplicative_1256_, 1);
lean_inc(v_toPure_1258_);
v_e_1259_ = lean_ctor_get(v_info_1252_, 0);
lean_inc_ref(v_e_1259_);
lean_dec_ref_known(v_info_1252_, 1);
v___x_1260_ = lean_box(v_useSplitter_1255_);
lean_inc(v_inst_1247_);
lean_inc_ref(v_resTy_1253_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1261_, 0, v_e_1259_);
lean_closure_set(v___f_1261_, 1, v___x_1260_);
lean_closure_set(v___f_1261_, 2, v_resTy_1253_);
lean_closure_set(v___f_1261_, 3, v_toPure_1258_);
lean_closure_set(v___f_1261_, 4, v_onAlt_1254_);
lean_closure_set(v___f_1261_, 5, v_toBind_1257_);
lean_closure_set(v___f_1261_, 6, v_inst_1247_);
lean_closure_set(v___f_1261_, 7, v_inst_1248_);
lean_closure_set(v___f_1261_, 8, v_inst_1249_);
v___x_1262_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1262_, 0, v_resTy_1253_);
v___x_1263_ = lean_apply_2(v_inst_1247_, lean_box(0), v___x_1262_);
v___x_1264_ = lean_apply_4(v_toBind_1257_, lean_box(0), lean_box(0), v___x_1263_, v___f_1261_);
return v___x_1264_;
}
case 1:
{
lean_object* v_toApplicative_1265_; lean_object* v_toBind_1266_; lean_object* v_toPure_1267_; lean_object* v_e_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_toApplicative_1265_ = lean_ctor_get(v_inst_1249_, 0);
lean_dec_ref(v_inst_1251_);
lean_dec_ref(v_inst_1250_);
v_toBind_1266_ = lean_ctor_get(v_inst_1249_, 1);
lean_inc_n(v_toBind_1266_, 3);
v_toPure_1267_ = lean_ctor_get(v_toApplicative_1265_, 1);
lean_inc(v_toPure_1267_);
v_e_1268_ = lean_ctor_get(v_info_1252_, 0);
lean_inc_ref(v_e_1268_);
lean_dec_ref_known(v_info_1252_, 1);
lean_inc_ref_n(v_resTy_1253_, 2);
lean_inc(v_onAlt_1254_);
lean_inc_n(v_inst_1247_, 2);
v___f_1269_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1269_, 0, v_inst_1247_);
lean_closure_set(v___f_1269_, 1, v_onAlt_1254_);
lean_closure_set(v___f_1269_, 2, v_resTy_1253_);
lean_closure_set(v___f_1269_, 3, v_toBind_1266_);
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1270_, 0, v_inst_1247_);
lean_closure_set(v___f_1270_, 1, v_onAlt_1254_);
lean_closure_set(v___f_1270_, 2, v_resTy_1253_);
lean_closure_set(v___f_1270_, 3, v_toBind_1266_);
lean_closure_set(v___f_1270_, 4, v_e_1268_);
lean_closure_set(v___f_1270_, 5, v_toPure_1267_);
lean_closure_set(v___f_1270_, 6, v_inst_1248_);
lean_closure_set(v___f_1270_, 7, v_inst_1249_);
lean_closure_set(v___f_1270_, 8, v___f_1269_);
v___x_1271_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1271_, 0, v_resTy_1253_);
v___x_1272_ = lean_apply_2(v_inst_1247_, lean_box(0), v___x_1271_);
v___x_1273_ = lean_apply_4(v_toBind_1266_, lean_box(0), lean_box(0), v___x_1272_, v___f_1270_);
return v___x_1273_;
}
default: 
{
lean_object* v_toApplicative_1274_; lean_object* v_matcherApp_1275_; lean_object* v_toBind_1276_; lean_object* v_toFunctor_1277_; lean_object* v_toPure_1278_; lean_object* v_discrs_1279_; lean_object* v___f_1280_; lean_object* v___f_1281_; lean_object* v___f_1282_; lean_object* v___x_1283_; size_t v_sz_1284_; size_t v___x_1285_; lean_object* v_mask_1286_; lean_object* v___x_1287_; lean_object* v___f_1288_; lean_object* v_maskedDiscrs_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_toApplicative_1274_ = lean_ctor_get(v_inst_1249_, 0);
v_matcherApp_1275_ = lean_ctor_get(v_info_1252_, 0);
lean_inc_ref(v_matcherApp_1275_);
lean_dec_ref_known(v_info_1252_, 1);
v_toBind_1276_ = lean_ctor_get(v_inst_1249_, 1);
lean_inc(v_toBind_1276_);
v_toFunctor_1277_ = lean_ctor_get(v_toApplicative_1274_, 0);
lean_inc_ref(v_toFunctor_1277_);
v_toPure_1278_ = lean_ctor_get(v_toApplicative_1274_, 1);
lean_inc(v_toPure_1278_);
v_discrs_1279_ = lean_ctor_get(v_matcherApp_1275_, 5);
lean_inc_ref_n(v_discrs_1279_, 2);
v___f_1280_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
v___f_1281_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed), 5, 1);
lean_closure_set(v___f_1281_, 0, v_onAlt_1254_);
v___f_1282_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1));
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v_sz_1284_ = lean_array_size(v_discrs_1279_);
v___x_1285_ = ((size_t)0ULL);
v_mask_1286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1283_, v___f_1282_, v_sz_1284_, v___x_1285_, v_discrs_1279_);
v___x_1287_ = lean_box(v_useSplitter_1255_);
lean_inc(v_inst_1247_);
lean_inc(v_mask_1286_);
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 13, 12);
lean_closure_set(v___f_1288_, 0, v_toFunctor_1277_);
lean_closure_set(v___f_1288_, 1, v_mask_1286_);
lean_closure_set(v___f_1288_, 2, v_toPure_1278_);
lean_closure_set(v___f_1288_, 3, v_inst_1247_);
lean_closure_set(v___f_1288_, 4, v_inst_1248_);
lean_closure_set(v___f_1288_, 5, v_inst_1249_);
lean_closure_set(v___f_1288_, 6, v_inst_1250_);
lean_closure_set(v___f_1288_, 7, v_inst_1251_);
lean_closure_set(v___f_1288_, 8, v_matcherApp_1275_);
lean_closure_set(v___f_1288_, 9, v___x_1287_);
lean_closure_set(v___f_1288_, 10, v___f_1281_);
lean_closure_set(v___f_1288_, 11, v___f_1280_);
v_maskedDiscrs_1289_ = l_Array_mask___redArg(v_mask_1286_, v_discrs_1279_);
lean_dec(v_mask_1286_);
v___x_1290_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1290_, 0, v_resTy_1253_);
lean_closure_set(v___x_1290_, 1, v_maskedDiscrs_1289_);
v___x_1291_ = lean_apply_2(v_inst_1247_, lean_box(0), v___x_1290_);
v___x_1292_ = lean_apply_4(v_toBind_1276_, lean_box(0), lean_box(0), v___x_1291_, v___f_1288_);
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_info_1298_, lean_object* v_resTy_1299_, lean_object* v_onAlt_1300_, lean_object* v_useSplitter_1301_){
_start:
{
uint8_t v_useSplitter_boxed_1302_; lean_object* v_res_1303_; 
v_useSplitter_boxed_1302_ = lean_unbox(v_useSplitter_1301_);
v_res_1303_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1293_, v_inst_1294_, v_inst_1295_, v_inst_1296_, v_inst_1297_, v_info_1298_, v_resTy_1299_, v_onAlt_1300_, v_useSplitter_boxed_1302_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_info_1313_, lean_object* v_resTy_1314_, lean_object* v_onAlt_1315_, uint8_t v_useSplitter_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1305_, v_inst_1306_, v_inst_1307_, v_inst_1308_, v_inst_1309_, v_info_1313_, v_resTy_1314_, v_onAlt_1315_, v_useSplitter_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_info_1327_, lean_object* v_resTy_1328_, lean_object* v_onAlt_1329_, lean_object* v_useSplitter_1330_){
_start:
{
uint8_t v_useSplitter_boxed_1331_; lean_object* v_res_1332_; 
v_useSplitter_boxed_1331_ = lean_unbox(v_useSplitter_1330_);
v_res_1332_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1318_, v_inst_1319_, v_inst_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_inst_1324_, v_inst_1325_, v_inst_1326_, v_info_1327_, v_resTy_1328_, v_onAlt_1329_, v_useSplitter_boxed_1331_);
lean_dec(v_inst_1326_);
lean_dec(v_inst_1325_);
lean_dec_ref(v_inst_1324_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1333_, lean_object* v_e_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
if (lean_obj_tag(v_info_1333_) == 2)
{
lean_object* v_matcherApp_1343_; lean_object* v_toMatcherInfo_1344_; lean_object* v___x_1345_; 
v_matcherApp_1343_ = lean_ctor_get(v_info_1333_, 0);
lean_inc_ref(v_matcherApp_1343_);
lean_dec_ref_known(v_info_1333_, 1);
v_toMatcherInfo_1344_ = lean_ctor_get(v_matcherApp_1343_, 0);
lean_inc_ref(v_toMatcherInfo_1344_);
lean_dec_ref(v_matcherApp_1343_);
v___x_1345_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1344_, v_e_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
return v___x_1345_;
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v_e_1334_);
lean_dec_ref(v_info_1333_);
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
return v___x_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1348_, lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1348_, v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; lean_object* v_env_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1362_ = lean_st_ref_get(v___y_1360_);
v_env_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc_ref(v_env_1363_);
lean_dec(v___x_1362_);
v___x_1364_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1363_, v_declName_1359_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1366_, v___y_1367_);
lean_dec(v___y_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v_env_1377_; lean_object* v___x_1378_; lean_object* v_mctx_1379_; lean_object* v_lctx_1380_; lean_object* v_options_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1376_ = lean_st_ref_get(v___y_1374_);
v_env_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_env_1377_);
lean_dec(v___x_1376_);
v___x_1378_ = lean_st_ref_get(v___y_1372_);
v_mctx_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc_ref(v_mctx_1379_);
lean_dec(v___x_1378_);
v_lctx_1380_ = lean_ctor_get(v___y_1371_, 2);
v_options_1381_ = lean_ctor_get(v___y_1373_, 2);
lean_inc_ref(v_options_1381_);
lean_inc_ref(v_lctx_1380_);
v___x_1382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1382_, 0, v_env_1377_);
lean_ctor_set(v___x_1382_, 1, v_mctx_1379_);
lean_ctor_set(v___x_1382_, 2, v_lctx_1380_);
lean_ctor_set(v___x_1382_, 3, v_options_1381_);
v___x_1383_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v_msgData_1370_);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_ref_1398_; lean_object* v___x_1399_; lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1408_; 
v_ref_1398_ = lean_ctor_get(v___y_1395_, 5);
v___x_1399_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1408_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1406_; 
lean_inc(v_ref_1398_);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v_ref_1398_);
lean_ctor_set(v___x_1404_, 1, v_a_1400_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 1);
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1406_ = v___x_1402_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_1416_, lean_object* v_msg_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_fileName_1423_; lean_object* v_fileMap_1424_; lean_object* v_options_1425_; lean_object* v_currRecDepth_1426_; lean_object* v_maxRecDepth_1427_; lean_object* v_ref_1428_; lean_object* v_currNamespace_1429_; lean_object* v_openDecls_1430_; lean_object* v_initHeartbeats_1431_; lean_object* v_maxHeartbeats_1432_; lean_object* v_quotContext_1433_; lean_object* v_currMacroScope_1434_; uint8_t v_diag_1435_; lean_object* v_cancelTk_x3f_1436_; uint8_t v_suppressElabErrors_1437_; lean_object* v_inheritedTraceOptions_1438_; lean_object* v_ref_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_fileName_1423_ = lean_ctor_get(v___y_1420_, 0);
v_fileMap_1424_ = lean_ctor_get(v___y_1420_, 1);
v_options_1425_ = lean_ctor_get(v___y_1420_, 2);
v_currRecDepth_1426_ = lean_ctor_get(v___y_1420_, 3);
v_maxRecDepth_1427_ = lean_ctor_get(v___y_1420_, 4);
v_ref_1428_ = lean_ctor_get(v___y_1420_, 5);
v_currNamespace_1429_ = lean_ctor_get(v___y_1420_, 6);
v_openDecls_1430_ = lean_ctor_get(v___y_1420_, 7);
v_initHeartbeats_1431_ = lean_ctor_get(v___y_1420_, 8);
v_maxHeartbeats_1432_ = lean_ctor_get(v___y_1420_, 9);
v_quotContext_1433_ = lean_ctor_get(v___y_1420_, 10);
v_currMacroScope_1434_ = lean_ctor_get(v___y_1420_, 11);
v_diag_1435_ = lean_ctor_get_uint8(v___y_1420_, sizeof(void*)*14);
v_cancelTk_x3f_1436_ = lean_ctor_get(v___y_1420_, 12);
v_suppressElabErrors_1437_ = lean_ctor_get_uint8(v___y_1420_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1438_ = lean_ctor_get(v___y_1420_, 13);
v_ref_1439_ = l_Lean_replaceRef(v_ref_1416_, v_ref_1428_);
lean_inc_ref(v_inheritedTraceOptions_1438_);
lean_inc(v_cancelTk_x3f_1436_);
lean_inc(v_currMacroScope_1434_);
lean_inc(v_quotContext_1433_);
lean_inc(v_maxHeartbeats_1432_);
lean_inc(v_initHeartbeats_1431_);
lean_inc(v_openDecls_1430_);
lean_inc(v_currNamespace_1429_);
lean_inc(v_maxRecDepth_1427_);
lean_inc(v_currRecDepth_1426_);
lean_inc_ref(v_options_1425_);
lean_inc_ref(v_fileMap_1424_);
lean_inc_ref(v_fileName_1423_);
v___x_1440_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1440_, 0, v_fileName_1423_);
lean_ctor_set(v___x_1440_, 1, v_fileMap_1424_);
lean_ctor_set(v___x_1440_, 2, v_options_1425_);
lean_ctor_set(v___x_1440_, 3, v_currRecDepth_1426_);
lean_ctor_set(v___x_1440_, 4, v_maxRecDepth_1427_);
lean_ctor_set(v___x_1440_, 5, v_ref_1439_);
lean_ctor_set(v___x_1440_, 6, v_currNamespace_1429_);
lean_ctor_set(v___x_1440_, 7, v_openDecls_1430_);
lean_ctor_set(v___x_1440_, 8, v_initHeartbeats_1431_);
lean_ctor_set(v___x_1440_, 9, v_maxHeartbeats_1432_);
lean_ctor_set(v___x_1440_, 10, v_quotContext_1433_);
lean_ctor_set(v___x_1440_, 11, v_currMacroScope_1434_);
lean_ctor_set(v___x_1440_, 12, v_cancelTk_x3f_1436_);
lean_ctor_set(v___x_1440_, 13, v_inheritedTraceOptions_1438_);
lean_ctor_set_uint8(v___x_1440_, sizeof(void*)*14, v_diag_1435_);
lean_ctor_set_uint8(v___x_1440_, sizeof(void*)*14 + 1, v_suppressElabErrors_1437_);
v___x_1441_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1417_, v___y_1418_, v___y_1419_, v___x_1440_, v___y_1421_);
lean_dec_ref_known(v___x_1440_, 14);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1442_, lean_object* v_msg_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1442_, v_msg_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v_ref_1442_);
return v_res_1449_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
lean_ctor_set(v___x_1455_, 2, v___x_1454_);
lean_ctor_set(v___x_1455_, 3, v___x_1454_);
lean_ctor_set(v___x_1455_, 4, v___x_1453_);
lean_ctor_set(v___x_1455_, 5, v___x_1453_);
lean_ctor_set(v___x_1455_, 6, v___x_1453_);
lean_ctor_set(v___x_1455_, 7, v___x_1453_);
lean_ctor_set(v___x_1455_, 8, v___x_1453_);
lean_ctor_set(v___x_1455_, 9, v___x_1453_);
return v___x_1455_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_unsigned_to_nat(32u);
v___x_1457_ = lean_mk_empty_array_with_capacity(v___x_1456_);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1459_ = ((size_t)5ULL);
v___x_1460_ = lean_unsigned_to_nat(0u);
v___x_1461_ = lean_unsigned_to_nat(32u);
v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1461_);
v___x_1463_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1464_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
lean_ctor_set(v___x_1464_, 1, v___x_1462_);
lean_ctor_set(v___x_1464_, 2, v___x_1460_);
lean_ctor_set(v___x_1464_, 3, v___x_1460_);
lean_ctor_set_usize(v___x_1464_, 4, v___x_1459_);
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1465_ = lean_box(1);
v___x_1466_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1466_);
lean_ctor_set(v___x_1468_, 2, v___x_1465_);
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1471_ = l_Lean_stringToMessageData(v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1490_, lean_object* v_declHint_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; lean_object* v_env_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_st_ref_get(v___y_1492_);
v_env_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc_ref(v_env_1495_);
lean_dec(v___x_1494_);
v___x_1496_ = l_Lean_Name_isAnonymous(v_declHint_1491_);
if (v___x_1496_ == 0)
{
uint8_t v_isExporting_1497_; 
v_isExporting_1497_ = lean_ctor_get_uint8(v_env_1495_, sizeof(void*)*8);
if (v_isExporting_1497_ == 0)
{
lean_object* v___x_1498_; 
lean_dec_ref(v_env_1495_);
lean_dec(v_declHint_1491_);
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_msg_1490_);
return v___x_1498_;
}
else
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
lean_inc_ref(v_env_1495_);
v___x_1499_ = l_Lean_Environment_setExporting(v_env_1495_, v___x_1496_);
lean_inc(v_declHint_1491_);
lean_inc_ref(v___x_1499_);
v___x_1500_ = l_Lean_Environment_contains(v___x_1499_, v_declHint_1491_, v_isExporting_1497_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_dec_ref(v___x_1499_);
lean_dec_ref(v_env_1495_);
lean_dec(v_declHint_1491_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_msg_1490_);
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_c_1507_; lean_object* v___x_1508_; 
v___x_1502_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1503_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1504_ = l_Lean_Options_empty;
v___x_1505_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1499_);
lean_ctor_set(v___x_1505_, 1, v___x_1502_);
lean_ctor_set(v___x_1505_, 2, v___x_1503_);
lean_ctor_set(v___x_1505_, 3, v___x_1504_);
lean_inc(v_declHint_1491_);
v___x_1506_ = l_Lean_MessageData_ofConstName(v_declHint_1491_, v___x_1496_);
v_c_1507_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1507_, 0, v___x_1505_);
lean_ctor_set(v_c_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1495_, v_declHint_1491_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec_ref(v_env_1495_);
lean_dec(v_declHint_1491_);
v___x_1509_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v_c_1507_);
v___x_1511_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Lean_MessageData_note(v___x_1512_);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_msg_1490_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
else
{
lean_object* v_val_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1551_; 
v_val_1516_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1518_ = v___x_1508_;
v_isShared_1519_ = v_isSharedCheck_1551_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_val_1516_);
lean_dec(v___x_1508_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1551_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_mod_1523_; uint8_t v___x_1524_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = l_Lean_Environment_header(v_env_1495_);
lean_dec_ref(v_env_1495_);
v___x_1522_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1521_);
v_mod_1523_ = lean_array_get(v___x_1520_, v___x_1522_, v_val_1516_);
lean_dec(v_val_1516_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = l_Lean_isPrivateName(v_declHint_1491_);
lean_dec(v_declHint_1491_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1525_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v_c_1507_);
v___x_1527_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = l_Lean_MessageData_ofName(v_mod_1523_);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_MessageData_note(v___x_1532_);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v_msg_1490_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1534_);
v___x_1536_ = v___x_1518_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v_c_1507_);
v___x_1540_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l_Lean_MessageData_ofName(v_mod_1523_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_MessageData_note(v___x_1545_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_msg_1490_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1547_);
v___x_1549_ = v___x_1518_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1552_; 
lean_dec_ref(v_env_1495_);
lean_dec(v_declHint_1491_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_msg_1490_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1553_, lean_object* v_declHint_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1553_, v_declHint_1554_, v___y_1555_);
lean_dec(v___y_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1558_, lean_object* v_declHint_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1575_; 
v___x_1565_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1558_, v_declHint_1559_, v___y_1563_);
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1575_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1575_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1570_ = l_Lean_unknownIdentifierMessageTag;
v___x_1571_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v_a_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1571_);
v___x_1573_ = v___x_1568_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1576_, lean_object* v_declHint_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1576_, v_declHint_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1584_, lean_object* v_msg_1585_, lean_object* v_declHint_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v_a_1593_; lean_object* v___x_1594_; 
v___x_1592_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1585_, v_declHint_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1584_, v_a_1593_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1595_, lean_object* v_msg_1596_, lean_object* v_declHint_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1595_, v_msg_1596_, v_declHint_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v_ref_1595_);
return v_res_1603_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1606_ = l_Lean_stringToMessageData(v___x_1605_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1609_ = l_Lean_stringToMessageData(v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1610_, lean_object* v_constName_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1617_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1618_ = 0;
lean_inc(v_constName_1611_);
v___x_1619_ = l_Lean_MessageData_ofConstName(v_constName_1611_, v___x_1618_);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1617_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1610_, v___x_1622_, v_constName_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1624_, lean_object* v_constName_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1624_, v_constName_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v_ref_1624_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_ref_1638_; lean_object* v___x_1639_; 
v_ref_1638_ = lean_ctor_get(v___y_1635_, 5);
v___x_1639_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1638_, v_constName_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v_env_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; 
v___x_1653_ = lean_st_ref_get(v___y_1651_);
v_env_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc_ref(v_env_1654_);
lean_dec(v___x_1653_);
v___x_1655_ = 0;
lean_inc(v_constName_1647_);
v___x_1656_ = l_Lean_Environment_find_x3f(v_env_1654_, v_constName_1647_, v___x_1655_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
return v___x_1657_;
}
else
{
lean_object* v_val_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_constName_1647_);
v_val_1658_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1656_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_val_1658_);
lean_dec(v___x_1656_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 0);
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_val_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; lean_object* v_toApplicative_1680_; lean_object* v_toFunctor_1681_; lean_object* v_toSeq_1682_; lean_object* v_toSeqLeft_1683_; lean_object* v_toSeqRight_1684_; lean_object* v___f_1685_; lean_object* v___f_1686_; lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_toApplicative_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1727_; 
v___x_1679_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_1680_ = lean_ctor_get(v___x_1679_, 0);
v_toFunctor_1681_ = lean_ctor_get(v_toApplicative_1680_, 0);
v_toSeq_1682_ = lean_ctor_get(v_toApplicative_1680_, 2);
v_toSeqLeft_1683_ = lean_ctor_get(v_toApplicative_1680_, 3);
v_toSeqRight_1684_ = lean_ctor_get(v_toApplicative_1680_, 4);
v___f_1685_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_1686_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1681_, 2);
v___f_1687_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1687_, 0, v_toFunctor_1681_);
v___f_1688_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1688_, 0, v_toFunctor_1681_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___f_1687_);
lean_ctor_set(v___x_1689_, 1, v___f_1688_);
lean_inc(v_toSeqRight_1684_);
v___f_1690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1690_, 0, v_toSeqRight_1684_);
lean_inc(v_toSeqLeft_1683_);
v___f_1691_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1691_, 0, v_toSeqLeft_1683_);
lean_inc(v_toSeq_1682_);
v___f_1692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1692_, 0, v_toSeq_1682_);
v___x_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1689_);
lean_ctor_set(v___x_1693_, 1, v___f_1685_);
lean_ctor_set(v___x_1693_, 2, v___f_1692_);
lean_ctor_set(v___x_1693_, 3, v___f_1691_);
lean_ctor_set(v___x_1693_, 4, v___f_1690_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___f_1686_);
v___x_1695_ = l_StateRefT_x27_instMonad___redArg(v___x_1694_);
v_toApplicative_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v___x_1695_, 1);
lean_dec(v_unused_1728_);
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1727_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_toApplicative_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1727_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_toFunctor_1700_; lean_object* v_toSeq_1701_; lean_object* v_toSeqLeft_1702_; lean_object* v_toSeqRight_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1725_; 
v_toFunctor_1700_ = lean_ctor_get(v_toApplicative_1696_, 0);
v_toSeq_1701_ = lean_ctor_get(v_toApplicative_1696_, 2);
v_toSeqLeft_1702_ = lean_ctor_get(v_toApplicative_1696_, 3);
v_toSeqRight_1703_ = lean_ctor_get(v_toApplicative_1696_, 4);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_toApplicative_1696_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v_toApplicative_1696_, 1);
lean_dec(v_unused_1726_);
v___x_1705_ = v_toApplicative_1696_;
v_isShared_1706_ = v_isSharedCheck_1725_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_toSeqRight_1703_);
lean_inc(v_toSeqLeft_1702_);
lean_inc(v_toSeq_1701_);
lean_inc(v_toFunctor_1700_);
lean_dec(v_toApplicative_1696_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1725_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___x_1716_; 
v___f_1707_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_1708_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_1700_);
v___f_1709_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1709_, 0, v_toFunctor_1700_);
v___f_1710_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1710_, 0, v_toFunctor_1700_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___f_1709_);
lean_ctor_set(v___x_1711_, 1, v___f_1710_);
v___f_1712_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1712_, 0, v_toSeqRight_1703_);
v___f_1713_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1713_, 0, v_toSeqLeft_1702_);
v___f_1714_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1714_, 0, v_toSeq_1701_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 4, v___f_1712_);
lean_ctor_set(v___x_1705_, 3, v___f_1713_);
lean_ctor_set(v___x_1705_, 2, v___f_1714_);
lean_ctor_set(v___x_1705_, 1, v___f_1707_);
lean_ctor_set(v___x_1705_, 0, v___x_1711_);
v___x_1716_ = v___x_1705_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___f_1707_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v___f_1714_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v___f_1713_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v___f_1712_);
v___x_1716_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___f_1708_);
lean_ctor_set(v___x_1698_, 0, v___x_1716_);
v___x_1718_ = v___x_1698_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___f_1708_);
v___x_1718_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_2921__overap_1721_; lean_object* v___x_1722_; 
v___x_1719_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1720_ = l_instInhabitedOfMonad___redArg(v___x_1718_, v___x_1719_);
v___x_2921__overap_1721_ = lean_panic_fn_borrowed(v___x_1720_, v_msg_1673_);
lean_dec(v___x_1720_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
v___x_1722_ = lean_apply_5(v___x_2921__overap_1721_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
return v___x_1722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
return v_res_1735_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_1740_ = lean_unsigned_to_nat(53u);
v___x_1741_ = lean_unsigned_to_nat(62u);
v___x_1742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_1743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_1744_ = l_mkPanicMessageWithDecl(v___x_1743_, v___x_1742_, v___x_1741_, v___x_1740_, v___x_1739_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_1745_, size_t v_i_1746_, lean_object* v_bs_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_lt(v_i_1746_, v_sz_1745_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_bs_1747_);
return v___x_1754_;
}
else
{
lean_object* v_v_1755_; lean_object* v___x_1756_; 
v_v_1755_ = lean_array_uget_borrowed(v_bs_1747_, v_i_1746_);
lean_inc(v_v_1755_);
v___x_1756_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_1755_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v_bs_x27_1759_; lean_object* v_a_1761_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1756_, 1);
v___x_1758_ = lean_unsigned_to_nat(0u);
v_bs_x27_1759_ = lean_array_uset(v_bs_1747_, v_i_1746_, v___x_1758_);
if (lean_obj_tag(v_a_1757_) == 6)
{
lean_object* v_val_1766_; lean_object* v_numFields_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; 
v_val_1766_ = lean_ctor_get(v_a_1757_, 0);
lean_inc_ref(v_val_1766_);
lean_dec_ref_known(v_a_1757_, 1);
v_numFields_1767_ = lean_ctor_get(v_val_1766_, 4);
lean_inc(v_numFields_1767_);
lean_dec_ref(v_val_1766_);
v___x_1768_ = 0;
v___x_1769_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1769_, 0, v_numFields_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1758_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*2, v___x_1768_);
v_a_1761_ = v___x_1769_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v_a_1757_);
v___x_1770_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
v___x_1771_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_1770_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v_a_1761_ = v_a_1772_;
goto v___jp_1760_;
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_bs_x27_1759_);
v_a_1773_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1771_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1771_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
v___jp_1760_:
{
size_t v___x_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = lean_usize_add(v_i_1746_, v___x_1762_);
v___x_1764_ = lean_array_uset(v_bs_x27_1759_, v_i_1746_, v_a_1761_);
v_i_1746_ = v___x_1763_;
v_bs_1747_ = v___x_1764_;
goto _start;
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v_bs_1747_);
v_a_1781_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1756_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1756_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_1789_, lean_object* v_i_1790_, lean_object* v_bs_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
size_t v_sz_boxed_1797_; size_t v_i_boxed_1798_; lean_object* v_res_1799_; 
v_sz_boxed_1797_ = lean_unbox_usize(v_sz_1789_);
lean_dec(v_sz_1789_);
v_i_boxed_1798_ = lean_unbox_usize(v_i_1790_);
lean_dec(v_i_1790_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_1797_, v_i_boxed_1798_, v_bs_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1799_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1800_; lean_object* v_dummy_1801_; 
v___x_1800_ = lean_box(0);
v_dummy_1801_ = l_Lean_Expr_sort___override(v___x_1800_);
return v_dummy_1801_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_unsigned_to_nat(16u);
v___x_1804_ = lean_mk_array(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
lean_ctor_set(v___x_1807_, 1, v___x_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_1810_, uint8_t v_alsoCasesOn_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = l_Lean_Expr_isApp(v_e_1810_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v_e_1810_);
v___x_1821_ = lean_box(0);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
else
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Lean_Expr_getAppFn(v_e_1810_);
if (lean_obj_tag(v___x_1823_) == 4)
{
lean_object* v_declName_1824_; lean_object* v_us_1825_; lean_object* v___x_1826_; lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1981_; 
v_declName_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc_n(v_declName_1824_, 2);
v_us_1825_ = lean_ctor_get(v___x_1823_, 1);
lean_inc(v_us_1825_);
lean_dec_ref_known(v___x_1823_, 2);
v___x_1826_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1824_, v___y_1815_);
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1981_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1981_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
if (lean_obj_tag(v_a_1827_) == 1)
{
lean_object* v_val_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1873_; 
v_val_1831_ = lean_ctor_get(v_a_1827_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_a_1827_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1833_ = v_a_1827_;
v_isShared_1834_ = v_isSharedCheck_1873_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_val_1831_);
lean_dec(v_a_1827_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1873_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_dummy_1835_; lean_object* v_nargs_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v_args_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v_dummy_1835_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v_nargs_1836_ = l_Lean_Expr_getAppNumArgs(v_e_1810_);
lean_inc(v_nargs_1836_);
v___x_1837_ = lean_mk_array(v_nargs_1836_, v_dummy_1835_);
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_sub(v_nargs_1836_, v___x_1838_);
lean_dec(v_nargs_1836_);
v_args_1840_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1810_, v___x_1837_, v___x_1839_);
v___x_1841_ = lean_array_get_size(v_args_1840_);
v___x_1842_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1831_);
v___x_1843_ = lean_nat_dec_lt(v___x_1841_, v___x_1842_);
lean_dec(v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v_numParams_1844_; lean_object* v_numDiscrs_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v_numParams_1844_ = lean_ctor_get(v_val_1831_, 0);
v_numDiscrs_1845_ = lean_ctor_get(v_val_1831_, 1);
v___x_1846_ = lean_array_mk(v_us_1825_);
v___x_1847_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1844_);
v___x_1848_ = l_Array_extract___redArg(v_args_1840_, v___x_1847_, v_numParams_1844_);
v___x_1849_ = l_Lean_instInhabitedExpr;
v___x_1850_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1831_);
v___x_1851_ = lean_array_get(v___x_1849_, v_args_1840_, v___x_1850_);
lean_dec(v___x_1850_);
v___x_1852_ = lean_nat_add(v_numParams_1844_, v___x_1838_);
v___x_1853_ = lean_nat_add(v___x_1852_, v_numDiscrs_1845_);
lean_inc(v___x_1853_);
lean_inc_ref_n(v_args_1840_, 2);
v___x_1854_ = l_Array_toSubarray___redArg(v_args_1840_, v___x_1852_, v___x_1853_);
v___x_1855_ = l_Subarray_copy___redArg(v___x_1854_);
v___x_1856_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1831_);
v___x_1857_ = lean_nat_add(v___x_1853_, v___x_1856_);
lean_dec(v___x_1856_);
lean_inc(v___x_1857_);
v___x_1858_ = l_Array_toSubarray___redArg(v_args_1840_, v___x_1853_, v___x_1857_);
v___x_1859_ = l_Subarray_copy___redArg(v___x_1858_);
v___x_1860_ = l_Array_toSubarray___redArg(v_args_1840_, v___x_1857_, v___x_1841_);
v___x_1861_ = l_Subarray_copy___redArg(v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1862_, 0, v_val_1831_);
lean_ctor_set(v___x_1862_, 1, v_declName_1824_);
lean_ctor_set(v___x_1862_, 2, v___x_1846_);
lean_ctor_set(v___x_1862_, 3, v___x_1848_);
lean_ctor_set(v___x_1862_, 4, v___x_1851_);
lean_ctor_set(v___x_1862_, 5, v___x_1855_);
lean_ctor_set(v___x_1862_, 6, v___x_1859_);
lean_ctor_set(v___x_1862_, 7, v___x_1861_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1862_);
v___x_1864_ = v___x_1833_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1864_);
v___x_1866_ = v___x_1829_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec_ref(v_args_1840_);
lean_del_object(v___x_1833_);
lean_dec(v_val_1831_);
lean_dec(v_us_1825_);
lean_dec(v_declName_1824_);
v___x_1869_ = lean_box(0);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1869_);
v___x_1871_ = v___x_1829_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v___x_1874_; 
lean_del_object(v___x_1829_);
lean_dec(v_a_1827_);
v___x_1874_ = lean_st_ref_get(v___y_1815_);
if (v_alsoCasesOn_1811_ == 0)
{
lean_dec(v___x_1874_);
lean_dec(v_us_1825_);
lean_dec(v_declName_1824_);
lean_dec_ref(v_e_1810_);
goto v___jp_1817_;
}
else
{
lean_object* v_env_1875_; uint8_t v___x_1876_; 
v_env_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc_ref(v_env_1875_);
lean_dec(v___x_1874_);
lean_inc(v_declName_1824_);
v___x_1876_ = l_Lean_isCasesOnRecursor(v_env_1875_, v_declName_1824_);
if (v___x_1876_ == 0)
{
lean_dec(v_us_1825_);
lean_dec(v_declName_1824_);
lean_dec_ref(v_e_1810_);
goto v___jp_1817_;
}
else
{
lean_object* v_indName_1877_; lean_object* v___x_1878_; 
v_indName_1877_ = l_Lean_Name_getPrefix(v_declName_1824_);
v___x_1878_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_1877_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1972_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1881_ = v___x_1878_;
v_isShared_1882_ = v_isSharedCheck_1972_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1972_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
if (lean_obj_tag(v_a_1879_) == 5)
{
lean_object* v_val_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1967_; 
v_val_1883_ = lean_ctor_get(v_a_1879_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_a_1879_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1885_ = v_a_1879_;
v_isShared_1886_ = v_isSharedCheck_1967_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_val_1883_);
lean_dec(v_a_1879_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1967_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_toConstantVal_1887_; lean_object* v_numParams_1888_; lean_object* v_numIndices_1889_; lean_object* v_ctors_1890_; lean_object* v_nargs_1891_; lean_object* v_dummy_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_args_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_toConstantVal_1887_ = lean_ctor_get(v_val_1883_, 0);
lean_inc_ref(v_toConstantVal_1887_);
v_numParams_1888_ = lean_ctor_get(v_val_1883_, 1);
lean_inc(v_numParams_1888_);
v_numIndices_1889_ = lean_ctor_get(v_val_1883_, 2);
lean_inc(v_numIndices_1889_);
v_ctors_1890_ = lean_ctor_get(v_val_1883_, 4);
lean_inc(v_ctors_1890_);
v_nargs_1891_ = l_Lean_Expr_getAppNumArgs(v_e_1810_);
v_dummy_1892_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
lean_inc(v_nargs_1891_);
v___x_1893_ = lean_mk_array(v_nargs_1891_, v_dummy_1892_);
v___x_1894_ = lean_unsigned_to_nat(1u);
v___x_1895_ = lean_nat_sub(v_nargs_1891_, v___x_1894_);
lean_dec(v_nargs_1891_);
v_args_1896_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1810_, v___x_1893_, v___x_1895_);
v___x_1897_ = lean_nat_add(v_numParams_1888_, v___x_1894_);
v___x_1898_ = lean_nat_add(v___x_1897_, v_numIndices_1889_);
v___x_1899_ = lean_nat_add(v___x_1898_, v___x_1894_);
lean_dec(v___x_1898_);
v___x_1900_ = l_Lean_InductiveVal_numCtors(v_val_1883_);
lean_dec_ref(v_val_1883_);
v___x_1901_ = lean_nat_add(v___x_1899_, v___x_1900_);
lean_dec(v___x_1900_);
v___x_1902_ = lean_array_get_size(v_args_1896_);
v___x_1903_ = lean_nat_dec_le(v___x_1901_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec(v___x_1901_);
lean_dec(v___x_1899_);
lean_dec(v___x_1897_);
lean_dec_ref(v_args_1896_);
lean_dec(v_ctors_1890_);
lean_dec(v_numIndices_1889_);
lean_dec(v_numParams_1888_);
lean_dec_ref(v_toConstantVal_1887_);
lean_del_object(v___x_1885_);
lean_dec(v_us_1825_);
lean_dec(v_declName_1824_);
v___x_1904_ = lean_box(0);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1904_);
v___x_1906_ = v___x_1881_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v___x_1908_; lean_object* v_params_1909_; lean_object* v___x_1910_; lean_object* v_motive_1911_; lean_object* v_discrs_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_discrInfos_1915_; lean_object* v_alts_1916_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v_lower_1958_; lean_object* v_upper_1959_; uint8_t v___x_1966_; 
lean_del_object(v___x_1881_);
v___x_1908_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1888_);
lean_inc_ref_n(v_args_1896_, 3);
v_params_1909_ = l_Array_toSubarray___redArg(v_args_1896_, v___x_1908_, v_numParams_1888_);
v___x_1910_ = l_Lean_instInhabitedExpr;
v_motive_1911_ = lean_array_get(v___x_1910_, v_args_1896_, v_numParams_1888_);
lean_dec(v_numParams_1888_);
lean_inc(v___x_1899_);
v_discrs_1912_ = l_Array_toSubarray___redArg(v_args_1896_, v___x_1897_, v___x_1899_);
v___x_1913_ = lean_nat_add(v_numIndices_1889_, v___x_1894_);
lean_dec(v_numIndices_1889_);
v___x_1914_ = lean_box(0);
v_discrInfos_1915_ = lean_mk_array(v___x_1913_, v___x_1914_);
lean_inc(v___x_1901_);
v_alts_1916_ = l_Array_toSubarray___redArg(v_args_1896_, v___x_1899_, v___x_1901_);
v___x_1966_ = lean_nat_dec_le(v___x_1901_, v___x_1908_);
if (v___x_1966_ == 0)
{
v_lower_1958_ = v___x_1901_;
v_upper_1959_ = v___x_1902_;
goto v___jp_1957_;
}
else
{
lean_dec(v___x_1901_);
v_lower_1958_ = v___x_1908_;
v_upper_1959_ = v___x_1902_;
goto v___jp_1957_;
}
v___jp_1917_:
{
lean_object* v___x_1920_; size_t v_sz_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1920_ = lean_array_mk(v_ctors_1890_);
v_sz_1921_ = lean_array_size(v___x_1920_);
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_1921_, v___x_1922_, v___x_1920_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1948_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1948_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1948_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v_start_1928_; lean_object* v_stop_1929_; lean_object* v_start_1930_; lean_object* v_stop_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v_start_1928_ = lean_ctor_get(v_params_1909_, 1);
lean_inc(v_start_1928_);
v_stop_1929_ = lean_ctor_get(v_params_1909_, 2);
lean_inc(v_stop_1929_);
v_start_1930_ = lean_ctor_get(v_discrs_1912_, 1);
lean_inc(v_start_1930_);
v_stop_1931_ = lean_ctor_get(v_discrs_1912_, 2);
lean_inc(v_stop_1931_);
v___x_1932_ = lean_nat_sub(v_stop_1929_, v_start_1928_);
lean_dec(v_start_1928_);
lean_dec(v_stop_1929_);
v___x_1933_ = lean_nat_sub(v_stop_1931_, v_start_1930_);
lean_dec(v_start_1930_);
lean_dec(v_stop_1931_);
v___x_1934_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
v___x_1935_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1932_);
lean_ctor_set(v___x_1935_, 1, v___x_1933_);
lean_ctor_set(v___x_1935_, 2, v_a_1924_);
lean_ctor_set(v___x_1935_, 3, v___y_1919_);
lean_ctor_set(v___x_1935_, 4, v_discrInfos_1915_);
lean_ctor_set(v___x_1935_, 5, v___x_1934_);
v___x_1936_ = lean_array_mk(v_us_1825_);
v___x_1937_ = l_Subarray_copy___redArg(v_params_1909_);
v___x_1938_ = l_Subarray_copy___redArg(v_discrs_1912_);
v___x_1939_ = l_Subarray_copy___redArg(v_alts_1916_);
v___x_1940_ = l_Subarray_copy___redArg(v___y_1918_);
v___x_1941_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1935_);
lean_ctor_set(v___x_1941_, 1, v_declName_1824_);
lean_ctor_set(v___x_1941_, 2, v___x_1936_);
lean_ctor_set(v___x_1941_, 3, v___x_1937_);
lean_ctor_set(v___x_1941_, 4, v_motive_1911_);
lean_ctor_set(v___x_1941_, 5, v___x_1938_);
lean_ctor_set(v___x_1941_, 6, v___x_1939_);
lean_ctor_set(v___x_1941_, 7, v___x_1940_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 1);
lean_ctor_set(v___x_1885_, 0, v___x_1941_);
v___x_1943_ = v___x_1885_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1945_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1943_);
v___x_1945_ = v___x_1926_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec_ref(v_alts_1916_);
lean_dec_ref(v_discrInfos_1915_);
lean_dec_ref(v_discrs_1912_);
lean_dec(v_motive_1911_);
lean_dec_ref(v_params_1909_);
lean_del_object(v___x_1885_);
lean_dec(v_us_1825_);
lean_dec(v_declName_1824_);
v_a_1949_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1923_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1923_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
v___jp_1957_:
{
lean_object* v_levelParams_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v_levelParams_1960_ = lean_ctor_get(v_toConstantVal_1887_, 1);
lean_inc(v_levelParams_1960_);
lean_dec_ref(v_toConstantVal_1887_);
v___x_1961_ = l_Array_toSubarray___redArg(v_args_1896_, v_lower_1958_, v_upper_1959_);
v___x_1962_ = l_List_lengthTR___redArg(v_levelParams_1960_);
lean_dec(v_levelParams_1960_);
v___x_1963_ = l_List_lengthTR___redArg(v_us_1825_);
v___x_1964_ = lean_nat_dec_eq(v___x_1962_, v___x_1963_);
lean_dec(v___x_1963_);
lean_dec(v___x_1962_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3));
v___y_1918_ = v___x_1961_;
v___y_1919_ = v___x_1965_;
goto v___jp_1917_;
}
else
{
v___y_1918_ = v___x_1961_;
v___y_1919_ = v___x_1914_;
goto v___jp_1917_;
}
}
}
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
lean_dec(v_a_1879_);
lean_dec(v_us_1825_);
lean_dec(v_declName_1824_);
lean_dec_ref(v_e_1810_);
v___x_1968_ = lean_box(0);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1968_);
v___x_1970_ = v___x_1881_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec(v_us_1825_);
lean_dec(v_declName_1824_);
lean_dec_ref(v_e_1810_);
v_a_1973_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1878_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1878_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
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
lean_dec_ref(v___x_1823_);
lean_dec_ref(v_e_1810_);
goto v___jp_1817_;
}
}
v___jp_1817_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_1982_, lean_object* v_alsoCasesOn_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1989_; lean_object* v_res_1990_; 
v_alsoCasesOn_boxed_1989_ = lean_unbox(v_alsoCasesOn_1983_);
v_res_1990_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1982_, v_alsoCasesOn_boxed_1989_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_1998_ = l_Lean_Expr_isAppOf(v_e_1991_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2000_ = l_Lean_Expr_isAppOf(v_e_1991_, v___x_1999_);
if (v___x_2000_ == 0)
{
uint8_t v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = 1;
v___x_2002_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1991_, v___x_2001_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2023_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2023_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2023_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
if (lean_obj_tag(v_a_2003_) == 1)
{
lean_object* v_val_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2018_; 
v_val_2007_ = lean_ctor_get(v_a_2003_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_a_2003_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2009_ = v_a_2003_;
v_isShared_2010_ = v_isSharedCheck_2018_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_val_2007_);
lean_dec(v_a_2003_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2018_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2011_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2011_, 0, v_val_2007_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2011_);
v___x_2013_ = v___x_2009_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2013_);
v___x_2015_ = v___x_2005_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_dec(v_a_2003_);
v___x_2019_ = lean_box(0);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2019_);
v___x_2021_ = v___x_2005_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_a_2024_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2002_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2002_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2032_, 0, v_e_1991_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_e_1991_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2045_, v___y_2049_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2059_, lean_object* v_constName_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2067_, lean_object* v_constName_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2067_, v_constName_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2075_, lean_object* v_ref_2076_, lean_object* v_constName_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2076_, v_constName_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_ref_2085_, lean_object* v_constName_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2084_, v_ref_2085_, v_constName_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v_ref_2085_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2093_, lean_object* v_ref_2094_, lean_object* v_msg_2095_, lean_object* v_declHint_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2094_, v_msg_2095_, v_declHint_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2103_, lean_object* v_ref_2104_, lean_object* v_msg_2105_, lean_object* v_declHint_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2103_, v_ref_2104_, v_msg_2105_, v_declHint_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v_ref_2104_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2113_, lean_object* v_declHint_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2113_, v_declHint_2114_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2121_, lean_object* v_declHint_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2121_, v_declHint_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2129_, lean_object* v_ref_2130_, lean_object* v_msg_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2130_, v_msg_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_ref_2139_, lean_object* v_msg_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2138_, v_ref_2139_, v_msg_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v_ref_2139_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2147_, lean_object* v_msg_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2155_, lean_object* v_msg_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2155_, v_msg_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2162_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2165_ = l_Lean_stringToMessageData(v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2166_, lean_object* v_e_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___y_2174_; uint8_t v___y_2193_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2204_ = l_Lean_Expr_isAppOf(v_e_2167_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2206_ = l_Lean_Expr_isAppOf(v_e_2167_, v___x_2205_);
v___y_2193_ = v___x_2206_;
goto v___jp_2192_;
}
else
{
v___y_2193_ = v___x_2204_;
goto v___jp_2192_;
}
v___jp_2173_:
{
lean_object* v___x_2175_; 
lean_inc_ref(v___y_2174_);
v___x_2175_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2174_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
if (lean_obj_tag(v_a_2176_) == 1)
{
lean_object* v_val_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec_ref(v___y_2174_);
v_val_2177_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_val_2177_);
lean_dec_ref_known(v_a_2176_, 1);
v___x_2178_ = l_Lean_mkFVar(v_val_2177_);
v___x_2179_ = l_Lean_Meta_rwIfWith(v___x_2178_, v_e_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2179_;
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec(v_a_2176_);
lean_dec_ref(v_e_2167_);
v___x_2180_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2181_ = l_Lean_MessageData_ofExpr(v___y_2174_);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2180_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2182_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2183_;
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v___y_2174_);
lean_dec_ref(v_e_2167_);
v_a_2184_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2175_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2175_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
v___jp_2192_:
{
if (v___y_2193_ == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Meta_rwMatcher(v_idx_2166_, v_e_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2194_;
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_c_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2195_ = lean_unsigned_to_nat(1u);
v___x_2196_ = l_Lean_Expr_getAppNumArgs(v_e_2167_);
v___x_2197_ = lean_nat_sub(v___x_2196_, v___x_2195_);
lean_dec(v___x_2196_);
v___x_2198_ = lean_nat_sub(v___x_2197_, v___x_2195_);
lean_dec(v___x_2197_);
v_c_2199_ = l_Lean_Expr_getRevArg_x21(v_e_2167_, v___x_2198_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = lean_nat_dec_eq(v_idx_2166_, v___x_2200_);
lean_dec(v_idx_2166_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_mkNot(v_c_2199_);
v___y_2174_ = v___x_2202_;
goto v___jp_2173_;
}
else
{
v___y_2174_ = v_c_2199_;
goto v___jp_2173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2207_, lean_object* v_e_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2207_, v_e_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
return v_res_2214_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
