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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mask___redArg(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_withLocalDeclsDND___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 128, 245, 49, 225, 62, 36, 86)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "discr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 61, 20, 168, 108, 94, 13, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_etaExpand___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0;
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
lean_dec_ref(v_val_63_);
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
lean_inc_ref(v_motive_90_);
lean_dec_ref(v_matcherApp_85_);
v_discrInfos_91_ = lean_ctor_get(v_toMatcherInfo_89_, 4);
lean_inc_ref(v_discrInfos_91_);
lean_dec_ref(v_toMatcherInfo_89_);
v___x_92_ = lean_array_get_size(v_discrInfos_91_);
lean_dec_ref(v_discrInfos_91_);
lean_inc_ref(v_motive_90_);
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
lean_dec_ref(v___x_95_);
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
lean_dec_ref(v_info_127_);
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
lean_dec_ref(v_info_127_);
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
lean_inc_ref(v_matcherApp_163_);
lean_dec_ref(v_info_127_);
lean_inc_ref(v_matcherApp_163_);
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
lean_dec_ref(v_x_183_);
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
lean_inc_ref(v_c_406_);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed), 7, 2);
lean_closure_set(v___f_407_, 0, v_c_406_);
lean_closure_set(v___f_407_, 1, v_resTy_400_);
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_409_ = lean_box(0);
lean_inc_ref(v_inst_405_);
lean_inc_ref(v_inst_404_);
lean_inc_ref(v_c_406_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object* v_resTy_414_, lean_object* v_motiveArgs_415_, lean_object* v_x_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v___x_422_; uint8_t v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
v___x_422_ = 0;
v___x_423_ = 1;
v___x_424_ = 1;
v___x_425_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_415_, v_resTy_414_, v___x_422_, v___x_423_, v___x_422_, v___x_423_, v___x_424_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed(lean_object* v_resTy_426_, lean_object* v_motiveArgs_427_, lean_object* v_x_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(v_resTy_426_, v_motiveArgs_427_, v_x_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec_ref(v_x_428_);
lean_dec_ref(v_motiveArgs_427_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object* v_i_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_441_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1));
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_i_438_, v___x_442_);
v___x_444_ = lean_name_append_index_after(v___x_441_, v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_a_439_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed(lean_object* v_i_446_, lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(v_i_446_, v_a_447_, v_x_448_);
lean_dec(v_i_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object* v_i_453_, lean_object* v_toPure_454_, lean_object* v_____do__lift_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_456_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1));
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_i_453_, v___x_457_);
v___x_459_ = lean_name_append_index_after(v___x_456_, v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v_____do__lift_455_);
v___x_461_ = lean_apply_2(v_toPure_454_, lean_box(0), v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed(lean_object* v_i_462_, lean_object* v_toPure_463_, lean_object* v_____do__lift_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(v_i_462_, v_toPure_463_, v_____do__lift_464_);
lean_dec(v_i_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object* v_toPure_466_, lean_object* v_inst_467_, lean_object* v_toBind_468_, lean_object* v_i_469_, lean_object* v_a_470_, lean_object* v_x_471_){
_start:
{
lean_object* v___f_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___f_472_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed), 3, 2);
lean_closure_set(v___f_472_, 0, v_i_469_);
lean_closure_set(v___f_472_, 1, v_toPure_466_);
v___x_473_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_473_, 0, v_a_470_);
v___x_474_ = lean_apply_2(v_inst_467_, lean_box(0), v___x_473_);
v___x_475_ = lean_apply_4(v_toBind_468_, lean_box(0), lean_box(0), v___x_474_, v___f_472_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object* v_toMatcherInfo_478_, lean_object* v_matcherName_479_, lean_object* v_matcherLevels_480_, lean_object* v_params_481_, lean_object* v_motive_482_, lean_object* v_discrs_483_, lean_object* v_alts_484_, lean_object* v_k_485_, lean_object* v_____do__lift_486_){
_start:
{
lean_object* v___x_487_; lean_object* v_abstractMatcherApp_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_487_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
lean_inc_ref(v_discrs_483_);
v_abstractMatcherApp_488_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_abstractMatcherApp_488_, 0, v_toMatcherInfo_478_);
lean_ctor_set(v_abstractMatcherApp_488_, 1, v_matcherName_479_);
lean_ctor_set(v_abstractMatcherApp_488_, 2, v_matcherLevels_480_);
lean_ctor_set(v_abstractMatcherApp_488_, 3, v_params_481_);
lean_ctor_set(v_abstractMatcherApp_488_, 4, v_motive_482_);
lean_ctor_set(v_abstractMatcherApp_488_, 5, v_discrs_483_);
lean_ctor_set(v_abstractMatcherApp_488_, 6, v_____do__lift_486_);
lean_ctor_set(v_abstractMatcherApp_488_, 7, v___x_487_);
v___x_489_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_489_, 0, v_abstractMatcherApp_488_);
v___x_490_ = l_Array_append___redArg(v_discrs_483_, v_alts_484_);
v___x_491_ = lean_apply_2(v_k_485_, v___x_489_, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(lean_object* v_toMatcherInfo_492_, lean_object* v_matcherName_493_, lean_object* v_matcherLevels_494_, lean_object* v_params_495_, lean_object* v_motive_496_, lean_object* v_discrs_497_, lean_object* v_alts_498_, lean_object* v_k_499_, lean_object* v_____do__lift_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(v_toMatcherInfo_492_, v_matcherName_493_, v_matcherLevels_494_, v_params_495_, v_motive_496_, v_discrs_497_, v_alts_498_, v_k_499_, v_____do__lift_500_);
lean_dec_ref(v_alts_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object* v_toMatcherInfo_503_, lean_object* v_matcherName_504_, lean_object* v_matcherLevels_505_, lean_object* v_params_506_, lean_object* v_motive_507_, lean_object* v_discrs_508_, lean_object* v_k_509_, lean_object* v___x_510_, lean_object* v_inst_511_, lean_object* v_toBind_512_, lean_object* v_alts_513_){
_start:
{
lean_object* v___f_514_; lean_object* v___x_515_; size_t v_sz_516_; size_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_inc_ref(v_alts_513_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed), 9, 8);
lean_closure_set(v___f_514_, 0, v_toMatcherInfo_503_);
lean_closure_set(v___f_514_, 1, v_matcherName_504_);
lean_closure_set(v___f_514_, 2, v_matcherLevels_505_);
lean_closure_set(v___f_514_, 3, v_params_506_);
lean_closure_set(v___f_514_, 4, v_motive_507_);
lean_closure_set(v___f_514_, 5, v_discrs_508_);
lean_closure_set(v___f_514_, 6, v_alts_513_);
lean_closure_set(v___f_514_, 7, v_k_509_);
v___x_515_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0));
v_sz_516_ = lean_array_size(v_alts_513_);
v___x_517_ = ((size_t)0ULL);
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_510_, v___x_515_, v_sz_516_, v___x_517_, v_alts_513_);
v___x_519_ = lean_apply_2(v_inst_511_, lean_box(0), v___x_518_);
v___x_520_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v___x_519_, v___f_514_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object* v___f_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v___f_543_, lean_object* v_origAltTypes_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_altNamesTypes_549_; uint8_t v___x_550_; lean_object* v___x_551_; 
v___x_545_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9));
v___x_546_ = lean_array_get_size(v_origAltTypes_544_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_546_);
v_altNamesTypes_549_ = l_Array_mapFinIdxM_map___redArg(v___x_545_, v_origAltTypes_544_, v___f_540_, v___x_546_, v___x_547_, v___x_548_);
v___x_550_ = 0;
v___x_551_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_541_, v_inst_542_, v_altNamesTypes_549_, v___f_543_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object* v_toMatcherInfo_552_, lean_object* v_matcherName_553_, lean_object* v_params_554_, lean_object* v_motive_555_, lean_object* v_discrs_556_, lean_object* v_k_557_, lean_object* v___x_558_, lean_object* v_inst_559_, lean_object* v_toBind_560_, lean_object* v___f_561_, lean_object* v_inst_562_, lean_object* v_inst_563_, lean_object* v_alts_564_, lean_object* v_matcherLevels_565_){
_start:
{
lean_object* v___f_566_; lean_object* v___f_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_matcherPartial_570_; lean_object* v_matcherPartial_571_; lean_object* v_matcherPartial_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_inc(v_toBind_560_);
lean_inc(v_inst_559_);
lean_inc_ref(v_discrs_556_);
lean_inc_ref(v_motive_555_);
lean_inc_ref(v_params_554_);
lean_inc_ref(v_matcherLevels_565_);
lean_inc(v_matcherName_553_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19), 11, 10);
lean_closure_set(v___f_566_, 0, v_toMatcherInfo_552_);
lean_closure_set(v___f_566_, 1, v_matcherName_553_);
lean_closure_set(v___f_566_, 2, v_matcherLevels_565_);
lean_closure_set(v___f_566_, 3, v_params_554_);
lean_closure_set(v___f_566_, 4, v_motive_555_);
lean_closure_set(v___f_566_, 5, v_discrs_556_);
lean_closure_set(v___f_566_, 6, v_k_557_);
lean_closure_set(v___f_566_, 7, v___x_558_);
lean_closure_set(v___f_566_, 8, v_inst_559_);
lean_closure_set(v___f_566_, 9, v_toBind_560_);
v___f_567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20), 5, 4);
lean_closure_set(v___f_567_, 0, v___f_561_);
lean_closure_set(v___f_567_, 1, v_inst_562_);
lean_closure_set(v___f_567_, 2, v_inst_563_);
lean_closure_set(v___f_567_, 3, v___f_566_);
v___x_568_ = lean_array_to_list(v_matcherLevels_565_);
v___x_569_ = l_Lean_mkConst(v_matcherName_553_, v___x_568_);
v_matcherPartial_570_ = l_Lean_mkAppN(v___x_569_, v_params_554_);
lean_dec_ref(v_params_554_);
v_matcherPartial_571_ = l_Lean_Expr_app___override(v_matcherPartial_570_, v_motive_555_);
v_matcherPartial_572_ = l_Lean_mkAppN(v_matcherPartial_571_, v_discrs_556_);
lean_dec_ref(v_discrs_556_);
v___x_573_ = lean_array_get_size(v_alts_564_);
v___x_574_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_574_, 0, v___x_573_);
lean_closure_set(v___x_574_, 1, v_matcherPartial_572_);
v___x_575_ = lean_apply_2(v_inst_559_, lean_box(0), v___x_574_);
v___x_576_ = lean_apply_4(v_toBind_560_, lean_box(0), lean_box(0), v___x_575_, v___f_567_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(lean_object* v_toMatcherInfo_577_, lean_object* v_matcherName_578_, lean_object* v_params_579_, lean_object* v_motive_580_, lean_object* v_discrs_581_, lean_object* v_k_582_, lean_object* v___x_583_, lean_object* v_inst_584_, lean_object* v_toBind_585_, lean_object* v___f_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_alts_589_, lean_object* v_matcherLevels_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(v_toMatcherInfo_577_, v_matcherName_578_, v_params_579_, v_motive_580_, v_discrs_581_, v_k_582_, v___x_583_, v_inst_584_, v_toBind_585_, v___f_586_, v_inst_587_, v_inst_588_, v_alts_589_, v_matcherLevels_590_);
lean_dec_ref(v_alts_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object* v___f_592_, lean_object* v_matcherLevels_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_apply_1(v___f_592_, v_matcherLevels_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object* v_matcherLevels_595_, lean_object* v_val_596_, lean_object* v_toPure_597_, lean_object* v_toBind_598_, lean_object* v___f_599_, lean_object* v_uElim_600_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_array_set(v_matcherLevels_595_, v_val_596_, v_uElim_600_);
v___x_602_ = lean_apply_2(v_toPure_597_, lean_box(0), v___x_601_);
v___x_603_ = lean_apply_4(v_toBind_598_, lean_box(0), lean_box(0), v___x_602_, v___f_599_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(lean_object* v_matcherLevels_604_, lean_object* v_val_605_, lean_object* v_toPure_606_, lean_object* v_toBind_607_, lean_object* v___f_608_, lean_object* v_uElim_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(v_matcherLevels_604_, v_val_605_, v_toPure_606_, v_toBind_607_, v___f_608_, v_uElim_609_);
lean_dec(v_val_605_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object* v_toMatcherInfo_611_, lean_object* v_matcherName_612_, lean_object* v_params_613_, lean_object* v_discrs_614_, lean_object* v_k_615_, lean_object* v___x_616_, lean_object* v_inst_617_, lean_object* v_toBind_618_, lean_object* v___f_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_alts_622_, lean_object* v_toPure_623_, lean_object* v_matcherLevels_624_, lean_object* v_resTy_625_, lean_object* v_motive_626_){
_start:
{
lean_object* v_uElimPos_x3f_627_; lean_object* v___f_628_; 
v_uElimPos_x3f_627_ = lean_ctor_get(v_toMatcherInfo_611_, 3);
lean_inc(v_uElimPos_x3f_627_);
lean_inc(v_toBind_618_);
lean_inc(v_inst_617_);
v___f_628_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed), 14, 13);
lean_closure_set(v___f_628_, 0, v_toMatcherInfo_611_);
lean_closure_set(v___f_628_, 1, v_matcherName_612_);
lean_closure_set(v___f_628_, 2, v_params_613_);
lean_closure_set(v___f_628_, 3, v_motive_626_);
lean_closure_set(v___f_628_, 4, v_discrs_614_);
lean_closure_set(v___f_628_, 5, v_k_615_);
lean_closure_set(v___f_628_, 6, v___x_616_);
lean_closure_set(v___f_628_, 7, v_inst_617_);
lean_closure_set(v___f_628_, 8, v_toBind_618_);
lean_closure_set(v___f_628_, 9, v___f_619_);
lean_closure_set(v___f_628_, 10, v_inst_620_);
lean_closure_set(v___f_628_, 11, v_inst_621_);
lean_closure_set(v___f_628_, 12, v_alts_622_);
if (lean_obj_tag(v_uElimPos_x3f_627_) == 0)
{
lean_object* v___f_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec_ref(v_resTy_625_);
lean_dec(v_inst_617_);
v___f_629_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 2, 1);
lean_closure_set(v___f_629_, 0, v___f_628_);
v___x_630_ = lean_apply_2(v_toPure_623_, lean_box(0), v_matcherLevels_624_);
v___x_631_ = lean_apply_4(v_toBind_618_, lean_box(0), lean_box(0), v___x_630_, v___f_629_);
return v___x_631_;
}
else
{
lean_object* v_val_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_val_632_ = lean_ctor_get(v_uElimPos_x3f_627_, 0);
lean_inc(v_val_632_);
lean_dec_ref(v_uElimPos_x3f_627_);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 2, 1);
lean_closure_set(v___f_633_, 0, v___f_628_);
lean_inc(v_toBind_618_);
v___f_634_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed), 6, 5);
lean_closure_set(v___f_634_, 0, v_matcherLevels_624_);
lean_closure_set(v___f_634_, 1, v_val_632_);
lean_closure_set(v___f_634_, 2, v_toPure_623_);
lean_closure_set(v___f_634_, 3, v_toBind_618_);
lean_closure_set(v___f_634_, 4, v___f_633_);
v___x_635_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_635_, 0, v_resTy_625_);
v___x_636_ = lean_apply_2(v_inst_617_, lean_box(0), v___x_635_);
v___x_637_ = lean_apply_4(v_toBind_618_, lean_box(0), lean_box(0), v___x_636_, v___f_634_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object* v_toMatcherInfo_638_, lean_object* v_matcherName_639_, lean_object* v_params_640_, lean_object* v_k_641_, lean_object* v___x_642_, lean_object* v_inst_643_, lean_object* v_toBind_644_, lean_object* v___f_645_, lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_alts_648_, lean_object* v_toPure_649_, lean_object* v_matcherLevels_650_, lean_object* v_resTy_651_, lean_object* v___x_652_, lean_object* v_motive_653_, lean_object* v___f_654_, lean_object* v_discrs_655_){
_start:
{
lean_object* v___f_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_inc(v_toBind_644_);
lean_inc(v_inst_643_);
lean_inc_ref(v___x_642_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23), 16, 15);
lean_closure_set(v___f_656_, 0, v_toMatcherInfo_638_);
lean_closure_set(v___f_656_, 1, v_matcherName_639_);
lean_closure_set(v___f_656_, 2, v_params_640_);
lean_closure_set(v___f_656_, 3, v_discrs_655_);
lean_closure_set(v___f_656_, 4, v_k_641_);
lean_closure_set(v___f_656_, 5, v___x_642_);
lean_closure_set(v___f_656_, 6, v_inst_643_);
lean_closure_set(v___f_656_, 7, v_toBind_644_);
lean_closure_set(v___f_656_, 8, v___f_645_);
lean_closure_set(v___f_656_, 9, v_inst_646_);
lean_closure_set(v___f_656_, 10, v_inst_647_);
lean_closure_set(v___f_656_, 11, v_alts_648_);
lean_closure_set(v___f_656_, 12, v_toPure_649_);
lean_closure_set(v___f_656_, 13, v_matcherLevels_650_);
lean_closure_set(v___f_656_, 14, v_resTy_651_);
v___x_657_ = 0;
v___x_658_ = l_Lean_Meta_lambdaTelescope___redArg(v___x_652_, v___x_642_, v_motive_653_, v___f_654_, v___x_657_);
v___x_659_ = lean_apply_2(v_inst_643_, lean_box(0), v___x_658_);
v___x_660_ = lean_apply_4(v_toBind_644_, lean_box(0), lean_box(0), v___x_659_, v___f_656_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_661_ = _args[0];
lean_object* v_matcherName_662_ = _args[1];
lean_object* v_params_663_ = _args[2];
lean_object* v_k_664_ = _args[3];
lean_object* v___x_665_ = _args[4];
lean_object* v_inst_666_ = _args[5];
lean_object* v_toBind_667_ = _args[6];
lean_object* v___f_668_ = _args[7];
lean_object* v_inst_669_ = _args[8];
lean_object* v_inst_670_ = _args[9];
lean_object* v_alts_671_ = _args[10];
lean_object* v_toPure_672_ = _args[11];
lean_object* v_matcherLevels_673_ = _args[12];
lean_object* v_resTy_674_ = _args[13];
lean_object* v___x_675_ = _args[14];
lean_object* v_motive_676_ = _args[15];
lean_object* v___f_677_ = _args[16];
lean_object* v_discrs_678_ = _args[17];
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(v_toMatcherInfo_661_, v_matcherName_662_, v_params_663_, v_k_664_, v___x_665_, v_inst_666_, v_toBind_667_, v___f_668_, v_inst_669_, v_inst_670_, v_alts_671_, v_toPure_672_, v_matcherLevels_673_, v_resTy_674_, v___x_675_, v_motive_676_, v___f_677_, v_discrs_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v___f_682_, lean_object* v_discrNamesTypes_683_){
_start:
{
uint8_t v___x_684_; lean_object* v___x_685_; 
v___x_684_ = 0;
v___x_685_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_680_, v_inst_681_, v_discrNamesTypes_683_, v___f_682_, v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0(void){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_688_ = l_ReaderT_instMonad___redArg(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(0u);
v___x_697_ = l_Lean_Level_ofNat(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8);
v___x_699_ = l_Lean_mkSort(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_info_704_, lean_object* v_resTy_705_, lean_object* v_k_706_){
_start:
{
lean_object* v___x_707_; lean_object* v_toApplicative_708_; lean_object* v_toFunctor_709_; lean_object* v_toSeq_710_; lean_object* v_toSeqLeft_711_; lean_object* v_toSeqRight_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_819_; 
v___x_707_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc_ref(v_toApplicative_708_);
v_toFunctor_709_ = lean_ctor_get(v_toApplicative_708_, 0);
v_toSeq_710_ = lean_ctor_get(v_toApplicative_708_, 2);
v_toSeqLeft_711_ = lean_ctor_get(v_toApplicative_708_, 3);
v_toSeqRight_712_ = lean_ctor_get(v_toApplicative_708_, 4);
v_isSharedCheck_819_ = !lean_is_exclusive(v_toApplicative_708_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_toApplicative_708_, 1);
lean_dec(v_unused_820_);
v___x_714_ = v_toApplicative_708_;
v_isShared_715_ = v_isSharedCheck_819_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_toSeqRight_712_);
lean_inc(v_toSeqLeft_711_);
lean_inc(v_toSeq_710_);
lean_inc(v_toFunctor_709_);
lean_dec(v_toApplicative_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_819_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___x_725_; 
v___f_716_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_717_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref(v_toFunctor_709_);
v___f_718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_718_, 0, v_toFunctor_709_);
v___f_719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_719_, 0, v_toFunctor_709_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___f_718_);
lean_ctor_set(v___x_720_, 1, v___f_719_);
v___f_721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_721_, 0, v_toSeqRight_712_);
v___f_722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_722_, 0, v_toSeqLeft_711_);
v___f_723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_723_, 0, v_toSeq_710_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 4, v___f_721_);
lean_ctor_set(v___x_714_, 3, v___f_722_);
lean_ctor_set(v___x_714_, 2, v___f_723_);
lean_ctor_set(v___x_714_, 1, v___f_716_);
lean_ctor_set(v___x_714_, 0, v___x_720_);
v___x_725_ = v___x_714_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___f_716_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v___f_723_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v___f_722_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v___f_721_);
v___x_725_ = v_reuseFailAlloc_818_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v_toApplicative_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_816_; 
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___f_717_);
v___x_727_ = l_ReaderT_instMonad___redArg(v___x_726_);
v___x_728_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_728_, 0, lean_box(0));
lean_closure_set(v___x_728_, 1, lean_box(0));
lean_closure_set(v___x_728_, 2, v___x_727_);
v___x_729_ = l_instMonadControlTOfPure___redArg(v___x_728_);
v_toApplicative_730_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v___x_707_, 1);
lean_dec(v_unused_817_);
v___x_732_ = v___x_707_;
v_isShared_733_ = v_isSharedCheck_816_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_toApplicative_730_);
lean_dec(v___x_707_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_816_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_toFunctor_734_; lean_object* v_toSeq_735_; lean_object* v_toSeqLeft_736_; lean_object* v_toSeqRight_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_814_; 
v_toFunctor_734_ = lean_ctor_get(v_toApplicative_730_, 0);
v_toSeq_735_ = lean_ctor_get(v_toApplicative_730_, 2);
v_toSeqLeft_736_ = lean_ctor_get(v_toApplicative_730_, 3);
v_toSeqRight_737_ = lean_ctor_get(v_toApplicative_730_, 4);
v_isSharedCheck_814_ = !lean_is_exclusive(v_toApplicative_730_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_toApplicative_730_, 1);
lean_dec(v_unused_815_);
v___x_739_ = v_toApplicative_730_;
v_isShared_740_ = v_isSharedCheck_814_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_toSeqRight_737_);
lean_inc(v_toSeqLeft_736_);
lean_inc(v_toSeq_735_);
lean_inc(v_toFunctor_734_);
lean_dec(v_toApplicative_730_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_814_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___x_748_; 
lean_inc_ref(v_toFunctor_734_);
v___f_741_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_741_, 0, v_toFunctor_734_);
v___f_742_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_742_, 0, v_toFunctor_734_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___f_741_);
lean_ctor_set(v___x_743_, 1, v___f_742_);
v___f_744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_744_, 0, v_toSeqRight_737_);
v___f_745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_745_, 0, v_toSeqLeft_736_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_746_, 0, v_toSeq_735_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 4, v___f_744_);
lean_ctor_set(v___x_739_, 3, v___f_745_);
lean_ctor_set(v___x_739_, 2, v___f_746_);
lean_ctor_set(v___x_739_, 1, v___f_716_);
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_748_ = v___x_739_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___f_716_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v___f_746_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v___f_745_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v___f_744_);
v___x_748_ = v_reuseFailAlloc_813_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___f_717_);
lean_ctor_set(v___x_732_, 0, v___x_748_);
v___x_750_ = v___x_732_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___f_717_);
v___x_750_ = v_reuseFailAlloc_812_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v_toApplicative_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_810_; 
v___x_751_ = l_ReaderT_instMonad___redArg(v___x_750_);
v_toApplicative_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_751_, 1);
lean_dec(v_unused_811_);
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_810_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_toApplicative_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_810_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v_toFunctor_756_; lean_object* v_toSeq_757_; lean_object* v_toSeqLeft_758_; lean_object* v_toSeqRight_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_808_; 
v_toFunctor_756_ = lean_ctor_get(v_toApplicative_752_, 0);
v_toSeq_757_ = lean_ctor_get(v_toApplicative_752_, 2);
v_toSeqLeft_758_ = lean_ctor_get(v_toApplicative_752_, 3);
v_toSeqRight_759_ = lean_ctor_get(v_toApplicative_752_, 4);
v_isSharedCheck_808_ = !lean_is_exclusive(v_toApplicative_752_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_toApplicative_752_, 1);
lean_dec(v_unused_809_);
v___x_761_ = v_toApplicative_752_;
v_isShared_762_ = v_isSharedCheck_808_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_toSeqRight_759_);
lean_inc(v_toSeqLeft_758_);
lean_inc(v_toSeq_757_);
lean_inc(v_toFunctor_756_);
lean_dec(v_toApplicative_752_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_808_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___x_772_; 
v___f_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_764_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_756_);
v___f_765_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_765_, 0, v_toFunctor_756_);
v___f_766_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_766_, 0, v_toFunctor_756_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___f_765_);
lean_ctor_set(v___x_767_, 1, v___f_766_);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_768_, 0, v_toSeqRight_759_);
v___f_769_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_769_, 0, v_toSeqLeft_758_);
v___f_770_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_770_, 0, v_toSeq_757_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 4, v___f_768_);
lean_ctor_set(v___x_761_, 3, v___f_769_);
lean_ctor_set(v___x_761_, 2, v___f_770_);
lean_ctor_set(v___x_761_, 1, v___f_763_);
lean_ctor_set(v___x_761_, 0, v___x_767_);
v___x_772_ = v___x_761_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___f_763_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v___f_770_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v___f_769_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v___f_768_);
v___x_772_ = v_reuseFailAlloc_807_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v___f_764_);
lean_ctor_set(v___x_754_, 0, v___x_772_);
v___x_774_ = v___x_754_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___f_764_);
v___x_774_ = v_reuseFailAlloc_806_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
switch(lean_obj_tag(v_info_704_))
{
case 0:
{
lean_object* v_toBind_775_; lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref(v_info_704_);
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_729_);
v_toBind_775_ = lean_ctor_get(v_inst_703_, 1);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
lean_inc(v_toBind_775_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_776_, 0, v_resTy_705_);
lean_closure_set(v___f_776_, 1, v_k_706_);
lean_closure_set(v___f_776_, 2, v_inst_701_);
lean_closure_set(v___f_776_, 3, v_toBind_775_);
lean_closure_set(v___f_776_, 4, v_inst_702_);
lean_closure_set(v___f_776_, 5, v_inst_703_);
v___x_777_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_778_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_779_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_702_, v_inst_703_, v___x_777_, v___x_778_, v___f_776_);
return v___x_779_;
}
case 1:
{
lean_object* v_toBind_780_; lean_object* v___f_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v_info_704_);
lean_dec_ref(v___x_774_);
lean_dec_ref(v___x_729_);
v_toBind_780_ = lean_ctor_get(v_inst_703_, 1);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
lean_inc(v_toBind_780_);
v___f_781_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_781_, 0, v_resTy_705_);
lean_closure_set(v___f_781_, 1, v_k_706_);
lean_closure_set(v___f_781_, 2, v_inst_701_);
lean_closure_set(v___f_781_, 3, v_toBind_780_);
lean_closure_set(v___f_781_, 4, v_inst_702_);
lean_closure_set(v___f_781_, 5, v_inst_703_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_783_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_784_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_702_, v_inst_703_, v___x_782_, v___x_783_, v___f_781_);
return v___x_784_;
}
default: 
{
lean_object* v_toApplicative_785_; lean_object* v_matcherApp_786_; lean_object* v_toBind_787_; lean_object* v_toPure_788_; lean_object* v_toMatcherInfo_789_; lean_object* v_matcherName_790_; lean_object* v_matcherLevels_791_; lean_object* v_params_792_; lean_object* v_motive_793_; lean_object* v_discrs_794_; lean_object* v_alts_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_toApplicative_785_ = lean_ctor_get(v_inst_703_, 0);
v_matcherApp_786_ = lean_ctor_get(v_info_704_, 0);
lean_inc_ref(v_matcherApp_786_);
lean_dec_ref(v_info_704_);
v_toBind_787_ = lean_ctor_get(v_inst_703_, 1);
lean_inc(v_toBind_787_);
v_toPure_788_ = lean_ctor_get(v_toApplicative_785_, 1);
v_toMatcherInfo_789_ = lean_ctor_get(v_matcherApp_786_, 0);
lean_inc_ref(v_toMatcherInfo_789_);
v_matcherName_790_ = lean_ctor_get(v_matcherApp_786_, 1);
lean_inc(v_matcherName_790_);
v_matcherLevels_791_ = lean_ctor_get(v_matcherApp_786_, 2);
lean_inc_ref(v_matcherLevels_791_);
v_params_792_ = lean_ctor_get(v_matcherApp_786_, 3);
lean_inc_ref(v_params_792_);
v_motive_793_ = lean_ctor_get(v_matcherApp_786_, 4);
lean_inc_ref(v_motive_793_);
v_discrs_794_ = lean_ctor_get(v_matcherApp_786_, 5);
lean_inc_ref(v_discrs_794_);
v_alts_795_ = lean_ctor_get(v_matcherApp_786_, 6);
lean_inc_ref(v_alts_795_);
lean_dec_ref(v_matcherApp_786_);
lean_inc_ref(v_resTy_705_);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed), 8, 1);
lean_closure_set(v___f_796_, 0, v_resTy_705_);
v___f_797_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
lean_inc(v_toBind_787_);
lean_inc(v_inst_701_);
lean_inc(v_toPure_788_);
v___f_798_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17), 6, 3);
lean_closure_set(v___f_798_, 0, v_toPure_788_);
lean_closure_set(v___f_798_, 1, v_inst_701_);
lean_closure_set(v___f_798_, 2, v_toBind_787_);
lean_inc(v_toPure_788_);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
lean_inc(v_toBind_787_);
v___f_799_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___boxed), 18, 17);
lean_closure_set(v___f_799_, 0, v_toMatcherInfo_789_);
lean_closure_set(v___f_799_, 1, v_matcherName_790_);
lean_closure_set(v___f_799_, 2, v_params_792_);
lean_closure_set(v___f_799_, 3, v_k_706_);
lean_closure_set(v___f_799_, 4, v___x_774_);
lean_closure_set(v___f_799_, 5, v_inst_701_);
lean_closure_set(v___f_799_, 6, v_toBind_787_);
lean_closure_set(v___f_799_, 7, v___f_797_);
lean_closure_set(v___f_799_, 8, v_inst_702_);
lean_closure_set(v___f_799_, 9, v_inst_703_);
lean_closure_set(v___f_799_, 10, v_alts_795_);
lean_closure_set(v___f_799_, 11, v_toPure_788_);
lean_closure_set(v___f_799_, 12, v_matcherLevels_791_);
lean_closure_set(v___f_799_, 13, v_resTy_705_);
lean_closure_set(v___f_799_, 14, v___x_729_);
lean_closure_set(v___f_799_, 15, v_motive_793_);
lean_closure_set(v___f_799_, 16, v___f_796_);
lean_inc_ref(v_inst_703_);
v___f_800_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26), 4, 3);
lean_closure_set(v___f_800_, 0, v_inst_702_);
lean_closure_set(v___f_800_, 1, v_inst_703_);
lean_closure_set(v___f_800_, 2, v___f_799_);
v___x_801_ = lean_array_get_size(v_discrs_794_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_mk_empty_array_with_capacity(v___x_801_);
v___x_804_ = l_Array_mapFinIdxM_map___redArg(v_inst_703_, v_discrs_794_, v___f_798_, v___x_801_, v___x_802_, v___x_803_);
v___x_805_ = lean_apply_4(v_toBind_787_, lean_box(0), lean_box(0), v___x_804_, v___f_800_);
return v___x_805_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_821_, lean_object* v_00_u03b1_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_info_827_, lean_object* v_resTy_828_, lean_object* v_k_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_823_, v_inst_824_, v_inst_825_, v_info_827_, v_resTy_828_, v_k_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_831_, lean_object* v_00_u03b1_832_, lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_info_837_, lean_object* v_resTy_838_, lean_object* v_k_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_831_, v_00_u03b1_832_, v_inst_833_, v_inst_834_, v_inst_835_, v_inst_836_, v_info_837_, v_resTy_838_, v_k_839_);
lean_dec(v_inst_836_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_841_, lean_object* v_resTy_842_, lean_object* v_c_843_, lean_object* v_h_844_, lean_object* v_t_845_, lean_object* v_toPure_846_, lean_object* v_e_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_848_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_849_ = lean_box(0);
v___x_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_850_, 0, v_u_841_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_mkConst(v___x_848_, v___x_850_);
v___x_852_ = l_Lean_mkApp5(v___x_851_, v_resTy_842_, v_c_843_, v_h_844_, v_t_845_, v_e_847_);
v___x_853_ = lean_apply_2(v_toPure_846_, lean_box(0), v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_857_, lean_object* v_resTy_858_, lean_object* v_c_859_, lean_object* v_h_860_, lean_object* v_toPure_861_, lean_object* v_onAlt_862_, lean_object* v___x_863_, lean_object* v___x_864_, lean_object* v_toBind_865_, lean_object* v_t_866_){
_start:
{
lean_object* v___f_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
lean_inc_ref(v_resTy_858_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_867_, 0, v_u_857_);
lean_closure_set(v___f_867_, 1, v_resTy_858_);
lean_closure_set(v___f_867_, 2, v_c_859_);
lean_closure_set(v___f_867_, 3, v_h_860_);
lean_closure_set(v___f_867_, 4, v_t_866_);
lean_closure_set(v___f_867_, 5, v_toPure_861_);
v___x_868_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_869_ = lean_apply_4(v_onAlt_862_, v___x_868_, v_resTy_858_, v___x_863_, v___x_864_);
v___x_870_ = lean_apply_4(v_toBind_865_, lean_box(0), lean_box(0), v___x_869_, v___f_867_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_871_, uint8_t v_useSplitter_872_, lean_object* v_inst_873_, lean_object* v_____do__lift_874_){
_start:
{
uint8_t v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_875_ = 0;
v___x_876_ = 1;
v___x_877_ = lean_box(v___x_875_);
v___x_878_ = lean_box(v_useSplitter_872_);
v___x_879_ = lean_box(v___x_875_);
v___x_880_ = lean_box(v_useSplitter_872_);
v___x_881_ = lean_box(v___x_876_);
v___x_882_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_882_, 0, v___x_871_);
lean_closure_set(v___x_882_, 1, v_____do__lift_874_);
lean_closure_set(v___x_882_, 2, v___x_877_);
lean_closure_set(v___x_882_, 3, v___x_878_);
lean_closure_set(v___x_882_, 4, v___x_879_);
lean_closure_set(v___x_882_, 5, v___x_880_);
lean_closure_set(v___x_882_, 6, v___x_881_);
v___x_883_ = lean_apply_2(v_inst_873_, lean_box(0), v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_884_, lean_object* v_useSplitter_885_, lean_object* v_inst_886_, lean_object* v_____do__lift_887_){
_start:
{
uint8_t v_useSplitter_boxed_888_; lean_object* v_res_889_; 
v_useSplitter_boxed_888_ = lean_unbox(v_useSplitter_885_);
v_res_889_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_884_, v_useSplitter_boxed_888_, v_inst_886_, v_____do__lift_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_893_, uint8_t v_useSplitter_894_, lean_object* v_inst_895_, lean_object* v_onAlt_896_, lean_object* v_resTy_897_, lean_object* v_toBind_898_, lean_object* v_h_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_900_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
v___x_903_ = lean_mk_empty_array_with_capacity(v___x_893_);
v___x_904_ = lean_array_push(v___x_903_, v_h_899_);
v___x_905_ = lean_box(v_useSplitter_894_);
lean_inc_ref(v___x_904_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_906_, 0, v___x_904_);
lean_closure_set(v___f_906_, 1, v___x_905_);
lean_closure_set(v___f_906_, 2, v_inst_895_);
v___x_907_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_907_, 0, v___x_902_);
lean_ctor_set(v___x_907_, 1, v___x_904_);
lean_ctor_set(v___x_907_, 2, v___x_902_);
lean_ctor_set(v___x_907_, 3, v___x_902_);
lean_ctor_set(v___x_907_, 4, v___x_902_);
v___x_908_ = lean_apply_4(v_onAlt_896_, v___x_900_, v_resTy_897_, v___x_901_, v___x_907_);
v___x_909_ = lean_apply_4(v_toBind_898_, lean_box(0), lean_box(0), v___x_908_, v___f_906_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_910_, lean_object* v_useSplitter_911_, lean_object* v_inst_912_, lean_object* v_onAlt_913_, lean_object* v_resTy_914_, lean_object* v_toBind_915_, lean_object* v_h_916_){
_start:
{
uint8_t v_useSplitter_boxed_917_; lean_object* v_res_918_; 
v_useSplitter_boxed_917_ = lean_unbox(v_useSplitter_911_);
v_res_918_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_910_, v_useSplitter_boxed_917_, v_inst_912_, v_onAlt_913_, v_resTy_914_, v_toBind_915_, v_h_916_);
lean_dec(v___x_910_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_919_, uint8_t v_useSplitter_920_, lean_object* v_inst_921_, lean_object* v_onAlt_922_, lean_object* v_resTy_923_, lean_object* v_toBind_924_, lean_object* v_h_925_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_926_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_927_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
v___x_928_ = lean_mk_empty_array_with_capacity(v___x_919_);
v___x_929_ = lean_array_push(v___x_928_, v_h_925_);
v___x_930_ = lean_box(v_useSplitter_920_);
lean_inc_ref(v___x_929_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_931_, 0, v___x_929_);
lean_closure_set(v___f_931_, 1, v___x_930_);
lean_closure_set(v___f_931_, 2, v_inst_921_);
v___x_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_932_, 0, v___x_927_);
lean_ctor_set(v___x_932_, 1, v___x_929_);
lean_ctor_set(v___x_932_, 2, v___x_927_);
lean_ctor_set(v___x_932_, 3, v___x_927_);
lean_ctor_set(v___x_932_, 4, v___x_927_);
v___x_933_ = lean_apply_4(v_onAlt_922_, v___x_926_, v_resTy_923_, v___x_919_, v___x_932_);
v___x_934_ = lean_apply_4(v_toBind_924_, lean_box(0), lean_box(0), v___x_933_, v___f_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_935_, lean_object* v_useSplitter_936_, lean_object* v_inst_937_, lean_object* v_onAlt_938_, lean_object* v_resTy_939_, lean_object* v_toBind_940_, lean_object* v_h_941_){
_start:
{
uint8_t v_useSplitter_boxed_942_; lean_object* v_res_943_; 
v_useSplitter_boxed_942_ = lean_unbox(v_useSplitter_936_);
v_res_943_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_935_, v_useSplitter_boxed_942_, v_inst_937_, v_onAlt_938_, v_resTy_939_, v_toBind_940_, v_h_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_944_, lean_object* v_resTy_945_, lean_object* v_c_946_, lean_object* v_h_947_, lean_object* v_t_948_, lean_object* v_toPure_949_, lean_object* v_e_950_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_951_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_953_, 0, v_u_944_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = l_Lean_mkConst(v___x_951_, v___x_953_);
v___x_955_ = l_Lean_mkApp5(v___x_954_, v_resTy_945_, v_c_946_, v_h_947_, v_t_948_, v_e_950_);
v___x_956_ = lean_apply_2(v_toPure_949_, lean_box(0), v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_957_, lean_object* v_resTy_958_, lean_object* v_c_959_, lean_object* v_h_960_, lean_object* v_toPure_961_, lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_n_964_, uint8_t v___x_965_, lean_object* v___f_966_, uint8_t v___x_967_, lean_object* v_toBind_968_, lean_object* v_t_969_){
_start:
{
lean_object* v___f_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_inc_ref(v_c_959_);
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_970_, 0, v_u_957_);
lean_closure_set(v___f_970_, 1, v_resTy_958_);
lean_closure_set(v___f_970_, 2, v_c_959_);
lean_closure_set(v___f_970_, 3, v_h_960_);
lean_closure_set(v___f_970_, 4, v_t_969_);
lean_closure_set(v___f_970_, 5, v_toPure_961_);
v___x_971_ = l_Lean_mkNot(v_c_959_);
v___x_972_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_962_, v_inst_963_, v_n_964_, v___x_965_, v___x_971_, v___f_966_, v___x_967_);
v___x_973_ = lean_apply_4(v_toBind_968_, lean_box(0), lean_box(0), v___x_972_, v___f_970_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_974_, lean_object* v_resTy_975_, lean_object* v_c_976_, lean_object* v_h_977_, lean_object* v_toPure_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_n_981_, lean_object* v___x_982_, lean_object* v___f_983_, lean_object* v___x_984_, lean_object* v_toBind_985_, lean_object* v_t_986_){
_start:
{
uint8_t v___x_1249__boxed_987_; uint8_t v___x_1251__boxed_988_; lean_object* v_res_989_; 
v___x_1249__boxed_987_ = lean_unbox(v___x_982_);
v___x_1251__boxed_988_ = lean_unbox(v___x_984_);
v_res_989_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_974_, v_resTy_975_, v_c_976_, v_h_977_, v_toPure_978_, v_inst_979_, v_inst_980_, v_n_981_, v___x_1249__boxed_987_, v___f_983_, v___x_1251__boxed_988_, v_toBind_985_, v_t_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_990_, lean_object* v_resTy_991_, lean_object* v_c_992_, lean_object* v_h_993_, lean_object* v_toPure_994_, lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v___f_997_, lean_object* v_toBind_998_, lean_object* v___f_999_, lean_object* v_n_1000_){
_start:
{
uint8_t v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1001_ = 0;
v___x_1002_ = 0;
v___x_1003_ = lean_box(v___x_1001_);
v___x_1004_ = lean_box(v___x_1002_);
lean_inc(v_toBind_998_);
lean_inc(v_n_1000_);
lean_inc_ref(v_inst_996_);
lean_inc_ref(v_inst_995_);
lean_inc_ref(v_c_992_);
v___f_1005_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1005_, 0, v_u_990_);
lean_closure_set(v___f_1005_, 1, v_resTy_991_);
lean_closure_set(v___f_1005_, 2, v_c_992_);
lean_closure_set(v___f_1005_, 3, v_h_993_);
lean_closure_set(v___f_1005_, 4, v_toPure_994_);
lean_closure_set(v___f_1005_, 5, v_inst_995_);
lean_closure_set(v___f_1005_, 6, v_inst_996_);
lean_closure_set(v___f_1005_, 7, v_n_1000_);
lean_closure_set(v___f_1005_, 8, v___x_1003_);
lean_closure_set(v___f_1005_, 9, v___f_997_);
lean_closure_set(v___f_1005_, 10, v___x_1004_);
lean_closure_set(v___f_1005_, 11, v_toBind_998_);
v___x_1006_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_995_, v_inst_996_, v_n_1000_, v___x_1001_, v_c_992_, v___f_999_, v___x_1002_);
v___x_1007_ = lean_apply_4(v_toBind_998_, lean_box(0), lean_box(0), v___x_1006_, v___f_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Core_mkFreshUserName(v___x_1008_, v___y_1011_, v___y_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1021_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
v___x_1023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
lean_ctor_set(v___x_1023_, 2, v___x_1022_);
lean_ctor_set(v___x_1023_, 3, v___x_1022_);
lean_ctor_set(v___x_1023_, 4, v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1029_, uint8_t v_useSplitter_1030_, lean_object* v_resTy_1031_, lean_object* v_toPure_1032_, lean_object* v_onAlt_1033_, lean_object* v_toBind_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_u_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_c_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_h_1047_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = l_Lean_Expr_getAppNumArgs(v_e_1029_);
v___x_1041_ = lean_nat_sub(v___x_1040_, v___x_1039_);
v___x_1042_ = lean_nat_sub(v___x_1041_, v___x_1039_);
lean_dec(v___x_1041_);
v_c_1043_ = l_Lean_Expr_getRevArg_x21(v_e_1029_, v___x_1042_);
v___x_1044_ = lean_unsigned_to_nat(2u);
v___x_1045_ = lean_nat_sub(v___x_1040_, v___x_1044_);
lean_dec(v___x_1040_);
v___x_1046_ = lean_nat_sub(v___x_1045_, v___x_1039_);
lean_dec(v___x_1045_);
v_h_1047_ = l_Lean_Expr_getRevArg_x21(v_e_1029_, v___x_1046_);
if (v_useSplitter_1030_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_dec_ref(v_inst_1037_);
lean_dec_ref(v_inst_1036_);
lean_dec(v_inst_1035_);
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0);
lean_inc(v_toBind_1034_);
lean_inc(v_onAlt_1033_);
lean_inc_ref(v_resTy_1031_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1051_, 0, v_u_1038_);
lean_closure_set(v___f_1051_, 1, v_resTy_1031_);
lean_closure_set(v___f_1051_, 2, v_c_1043_);
lean_closure_set(v___f_1051_, 3, v_h_1047_);
lean_closure_set(v___f_1051_, 4, v_toPure_1032_);
lean_closure_set(v___f_1051_, 5, v_onAlt_1033_);
lean_closure_set(v___f_1051_, 6, v___x_1039_);
lean_closure_set(v___f_1051_, 7, v___x_1050_);
lean_closure_set(v___f_1051_, 8, v_toBind_1034_);
v___x_1052_ = lean_apply_4(v_onAlt_1033_, v___x_1048_, v_resTy_1031_, v___x_1049_, v___x_1050_);
v___x_1053_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v___x_1052_, v___f_1051_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1054_ = lean_box(v_useSplitter_1030_);
lean_inc(v_toBind_1034_);
lean_inc_ref(v_resTy_1031_);
lean_inc(v_onAlt_1033_);
lean_inc(v_inst_1035_);
v___f_1055_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1055_, 0, v___x_1039_);
lean_closure_set(v___f_1055_, 1, v___x_1054_);
lean_closure_set(v___f_1055_, 2, v_inst_1035_);
lean_closure_set(v___f_1055_, 3, v_onAlt_1033_);
lean_closure_set(v___f_1055_, 4, v_resTy_1031_);
lean_closure_set(v___f_1055_, 5, v_toBind_1034_);
v___x_1056_ = lean_box(v_useSplitter_1030_);
lean_inc(v_toBind_1034_);
lean_inc_ref(v_resTy_1031_);
lean_inc(v_inst_1035_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1057_, 0, v___x_1039_);
lean_closure_set(v___f_1057_, 1, v___x_1056_);
lean_closure_set(v___f_1057_, 2, v_inst_1035_);
lean_closure_set(v___f_1057_, 3, v_onAlt_1033_);
lean_closure_set(v___f_1057_, 4, v_resTy_1031_);
lean_closure_set(v___f_1057_, 5, v_toBind_1034_);
lean_inc(v_toBind_1034_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1058_, 0, v_u_1038_);
lean_closure_set(v___f_1058_, 1, v_resTy_1031_);
lean_closure_set(v___f_1058_, 2, v_c_1043_);
lean_closure_set(v___f_1058_, 3, v_h_1047_);
lean_closure_set(v___f_1058_, 4, v_toPure_1032_);
lean_closure_set(v___f_1058_, 5, v_inst_1036_);
lean_closure_set(v___f_1058_, 6, v_inst_1037_);
lean_closure_set(v___f_1058_, 7, v___f_1057_);
lean_closure_set(v___f_1058_, 8, v_toBind_1034_);
lean_closure_set(v___f_1058_, 9, v___f_1055_);
v___f_1059_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1060_ = lean_apply_2(v_inst_1035_, lean_box(0), v___f_1059_);
v___x_1061_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v___x_1060_, v___f_1058_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1062_, lean_object* v_useSplitter_1063_, lean_object* v_resTy_1064_, lean_object* v_toPure_1065_, lean_object* v_onAlt_1066_, lean_object* v_toBind_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_u_1071_){
_start:
{
uint8_t v_useSplitter_boxed_1072_; lean_object* v_res_1073_; 
v_useSplitter_boxed_1072_ = lean_unbox(v_useSplitter_1063_);
v_res_1073_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1062_, v_useSplitter_boxed_1072_, v_resTy_1064_, v_toPure_1065_, v_onAlt_1066_, v_toBind_1067_, v_inst_1068_, v_inst_1069_, v_inst_1070_, v_u_1071_);
lean_dec_ref(v_e_1062_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1074_, lean_object* v_inst_1075_, lean_object* v_____do__lift_1076_){
_start:
{
uint8_t v___x_1077_; uint8_t v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1077_ = 0;
v___x_1078_ = 1;
v___x_1079_ = 1;
v___x_1080_ = lean_box(v___x_1077_);
v___x_1081_ = lean_box(v___x_1078_);
v___x_1082_ = lean_box(v___x_1077_);
v___x_1083_ = lean_box(v___x_1078_);
v___x_1084_ = lean_box(v___x_1079_);
v___x_1085_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1085_, 0, v___x_1074_);
lean_closure_set(v___x_1085_, 1, v_____do__lift_1076_);
lean_closure_set(v___x_1085_, 2, v___x_1080_);
lean_closure_set(v___x_1085_, 3, v___x_1081_);
lean_closure_set(v___x_1085_, 4, v___x_1082_);
lean_closure_set(v___x_1085_, 5, v___x_1083_);
lean_closure_set(v___x_1085_, 6, v___x_1084_);
v___x_1086_ = lean_apply_2(v_inst_1075_, lean_box(0), v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1087_, lean_object* v_onAlt_1088_, lean_object* v_resTy_1089_, lean_object* v_toBind_1090_, lean_object* v_h_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1092_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_mk_empty_array_with_capacity(v___x_1094_);
v___x_1096_ = lean_array_push(v___x_1095_, v_h_1091_);
lean_inc_ref(v___x_1096_);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1097_, 0, v___x_1096_);
lean_closure_set(v___f_1097_, 1, v_inst_1087_);
v___x_1098_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
lean_inc_ref(v___x_1096_);
v___x_1099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1096_);
lean_ctor_set(v___x_1099_, 1, v___x_1096_);
lean_ctor_set(v___x_1099_, 2, v___x_1098_);
lean_ctor_set(v___x_1099_, 3, v___x_1098_);
lean_ctor_set(v___x_1099_, 4, v___x_1098_);
v___x_1100_ = lean_apply_4(v_onAlt_1088_, v___x_1092_, v_resTy_1089_, v___x_1093_, v___x_1099_);
v___x_1101_ = lean_apply_4(v_toBind_1090_, lean_box(0), lean_box(0), v___x_1100_, v___f_1097_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1102_, lean_object* v_inst_1103_, lean_object* v_onAlt_1104_, lean_object* v_resTy_1105_, lean_object* v_toBind_1106_, lean_object* v_h_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1108_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1109_ = lean_mk_empty_array_with_capacity(v___x_1102_);
v___x_1110_ = lean_array_push(v___x_1109_, v_h_1107_);
lean_inc_ref(v___x_1110_);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1111_, 0, v___x_1110_);
lean_closure_set(v___f_1111_, 1, v_inst_1103_);
v___x_1112_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
lean_inc_ref(v___x_1110_);
v___x_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1110_);
lean_ctor_set(v___x_1113_, 1, v___x_1110_);
lean_ctor_set(v___x_1113_, 2, v___x_1112_);
lean_ctor_set(v___x_1113_, 3, v___x_1112_);
lean_ctor_set(v___x_1113_, 4, v___x_1112_);
v___x_1114_ = lean_apply_4(v_onAlt_1104_, v___x_1108_, v_resTy_1105_, v___x_1102_, v___x_1113_);
v___x_1115_ = lean_apply_4(v_toBind_1106_, lean_box(0), lean_box(0), v___x_1114_, v___f_1111_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1116_, lean_object* v_onAlt_1117_, lean_object* v_resTy_1118_, lean_object* v_toBind_1119_, lean_object* v_e_1120_, lean_object* v_toPure_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v___f_1124_, lean_object* v_u_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___f_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_c_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_h_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1126_ = lean_unsigned_to_nat(1u);
lean_inc(v_toBind_1119_);
lean_inc_ref(v_resTy_1118_);
lean_inc(v_inst_1116_);
v___f_1127_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1127_, 0, v___x_1126_);
lean_closure_set(v___f_1127_, 1, v_inst_1116_);
lean_closure_set(v___f_1127_, 2, v_onAlt_1117_);
lean_closure_set(v___f_1127_, 3, v_resTy_1118_);
lean_closure_set(v___f_1127_, 4, v_toBind_1119_);
v___x_1128_ = l_Lean_Expr_getAppNumArgs(v_e_1120_);
v___x_1129_ = lean_nat_sub(v___x_1128_, v___x_1126_);
v___x_1130_ = lean_nat_sub(v___x_1129_, v___x_1126_);
lean_dec(v___x_1129_);
v_c_1131_ = l_Lean_Expr_getRevArg_x21(v_e_1120_, v___x_1130_);
v___x_1132_ = lean_unsigned_to_nat(2u);
v___x_1133_ = lean_nat_sub(v___x_1128_, v___x_1132_);
lean_dec(v___x_1128_);
v___x_1134_ = lean_nat_sub(v___x_1133_, v___x_1126_);
lean_dec(v___x_1133_);
v_h_1135_ = l_Lean_Expr_getRevArg_x21(v_e_1120_, v___x_1134_);
lean_inc(v_toBind_1119_);
v___f_1136_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1136_, 0, v_u_1125_);
lean_closure_set(v___f_1136_, 1, v_resTy_1118_);
lean_closure_set(v___f_1136_, 2, v_c_1131_);
lean_closure_set(v___f_1136_, 3, v_h_1135_);
lean_closure_set(v___f_1136_, 4, v_toPure_1121_);
lean_closure_set(v___f_1136_, 5, v_inst_1122_);
lean_closure_set(v___f_1136_, 6, v_inst_1123_);
lean_closure_set(v___f_1136_, 7, v___f_1127_);
lean_closure_set(v___f_1136_, 8, v_toBind_1119_);
lean_closure_set(v___f_1136_, 9, v___f_1124_);
v___f_1137_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1138_ = lean_apply_2(v_inst_1116_, lean_box(0), v___f_1137_);
v___x_1139_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1138_, v___f_1136_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1140_, lean_object* v_onAlt_1141_, lean_object* v_resTy_1142_, lean_object* v_toBind_1143_, lean_object* v_e_1144_, lean_object* v_toPure_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v___f_1148_, lean_object* v_u_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1140_, v_onAlt_1141_, v_resTy_1142_, v_toBind_1143_, v_e_1144_, v_toPure_1145_, v_inst_1146_, v_inst_1147_, v___f_1148_, v_u_1149_);
lean_dec_ref(v_e_1144_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_onAlt_1151_, lean_object* v_idx_1152_, lean_object* v_expAltType_1153_, lean_object* v_altFVars_1154_, lean_object* v___alt_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_nat_add(v_idx_1152_, v___x_1157_);
v___x_1159_ = lean_name_append_index_after(v___x_1156_, v___x_1158_);
v___x_1160_ = lean_apply_4(v_onAlt_1151_, v___x_1159_, v_expAltType_1153_, v_idx_1152_, v_altFVars_1154_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(lean_object* v_onAlt_1161_, lean_object* v_idx_1162_, lean_object* v_expAltType_1163_, lean_object* v_altFVars_1164_, lean_object* v___alt_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(v_onAlt_1161_, v_idx_1162_, v_expAltType_1163_, v_altFVars_1164_, v___alt_1165_);
lean_dec_ref(v___alt_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_mask_1167_, lean_object* v_absMotiveBody_1168_, lean_object* v_toPure_1169_, lean_object* v_xs_1170_, lean_object* v___body_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = l_Array_mask___redArg(v_mask_1167_, v_xs_1170_);
v___x_1173_ = lean_expr_instantiate_rev(v_absMotiveBody_1168_, v___x_1172_);
lean_dec(v___x_1172_);
v___x_1174_ = lean_apply_2(v_toPure_1169_, lean_box(0), v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(lean_object* v_mask_1175_, lean_object* v_absMotiveBody_1176_, lean_object* v_toPure_1177_, lean_object* v_xs_1178_, lean_object* v___body_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(v_mask_1175_, v_absMotiveBody_1176_, v_toPure_1177_, v_xs_1178_, v___body_1179_);
lean_dec_ref(v___body_1179_);
lean_dec_ref(v_absMotiveBody_1176_);
lean_dec_ref(v_mask_1175_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v_toFunctor_1181_, lean_object* v_mask_1182_, lean_object* v_toPure_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_matcherApp_1189_, uint8_t v_useSplitter_1190_, lean_object* v___f_1191_, lean_object* v___f_1192_, lean_object* v_absMotiveBody_1193_){
_start:
{
lean_object* v_map_1194_; lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_map_1194_ = lean_ctor_get(v_toFunctor_1181_, 0);
lean_inc(v_map_1194_);
lean_dec_ref(v_toFunctor_1181_);
lean_inc(v_toPure_1183_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_1195_, 0, v_mask_1182_);
lean_closure_set(v___f_1195_, 1, v_absMotiveBody_1193_);
lean_closure_set(v___f_1195_, 2, v_toPure_1183_);
v___x_1196_ = lean_apply_1(v_toPure_1183_, lean_box(0));
lean_inc(v___x_1196_);
v___x_1197_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1184_, v_inst_1185_, v_inst_1186_, v_inst_1187_, v_inst_1188_, v_matcherApp_1189_, v_useSplitter_1190_, v_useSplitter_1190_, v___x_1196_, v___f_1195_, v___f_1191_, v___x_1196_);
v___x_1198_ = lean_apply_4(v_map_1194_, lean_box(0), lean_box(0), v___f_1192_, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v_toFunctor_1199_, lean_object* v_mask_1200_, lean_object* v_toPure_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_matcherApp_1207_, lean_object* v_useSplitter_1208_, lean_object* v___f_1209_, lean_object* v___f_1210_, lean_object* v_absMotiveBody_1211_){
_start:
{
uint8_t v_useSplitter_boxed_1212_; lean_object* v_res_1213_; 
v_useSplitter_boxed_1212_ = lean_unbox(v_useSplitter_1208_);
v_res_1213_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v_toFunctor_1199_, v_mask_1200_, v_toPure_1201_, v_inst_1202_, v_inst_1203_, v_inst_1204_, v_inst_1205_, v_inst_1206_, v_matcherApp_1207_, v_useSplitter_boxed_1212_, v___f_1209_, v___f_1210_, v_absMotiveBody_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_info_1221_, lean_object* v_resTy_1222_, lean_object* v_onAlt_1223_, uint8_t v_useSplitter_1224_){
_start:
{
switch(lean_obj_tag(v_info_1221_))
{
case 0:
{
lean_object* v_toApplicative_1225_; lean_object* v_toBind_1226_; lean_object* v_toPure_1227_; lean_object* v_e_1228_; lean_object* v___x_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_toApplicative_1225_ = lean_ctor_get(v_inst_1218_, 0);
lean_dec_ref(v_inst_1220_);
lean_dec_ref(v_inst_1219_);
v_toBind_1226_ = lean_ctor_get(v_inst_1218_, 1);
lean_inc(v_toBind_1226_);
v_toPure_1227_ = lean_ctor_get(v_toApplicative_1225_, 1);
lean_inc(v_toPure_1227_);
v_e_1228_ = lean_ctor_get(v_info_1221_, 0);
lean_inc_ref(v_e_1228_);
lean_dec_ref(v_info_1221_);
v___x_1229_ = lean_box(v_useSplitter_1224_);
lean_inc(v_inst_1216_);
lean_inc(v_toBind_1226_);
lean_inc_ref(v_resTy_1222_);
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1230_, 0, v_e_1228_);
lean_closure_set(v___f_1230_, 1, v___x_1229_);
lean_closure_set(v___f_1230_, 2, v_resTy_1222_);
lean_closure_set(v___f_1230_, 3, v_toPure_1227_);
lean_closure_set(v___f_1230_, 4, v_onAlt_1223_);
lean_closure_set(v___f_1230_, 5, v_toBind_1226_);
lean_closure_set(v___f_1230_, 6, v_inst_1216_);
lean_closure_set(v___f_1230_, 7, v_inst_1217_);
lean_closure_set(v___f_1230_, 8, v_inst_1218_);
v___x_1231_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1231_, 0, v_resTy_1222_);
v___x_1232_ = lean_apply_2(v_inst_1216_, lean_box(0), v___x_1231_);
v___x_1233_ = lean_apply_4(v_toBind_1226_, lean_box(0), lean_box(0), v___x_1232_, v___f_1230_);
return v___x_1233_;
}
case 1:
{
lean_object* v_toApplicative_1234_; lean_object* v_toBind_1235_; lean_object* v_toPure_1236_; lean_object* v_e_1237_; lean_object* v___f_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_toApplicative_1234_ = lean_ctor_get(v_inst_1218_, 0);
lean_dec_ref(v_inst_1220_);
lean_dec_ref(v_inst_1219_);
v_toBind_1235_ = lean_ctor_get(v_inst_1218_, 1);
lean_inc(v_toBind_1235_);
v_toPure_1236_ = lean_ctor_get(v_toApplicative_1234_, 1);
lean_inc(v_toPure_1236_);
v_e_1237_ = lean_ctor_get(v_info_1221_, 0);
lean_inc_ref(v_e_1237_);
lean_dec_ref(v_info_1221_);
lean_inc(v_toBind_1235_);
lean_inc_ref(v_resTy_1222_);
lean_inc(v_onAlt_1223_);
lean_inc(v_inst_1216_);
v___f_1238_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1238_, 0, v_inst_1216_);
lean_closure_set(v___f_1238_, 1, v_onAlt_1223_);
lean_closure_set(v___f_1238_, 2, v_resTy_1222_);
lean_closure_set(v___f_1238_, 3, v_toBind_1235_);
lean_inc(v_toBind_1235_);
lean_inc_ref(v_resTy_1222_);
lean_inc(v_inst_1216_);
v___f_1239_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1239_, 0, v_inst_1216_);
lean_closure_set(v___f_1239_, 1, v_onAlt_1223_);
lean_closure_set(v___f_1239_, 2, v_resTy_1222_);
lean_closure_set(v___f_1239_, 3, v_toBind_1235_);
lean_closure_set(v___f_1239_, 4, v_e_1237_);
lean_closure_set(v___f_1239_, 5, v_toPure_1236_);
lean_closure_set(v___f_1239_, 6, v_inst_1217_);
lean_closure_set(v___f_1239_, 7, v_inst_1218_);
lean_closure_set(v___f_1239_, 8, v___f_1238_);
v___x_1240_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1240_, 0, v_resTy_1222_);
v___x_1241_ = lean_apply_2(v_inst_1216_, lean_box(0), v___x_1240_);
v___x_1242_ = lean_apply_4(v_toBind_1235_, lean_box(0), lean_box(0), v___x_1241_, v___f_1239_);
return v___x_1242_;
}
default: 
{
lean_object* v_toApplicative_1243_; lean_object* v_matcherApp_1244_; lean_object* v_toBind_1245_; lean_object* v_toFunctor_1246_; lean_object* v_toPure_1247_; lean_object* v_discrs_1248_; lean_object* v___f_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; lean_object* v___x_1252_; size_t v_sz_1253_; size_t v___x_1254_; lean_object* v_mask_1255_; lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v_maskedDiscrs_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v_toApplicative_1243_ = lean_ctor_get(v_inst_1218_, 0);
v_matcherApp_1244_ = lean_ctor_get(v_info_1221_, 0);
lean_inc_ref(v_matcherApp_1244_);
lean_dec_ref(v_info_1221_);
v_toBind_1245_ = lean_ctor_get(v_inst_1218_, 1);
lean_inc(v_toBind_1245_);
v_toFunctor_1246_ = lean_ctor_get(v_toApplicative_1243_, 0);
lean_inc_ref(v_toFunctor_1246_);
v_toPure_1247_ = lean_ctor_get(v_toApplicative_1243_, 1);
lean_inc(v_toPure_1247_);
v_discrs_1248_ = lean_ctor_get(v_matcherApp_1244_, 5);
lean_inc_ref(v_discrs_1248_);
v___f_1249_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed), 5, 1);
lean_closure_set(v___f_1250_, 0, v_onAlt_1223_);
v___f_1251_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1));
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9));
v_sz_1253_ = lean_array_size(v_discrs_1248_);
v___x_1254_ = ((size_t)0ULL);
lean_inc_ref(v_discrs_1248_);
v_mask_1255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1252_, v___f_1251_, v_sz_1253_, v___x_1254_, v_discrs_1248_);
v___x_1256_ = lean_box(v_useSplitter_1224_);
lean_inc(v_inst_1216_);
lean_inc(v_mask_1255_);
v___f_1257_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 13, 12);
lean_closure_set(v___f_1257_, 0, v_toFunctor_1246_);
lean_closure_set(v___f_1257_, 1, v_mask_1255_);
lean_closure_set(v___f_1257_, 2, v_toPure_1247_);
lean_closure_set(v___f_1257_, 3, v_inst_1216_);
lean_closure_set(v___f_1257_, 4, v_inst_1217_);
lean_closure_set(v___f_1257_, 5, v_inst_1218_);
lean_closure_set(v___f_1257_, 6, v_inst_1219_);
lean_closure_set(v___f_1257_, 7, v_inst_1220_);
lean_closure_set(v___f_1257_, 8, v_matcherApp_1244_);
lean_closure_set(v___f_1257_, 9, v___x_1256_);
lean_closure_set(v___f_1257_, 10, v___f_1250_);
lean_closure_set(v___f_1257_, 11, v___f_1249_);
v_maskedDiscrs_1258_ = l_Array_mask___redArg(v_mask_1255_, v_discrs_1248_);
lean_dec(v_mask_1255_);
v___x_1259_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1259_, 0, v_resTy_1222_);
lean_closure_set(v___x_1259_, 1, v_maskedDiscrs_1258_);
v___x_1260_ = lean_apply_2(v_inst_1216_, lean_box(0), v___x_1259_);
v___x_1261_ = lean_apply_4(v_toBind_1245_, lean_box(0), lean_box(0), v___x_1260_, v___f_1257_);
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_info_1267_, lean_object* v_resTy_1268_, lean_object* v_onAlt_1269_, lean_object* v_useSplitter_1270_){
_start:
{
uint8_t v_useSplitter_boxed_1271_; lean_object* v_res_1272_; 
v_useSplitter_boxed_1271_ = lean_unbox(v_useSplitter_1270_);
v_res_1272_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1262_, v_inst_1263_, v_inst_1264_, v_inst_1265_, v_inst_1266_, v_info_1267_, v_resTy_1268_, v_onAlt_1269_, v_useSplitter_boxed_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1273_, lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v_info_1282_, lean_object* v_resTy_1283_, lean_object* v_onAlt_1284_, uint8_t v_useSplitter_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1274_, v_inst_1275_, v_inst_1276_, v_inst_1277_, v_inst_1278_, v_info_1282_, v_resTy_1283_, v_onAlt_1284_, v_useSplitter_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_info_1296_, lean_object* v_resTy_1297_, lean_object* v_onAlt_1298_, lean_object* v_useSplitter_1299_){
_start:
{
uint8_t v_useSplitter_boxed_1300_; lean_object* v_res_1301_; 
v_useSplitter_boxed_1300_ = lean_unbox(v_useSplitter_1299_);
v_res_1301_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1287_, v_inst_1288_, v_inst_1289_, v_inst_1290_, v_inst_1291_, v_inst_1292_, v_inst_1293_, v_inst_1294_, v_inst_1295_, v_info_1296_, v_resTy_1297_, v_onAlt_1298_, v_useSplitter_boxed_1300_);
lean_dec(v_inst_1295_);
lean_dec(v_inst_1294_);
lean_dec_ref(v_inst_1293_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1302_, lean_object* v_e_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
if (lean_obj_tag(v_info_1302_) == 2)
{
lean_object* v_matcherApp_1312_; lean_object* v_toMatcherInfo_1313_; lean_object* v___x_1314_; 
v_matcherApp_1312_ = lean_ctor_get(v_info_1302_, 0);
lean_inc_ref(v_matcherApp_1312_);
lean_dec_ref(v_info_1302_);
v_toMatcherInfo_1313_ = lean_ctor_get(v_matcherApp_1312_, 0);
lean_inc_ref(v_toMatcherInfo_1313_);
lean_dec_ref(v_matcherApp_1312_);
v___x_1314_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1313_, v_e_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_e_1303_);
lean_dec_ref(v_info_1302_);
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1317_, lean_object* v_e_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1317_, v_e_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; lean_object* v_env_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1331_ = lean_st_ref_get(v___y_1329_);
v_env_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc_ref(v_env_1332_);
lean_dec(v___x_1331_);
v___x_1333_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1332_, v_declName_1328_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1335_, v___y_1336_);
lean_dec(v___y_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v_env_1346_; lean_object* v___x_1347_; lean_object* v_mctx_1348_; lean_object* v_lctx_1349_; lean_object* v_options_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1345_ = lean_st_ref_get(v___y_1343_);
v_env_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc_ref(v_env_1346_);
lean_dec(v___x_1345_);
v___x_1347_ = lean_st_ref_get(v___y_1341_);
v_mctx_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc_ref(v_mctx_1348_);
lean_dec(v___x_1347_);
v_lctx_1349_ = lean_ctor_get(v___y_1340_, 2);
v_options_1350_ = lean_ctor_get(v___y_1342_, 2);
lean_inc_ref(v_options_1350_);
lean_inc_ref(v_lctx_1349_);
v___x_1351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1351_, 0, v_env_1346_);
lean_ctor_set(v___x_1351_, 1, v_mctx_1348_);
lean_ctor_set(v___x_1351_, 2, v_lctx_1349_);
lean_ctor_set(v___x_1351_, 3, v_options_1350_);
v___x_1352_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v_msgData_1339_);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_ref_1367_; lean_object* v___x_1368_; lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1377_; 
v_ref_1367_ = lean_ctor_get(v___y_1364_, 5);
v___x_1368_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_inc(v_ref_1367_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_ref_1367_);
lean_ctor_set(v___x_1373_, 1, v_a_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set_tag(v___x_1371_, 1);
lean_ctor_set(v___x_1371_, 0, v___x_1373_);
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_1385_, lean_object* v_msg_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_fileName_1392_; lean_object* v_fileMap_1393_; lean_object* v_options_1394_; lean_object* v_currRecDepth_1395_; lean_object* v_maxRecDepth_1396_; lean_object* v_ref_1397_; lean_object* v_currNamespace_1398_; lean_object* v_openDecls_1399_; lean_object* v_initHeartbeats_1400_; lean_object* v_maxHeartbeats_1401_; lean_object* v_quotContext_1402_; lean_object* v_currMacroScope_1403_; uint8_t v_diag_1404_; lean_object* v_cancelTk_x3f_1405_; uint8_t v_suppressElabErrors_1406_; lean_object* v_inheritedTraceOptions_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1416_; 
v_fileName_1392_ = lean_ctor_get(v___y_1389_, 0);
v_fileMap_1393_ = lean_ctor_get(v___y_1389_, 1);
v_options_1394_ = lean_ctor_get(v___y_1389_, 2);
v_currRecDepth_1395_ = lean_ctor_get(v___y_1389_, 3);
v_maxRecDepth_1396_ = lean_ctor_get(v___y_1389_, 4);
v_ref_1397_ = lean_ctor_get(v___y_1389_, 5);
v_currNamespace_1398_ = lean_ctor_get(v___y_1389_, 6);
v_openDecls_1399_ = lean_ctor_get(v___y_1389_, 7);
v_initHeartbeats_1400_ = lean_ctor_get(v___y_1389_, 8);
v_maxHeartbeats_1401_ = lean_ctor_get(v___y_1389_, 9);
v_quotContext_1402_ = lean_ctor_get(v___y_1389_, 10);
v_currMacroScope_1403_ = lean_ctor_get(v___y_1389_, 11);
v_diag_1404_ = lean_ctor_get_uint8(v___y_1389_, sizeof(void*)*14);
v_cancelTk_x3f_1405_ = lean_ctor_get(v___y_1389_, 12);
v_suppressElabErrors_1406_ = lean_ctor_get_uint8(v___y_1389_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1407_ = lean_ctor_get(v___y_1389_, 13);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___y_1389_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1409_ = v___y_1389_;
v_isShared_1410_ = v_isSharedCheck_1416_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_inheritedTraceOptions_1407_);
lean_inc(v_cancelTk_x3f_1405_);
lean_inc(v_currMacroScope_1403_);
lean_inc(v_quotContext_1402_);
lean_inc(v_maxHeartbeats_1401_);
lean_inc(v_initHeartbeats_1400_);
lean_inc(v_openDecls_1399_);
lean_inc(v_currNamespace_1398_);
lean_inc(v_ref_1397_);
lean_inc(v_maxRecDepth_1396_);
lean_inc(v_currRecDepth_1395_);
lean_inc(v_options_1394_);
lean_inc(v_fileMap_1393_);
lean_inc(v_fileName_1392_);
lean_dec(v___y_1389_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1416_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_ref_1411_; lean_object* v___x_1413_; 
v_ref_1411_ = l_Lean_replaceRef(v_ref_1385_, v_ref_1397_);
lean_dec(v_ref_1397_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 5, v_ref_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_fileName_1392_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_fileMap_1393_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_options_1394_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_currRecDepth_1395_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_maxRecDepth_1396_);
lean_ctor_set(v_reuseFailAlloc_1415_, 5, v_ref_1411_);
lean_ctor_set(v_reuseFailAlloc_1415_, 6, v_currNamespace_1398_);
lean_ctor_set(v_reuseFailAlloc_1415_, 7, v_openDecls_1399_);
lean_ctor_set(v_reuseFailAlloc_1415_, 8, v_initHeartbeats_1400_);
lean_ctor_set(v_reuseFailAlloc_1415_, 9, v_maxHeartbeats_1401_);
lean_ctor_set(v_reuseFailAlloc_1415_, 10, v_quotContext_1402_);
lean_ctor_set(v_reuseFailAlloc_1415_, 11, v_currMacroScope_1403_);
lean_ctor_set(v_reuseFailAlloc_1415_, 12, v_cancelTk_x3f_1405_);
lean_ctor_set(v_reuseFailAlloc_1415_, 13, v_inheritedTraceOptions_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1415_, sizeof(void*)*14, v_diag_1404_);
lean_ctor_set_uint8(v_reuseFailAlloc_1415_, sizeof(void*)*14 + 1, v_suppressElabErrors_1406_);
v___x_1413_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1386_, v___y_1387_, v___y_1388_, v___x_1413_, v___y_1390_);
lean_dec_ref(v___x_1413_);
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1417_, lean_object* v_msg_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1417_, v_msg_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v_ref_1417_);
return v_res_1424_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
lean_ctor_set(v___x_1430_, 2, v___x_1429_);
lean_ctor_set(v___x_1430_, 3, v___x_1428_);
lean_ctor_set(v___x_1430_, 4, v___x_1428_);
lean_ctor_set(v___x_1430_, 5, v___x_1428_);
lean_ctor_set(v___x_1430_, 6, v___x_1428_);
lean_ctor_set(v___x_1430_, 7, v___x_1428_);
lean_ctor_set(v___x_1430_, 8, v___x_1428_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = lean_unsigned_to_nat(32u);
v___x_1432_ = lean_mk_empty_array_with_capacity(v___x_1431_);
v___x_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1434_ = ((size_t)5ULL);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_unsigned_to_nat(32u);
v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
v___x_1438_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1439_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v___x_1437_);
lean_ctor_set(v___x_1439_, 2, v___x_1435_);
lean_ctor_set(v___x_1439_, 3, v___x_1435_);
lean_ctor_set_usize(v___x_1439_, 4, v___x_1434_);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1440_ = lean_box(1);
v___x_1441_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1442_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v___x_1441_);
lean_ctor_set(v___x_1443_, 2, v___x_1440_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1446_ = l_Lean_stringToMessageData(v___x_1445_);
return v___x_1446_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1449_ = l_Lean_stringToMessageData(v___x_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1452_ = l_Lean_stringToMessageData(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1455_ = l_Lean_stringToMessageData(v___x_1454_);
return v___x_1455_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1458_ = l_Lean_stringToMessageData(v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1461_ = l_Lean_stringToMessageData(v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1464_ = l_Lean_stringToMessageData(v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1465_, lean_object* v_declHint_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v_env_1470_; uint8_t v___x_1471_; 
v___x_1469_ = lean_st_ref_get(v___y_1467_);
v_env_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc_ref(v_env_1470_);
lean_dec(v___x_1469_);
v___x_1471_ = l_Lean_Name_isAnonymous(v_declHint_1466_);
if (v___x_1471_ == 0)
{
uint8_t v_isExporting_1472_; 
v_isExporting_1472_ = lean_ctor_get_uint8(v_env_1470_, sizeof(void*)*8);
if (v_isExporting_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec_ref(v_env_1470_);
lean_dec(v_declHint_1466_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_msg_1465_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; uint8_t v___x_1475_; 
lean_inc_ref(v_env_1470_);
v___x_1474_ = l_Lean_Environment_setExporting(v_env_1470_, v___x_1471_);
lean_inc(v_declHint_1466_);
lean_inc_ref(v___x_1474_);
v___x_1475_ = l_Lean_Environment_contains(v___x_1474_, v_declHint_1466_, v_isExporting_1472_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref(v___x_1474_);
lean_dec_ref(v_env_1470_);
lean_dec(v_declHint_1466_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_msg_1465_);
return v___x_1476_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_c_1482_; lean_object* v___x_1483_; 
v___x_1477_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1478_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1479_ = l_Lean_Options_empty;
v___x_1480_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1474_);
lean_ctor_set(v___x_1480_, 1, v___x_1477_);
lean_ctor_set(v___x_1480_, 2, v___x_1478_);
lean_ctor_set(v___x_1480_, 3, v___x_1479_);
lean_inc(v_declHint_1466_);
v___x_1481_ = l_Lean_MessageData_ofConstName(v_declHint_1466_, v___x_1471_);
v_c_1482_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1482_, 0, v___x_1480_);
lean_ctor_set(v_c_1482_, 1, v___x_1481_);
v___x_1483_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1470_, v_declHint_1466_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref(v_env_1470_);
lean_dec(v_declHint_1466_);
v___x_1484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v_c_1482_);
v___x_1486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_MessageData_note(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_msg_1465_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
else
{
lean_object* v_val_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1526_; 
v_val_1491_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1493_ = v___x_1483_;
v_isShared_1494_ = v_isSharedCheck_1526_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_val_1491_);
lean_dec(v___x_1483_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1526_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_mod_1498_; uint8_t v___x_1499_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = l_Lean_Environment_header(v_env_1470_);
lean_dec_ref(v_env_1470_);
v___x_1497_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1496_);
v_mod_1498_ = lean_array_get(v___x_1495_, v___x_1497_, v_val_1491_);
lean_dec(v_val_1491_);
lean_dec_ref(v___x_1497_);
v___x_1499_ = l_Lean_isPrivateName(v_declHint_1466_);
lean_dec(v_declHint_1466_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1500_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v_c_1482_);
v___x_1502_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = l_Lean_MessageData_ofName(v_mod_1498_);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_MessageData_note(v___x_1507_);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_msg_1465_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set_tag(v___x_1493_, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1509_);
v___x_1511_ = v___x_1493_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1513_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_c_1482_);
v___x_1515_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_MessageData_ofName(v_mod_1498_);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = l_Lean_MessageData_note(v___x_1520_);
v___x_1522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_msg_1465_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set_tag(v___x_1493_, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1522_);
v___x_1524_ = v___x_1493_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1527_; 
lean_dec_ref(v_env_1470_);
lean_dec(v_declHint_1466_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_msg_1465_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1528_, lean_object* v_declHint_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1528_, v_declHint_1529_, v___y_1530_);
lean_dec(v___y_1530_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1533_, lean_object* v_declHint_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1550_; 
v___x_1540_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1533_, v_declHint_1534_, v___y_1538_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1550_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1550_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1545_ = l_Lean_unknownIdentifierMessageTag;
v___x_1546_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v_a_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1546_);
v___x_1548_ = v___x_1543_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1551_, lean_object* v_declHint_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1551_, v_declHint_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1559_, lean_object* v_msg_1560_, lean_object* v_declHint_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; lean_object* v_a_1568_; lean_object* v___x_1569_; 
v___x_1567_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1560_, v_declHint_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
v___x_1569_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1559_, v_a_1568_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1570_, lean_object* v_msg_1571_, lean_object* v_declHint_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1570_, v_msg_1571_, v_declHint_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v_ref_1570_);
return v_res_1578_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1581_ = l_Lean_stringToMessageData(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1584_ = l_Lean_stringToMessageData(v___x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1585_, lean_object* v_constName_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1592_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1593_ = 0;
lean_inc(v_constName_1586_);
v___x_1594_ = l_Lean_MessageData_ofConstName(v_constName_1586_, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1592_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1585_, v___x_1597_, v_constName_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1599_, lean_object* v_constName_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1599_, v_constName_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v_ref_1599_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_ref_1613_; lean_object* v___x_1614_; 
v_ref_1613_ = lean_ctor_get(v___y_1610_, 5);
lean_inc(v_ref_1613_);
v___x_1614_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1613_, v_constName_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v_ref_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; lean_object* v_env_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1628_ = lean_st_ref_get(v___y_1626_);
v_env_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc_ref(v_env_1629_);
lean_dec(v___x_1628_);
v___x_1630_ = 0;
lean_inc(v_constName_1622_);
v___x_1631_ = l_Lean_Environment_find_x3f(v_env_1629_, v_constName_1622_, v___x_1630_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1632_;
}
else
{
lean_object* v_val_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v___y_1625_);
lean_dec(v_constName_1622_);
v_val_1633_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1631_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_val_1633_);
lean_dec(v___x_1631_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 0);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_val_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v_toApplicative_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1716_; 
v___x_1654_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v___x_1654_, 1);
lean_dec(v_unused_1717_);
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1716_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_toApplicative_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1716_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v_toFunctor_1659_; lean_object* v_toSeq_1660_; lean_object* v_toSeqLeft_1661_; lean_object* v_toSeqRight_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1714_; 
v_toFunctor_1659_ = lean_ctor_get(v_toApplicative_1655_, 0);
v_toSeq_1660_ = lean_ctor_get(v_toApplicative_1655_, 2);
v_toSeqLeft_1661_ = lean_ctor_get(v_toApplicative_1655_, 3);
v_toSeqRight_1662_ = lean_ctor_get(v_toApplicative_1655_, 4);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_toApplicative_1655_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_toApplicative_1655_, 1);
lean_dec(v_unused_1715_);
v___x_1664_ = v_toApplicative_1655_;
v_isShared_1665_ = v_isSharedCheck_1714_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_toSeqRight_1662_);
lean_inc(v_toSeqLeft_1661_);
lean_inc(v_toSeq_1660_);
lean_inc(v_toFunctor_1659_);
lean_dec(v_toApplicative_1655_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1714_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___f_1666_; lean_object* v___f_1667_; lean_object* v___f_1668_; lean_object* v___f_1669_; lean_object* v___x_1670_; lean_object* v___f_1671_; lean_object* v___f_1672_; lean_object* v___f_1673_; lean_object* v___x_1675_; 
v___f_1666_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_1667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref(v_toFunctor_1659_);
v___f_1668_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1668_, 0, v_toFunctor_1659_);
v___f_1669_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1669_, 0, v_toFunctor_1659_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___f_1668_);
lean_ctor_set(v___x_1670_, 1, v___f_1669_);
v___f_1671_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1671_, 0, v_toSeqRight_1662_);
v___f_1672_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1672_, 0, v_toSeqLeft_1661_);
v___f_1673_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1673_, 0, v_toSeq_1660_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 4, v___f_1671_);
lean_ctor_set(v___x_1664_, 3, v___f_1672_);
lean_ctor_set(v___x_1664_, 2, v___f_1673_);
lean_ctor_set(v___x_1664_, 1, v___f_1666_);
lean_ctor_set(v___x_1664_, 0, v___x_1670_);
v___x_1675_ = v___x_1664_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___f_1666_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v___f_1673_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v___f_1672_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v___f_1671_);
v___x_1675_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v___f_1667_);
lean_ctor_set(v___x_1657_, 0, v___x_1675_);
v___x_1677_ = v___x_1657_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___f_1667_);
v___x_1677_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v_toApplicative_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1710_; 
v___x_1678_ = l_ReaderT_instMonad___redArg(v___x_1677_);
v_toApplicative_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v___x_1678_, 1);
lean_dec(v_unused_1711_);
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1710_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_toApplicative_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1710_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_toFunctor_1683_; lean_object* v_toSeq_1684_; lean_object* v_toSeqLeft_1685_; lean_object* v_toSeqRight_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1708_; 
v_toFunctor_1683_ = lean_ctor_get(v_toApplicative_1679_, 0);
v_toSeq_1684_ = lean_ctor_get(v_toApplicative_1679_, 2);
v_toSeqLeft_1685_ = lean_ctor_get(v_toApplicative_1679_, 3);
v_toSeqRight_1686_ = lean_ctor_get(v_toApplicative_1679_, 4);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_toApplicative_1679_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v_toApplicative_1679_, 1);
lean_dec(v_unused_1709_);
v___x_1688_ = v_toApplicative_1679_;
v_isShared_1689_ = v_isSharedCheck_1708_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_toSeqRight_1686_);
lean_inc(v_toSeqLeft_1685_);
lean_inc(v_toSeq_1684_);
lean_inc(v_toFunctor_1683_);
lean_dec(v_toApplicative_1679_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1708_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___x_1694_; lean_object* v___f_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___x_1699_; 
v___f_1690_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_1691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_1683_);
v___f_1692_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1692_, 0, v_toFunctor_1683_);
v___f_1693_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1693_, 0, v_toFunctor_1683_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___f_1692_);
lean_ctor_set(v___x_1694_, 1, v___f_1693_);
v___f_1695_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1695_, 0, v_toSeqRight_1686_);
v___f_1696_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1696_, 0, v_toSeqLeft_1685_);
v___f_1697_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1697_, 0, v_toSeq_1684_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 4, v___f_1695_);
lean_ctor_set(v___x_1688_, 3, v___f_1696_);
lean_ctor_set(v___x_1688_, 2, v___f_1697_);
lean_ctor_set(v___x_1688_, 1, v___f_1690_);
lean_ctor_set(v___x_1688_, 0, v___x_1694_);
v___x_1699_ = v___x_1688_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___f_1690_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v___f_1697_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v___f_1696_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v___f_1695_);
v___x_1699_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
lean_object* v___x_1701_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___f_1691_);
lean_ctor_set(v___x_1681_, 0, v___x_1699_);
v___x_1701_ = v___x_1681_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___f_1691_);
v___x_1701_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_3049__overap_1704_; lean_object* v___x_1705_; 
v___x_1702_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1703_ = l_instInhabitedOfMonad___redArg(v___x_1701_, v___x_1702_);
v___x_3049__overap_1704_ = lean_panic_fn(v___x_1703_, v_msg_1648_);
v___x_1705_ = lean_apply_5(v___x_3049__overap_1704_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, lean_box(0));
return v___x_1705_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v_res_1724_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_1729_ = lean_unsigned_to_nat(53u);
v___x_1730_ = lean_unsigned_to_nat(62u);
v___x_1731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_1732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_1733_ = l_mkPanicMessageWithDecl(v___x_1732_, v___x_1731_, v___x_1730_, v___x_1729_, v___x_1728_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_1734_, size_t v_i_1735_, lean_object* v_bs_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_usize_dec_lt(v_i_1735_, v_sz_1734_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; 
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_bs_1736_);
return v___x_1743_;
}
else
{
lean_object* v_v_1744_; lean_object* v___x_1745_; 
v_v_1744_ = lean_array_uget_borrowed(v_bs_1736_, v_i_1735_);
lean_inc_ref(v___y_1739_);
lean_inc(v_v_1744_);
v___x_1745_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_1744_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; lean_object* v_bs_x27_1748_; lean_object* v_a_1750_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref(v___x_1745_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v_bs_x27_1748_ = lean_array_uset(v_bs_1736_, v_i_1735_, v___x_1747_);
if (lean_obj_tag(v_a_1746_) == 6)
{
lean_object* v_val_1755_; lean_object* v_numFields_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; 
v_val_1755_ = lean_ctor_get(v_a_1746_, 0);
lean_inc_ref(v_val_1755_);
lean_dec_ref(v_a_1746_);
v_numFields_1756_ = lean_ctor_get(v_val_1755_, 4);
lean_inc(v_numFields_1756_);
lean_dec_ref(v_val_1755_);
v___x_1757_ = 0;
v___x_1758_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1758_, 0, v_numFields_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1747_);
lean_ctor_set_uint8(v___x_1758_, sizeof(void*)*2, v___x_1757_);
v_a_1750_ = v___x_1758_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_dec(v_a_1746_);
v___x_1759_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
lean_inc(v___y_1740_);
lean_inc_ref(v___y_1739_);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
v___x_1760_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_1759_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref(v___x_1760_);
v_a_1750_ = v_a_1761_;
goto v___jp_1749_;
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v_bs_x27_1748_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
v_a_1762_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1760_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
v___jp_1749_:
{
size_t v___x_1751_; size_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1735_, v___x_1751_);
v___x_1753_ = lean_array_uset(v_bs_x27_1748_, v_i_1735_, v_a_1750_);
v_i_1735_ = v___x_1752_;
v_bs_1736_ = v___x_1753_;
goto _start;
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v_bs_1736_);
v_a_1770_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1745_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1745_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_1778_, lean_object* v_i_1779_, lean_object* v_bs_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
size_t v_sz_boxed_1786_; size_t v_i_boxed_1787_; lean_object* v_res_1788_; 
v_sz_boxed_1786_ = lean_unbox_usize(v_sz_1778_);
lean_dec(v_sz_1778_);
v_i_boxed_1787_ = lean_unbox_usize(v_i_1779_);
lean_dec(v_i_1779_);
v_res_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_1786_, v_i_boxed_1787_, v_bs_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v_res_1788_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1789_; lean_object* v_dummy_1790_; 
v___x_1789_ = lean_box(0);
v_dummy_1790_ = l_Lean_Expr_sort___override(v___x_1789_);
return v_dummy_1790_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_unsigned_to_nat(16u);
v___x_1793_ = lean_mk_array(v___x_1792_, v___x_1791_);
return v___x_1793_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___x_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_1799_, uint8_t v_alsoCasesOn_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v___x_1809_; 
v___x_1809_ = l_Lean_Expr_isApp(v_e_1799_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_e_1799_);
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_Expr_getAppFn(v_e_1799_);
if (lean_obj_tag(v___x_1812_) == 4)
{
lean_object* v_declName_1813_; lean_object* v_us_1814_; lean_object* v___x_1815_; lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1970_; 
v_declName_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_declName_1813_);
v_us_1814_ = lean_ctor_get(v___x_1812_, 1);
lean_inc(v_us_1814_);
lean_dec_ref(v___x_1812_);
lean_inc(v_declName_1813_);
v___x_1815_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1813_, v___y_1804_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1970_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1970_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
if (lean_obj_tag(v_a_1816_) == 1)
{
lean_object* v_val_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
v_val_1820_ = lean_ctor_get(v_a_1816_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_a_1816_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1822_ = v_a_1816_;
v_isShared_1823_ = v_isSharedCheck_1862_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_val_1820_);
lean_dec(v_a_1816_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1862_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_dummy_1824_; lean_object* v_nargs_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_args_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_dummy_1824_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v_nargs_1825_ = l_Lean_Expr_getAppNumArgs(v_e_1799_);
lean_inc(v_nargs_1825_);
v___x_1826_ = lean_mk_array(v_nargs_1825_, v_dummy_1824_);
v___x_1827_ = lean_unsigned_to_nat(1u);
v___x_1828_ = lean_nat_sub(v_nargs_1825_, v___x_1827_);
lean_dec(v_nargs_1825_);
v_args_1829_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1799_, v___x_1826_, v___x_1828_);
v___x_1830_ = lean_array_get_size(v_args_1829_);
v___x_1831_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1820_);
v___x_1832_ = lean_nat_dec_lt(v___x_1830_, v___x_1831_);
lean_dec(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v_numParams_1833_; lean_object* v_numDiscrs_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v_numParams_1833_ = lean_ctor_get(v_val_1820_, 0);
v_numDiscrs_1834_ = lean_ctor_get(v_val_1820_, 1);
v___x_1835_ = lean_array_mk(v_us_1814_);
v___x_1836_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1833_);
v___x_1837_ = l_Array_extract___redArg(v_args_1829_, v___x_1836_, v_numParams_1833_);
v___x_1838_ = l_Lean_instInhabitedExpr;
v___x_1839_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1820_);
v___x_1840_ = lean_array_get(v___x_1838_, v_args_1829_, v___x_1839_);
lean_dec(v___x_1839_);
v___x_1841_ = lean_nat_add(v_numParams_1833_, v___x_1827_);
v___x_1842_ = lean_nat_add(v___x_1841_, v_numDiscrs_1834_);
lean_inc(v___x_1842_);
lean_inc_ref(v_args_1829_);
v___x_1843_ = l_Array_toSubarray___redArg(v_args_1829_, v___x_1841_, v___x_1842_);
v___x_1844_ = l_Subarray_copy___redArg(v___x_1843_);
v___x_1845_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1820_);
v___x_1846_ = lean_nat_add(v___x_1842_, v___x_1845_);
lean_dec(v___x_1845_);
lean_inc(v___x_1846_);
lean_inc_ref(v_args_1829_);
v___x_1847_ = l_Array_toSubarray___redArg(v_args_1829_, v___x_1842_, v___x_1846_);
v___x_1848_ = l_Subarray_copy___redArg(v___x_1847_);
v___x_1849_ = l_Array_toSubarray___redArg(v_args_1829_, v___x_1846_, v___x_1830_);
v___x_1850_ = l_Subarray_copy___redArg(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1851_, 0, v_val_1820_);
lean_ctor_set(v___x_1851_, 1, v_declName_1813_);
lean_ctor_set(v___x_1851_, 2, v___x_1835_);
lean_ctor_set(v___x_1851_, 3, v___x_1837_);
lean_ctor_set(v___x_1851_, 4, v___x_1840_);
lean_ctor_set(v___x_1851_, 5, v___x_1844_);
lean_ctor_set(v___x_1851_, 6, v___x_1848_);
lean_ctor_set(v___x_1851_, 7, v___x_1850_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1851_);
v___x_1853_ = v___x_1822_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1853_);
v___x_1855_ = v___x_1818_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
lean_dec_ref(v_args_1829_);
lean_del_object(v___x_1822_);
lean_dec(v_val_1820_);
lean_dec(v_us_1814_);
lean_dec(v_declName_1813_);
v___x_1858_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1858_);
v___x_1860_ = v___x_1818_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v___x_1863_; 
lean_del_object(v___x_1818_);
lean_dec(v_a_1816_);
v___x_1863_ = lean_st_ref_get(v___y_1804_);
if (v_alsoCasesOn_1800_ == 0)
{
lean_dec(v___x_1863_);
lean_dec(v_us_1814_);
lean_dec(v_declName_1813_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_e_1799_);
goto v___jp_1806_;
}
else
{
lean_object* v_env_1864_; uint8_t v___x_1865_; 
v_env_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc_ref(v_env_1864_);
lean_dec(v___x_1863_);
lean_inc(v_declName_1813_);
v___x_1865_ = l_Lean_isCasesOnRecursor(v_env_1864_, v_declName_1813_);
if (v___x_1865_ == 0)
{
lean_dec(v_us_1814_);
lean_dec(v_declName_1813_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_e_1799_);
goto v___jp_1806_;
}
else
{
lean_object* v_indName_1866_; lean_object* v___x_1867_; 
v_indName_1866_ = l_Lean_Name_getPrefix(v_declName_1813_);
lean_inc_ref(v___y_1803_);
v___x_1867_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_1866_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1961_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1961_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1961_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
if (lean_obj_tag(v_a_1868_) == 5)
{
lean_object* v_val_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1956_; 
v_val_1872_ = lean_ctor_get(v_a_1868_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_a_1868_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1874_ = v_a_1868_;
v_isShared_1875_ = v_isSharedCheck_1956_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_val_1872_);
lean_dec(v_a_1868_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1956_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_toConstantVal_1876_; lean_object* v_numParams_1877_; lean_object* v_numIndices_1878_; lean_object* v_ctors_1879_; lean_object* v_nargs_1880_; lean_object* v_dummy_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v_args_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_toConstantVal_1876_ = lean_ctor_get(v_val_1872_, 0);
lean_inc_ref(v_toConstantVal_1876_);
v_numParams_1877_ = lean_ctor_get(v_val_1872_, 1);
lean_inc(v_numParams_1877_);
v_numIndices_1878_ = lean_ctor_get(v_val_1872_, 2);
lean_inc(v_numIndices_1878_);
v_ctors_1879_ = lean_ctor_get(v_val_1872_, 4);
lean_inc(v_ctors_1879_);
v_nargs_1880_ = l_Lean_Expr_getAppNumArgs(v_e_1799_);
v_dummy_1881_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
lean_inc(v_nargs_1880_);
v___x_1882_ = lean_mk_array(v_nargs_1880_, v_dummy_1881_);
v___x_1883_ = lean_unsigned_to_nat(1u);
v___x_1884_ = lean_nat_sub(v_nargs_1880_, v___x_1883_);
lean_dec(v_nargs_1880_);
v_args_1885_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1799_, v___x_1882_, v___x_1884_);
v___x_1886_ = lean_nat_add(v_numParams_1877_, v___x_1883_);
v___x_1887_ = lean_nat_add(v___x_1886_, v_numIndices_1878_);
v___x_1888_ = lean_nat_add(v___x_1887_, v___x_1883_);
lean_dec(v___x_1887_);
v___x_1889_ = l_Lean_InductiveVal_numCtors(v_val_1872_);
lean_dec_ref(v_val_1872_);
v___x_1890_ = lean_nat_add(v___x_1888_, v___x_1889_);
lean_dec(v___x_1889_);
v___x_1891_ = lean_array_get_size(v_args_1885_);
v___x_1892_ = lean_nat_dec_le(v___x_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_dec(v___x_1890_);
lean_dec(v___x_1888_);
lean_dec(v___x_1886_);
lean_dec_ref(v_args_1885_);
lean_dec(v_ctors_1879_);
lean_dec(v_numIndices_1878_);
lean_dec(v_numParams_1877_);
lean_dec_ref(v_toConstantVal_1876_);
lean_del_object(v___x_1874_);
lean_dec(v_us_1814_);
lean_dec(v_declName_1813_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
v___x_1893_ = lean_box(0);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1893_);
v___x_1895_ = v___x_1870_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
else
{
lean_object* v___x_1897_; lean_object* v_params_1898_; lean_object* v___x_1899_; lean_object* v_motive_1900_; lean_object* v_discrs_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_discrInfos_1904_; lean_object* v_alts_1905_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v_lower_1947_; lean_object* v_upper_1948_; uint8_t v___x_1955_; 
lean_del_object(v___x_1870_);
v___x_1897_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1877_);
lean_inc_ref(v_args_1885_);
v_params_1898_ = l_Array_toSubarray___redArg(v_args_1885_, v___x_1897_, v_numParams_1877_);
v___x_1899_ = l_Lean_instInhabitedExpr;
v_motive_1900_ = lean_array_get(v___x_1899_, v_args_1885_, v_numParams_1877_);
lean_dec(v_numParams_1877_);
lean_inc(v___x_1888_);
lean_inc_ref(v_args_1885_);
v_discrs_1901_ = l_Array_toSubarray___redArg(v_args_1885_, v___x_1886_, v___x_1888_);
v___x_1902_ = lean_nat_add(v_numIndices_1878_, v___x_1883_);
lean_dec(v_numIndices_1878_);
v___x_1903_ = lean_box(0);
v_discrInfos_1904_ = lean_mk_array(v___x_1902_, v___x_1903_);
lean_inc(v___x_1890_);
lean_inc_ref(v_args_1885_);
v_alts_1905_ = l_Array_toSubarray___redArg(v_args_1885_, v___x_1888_, v___x_1890_);
v___x_1955_ = lean_nat_dec_le(v___x_1890_, v___x_1897_);
if (v___x_1955_ == 0)
{
v_lower_1947_ = v___x_1890_;
v_upper_1948_ = v___x_1891_;
goto v___jp_1946_;
}
else
{
lean_dec(v___x_1890_);
v_lower_1947_ = v___x_1897_;
v_upper_1948_ = v___x_1891_;
goto v___jp_1946_;
}
v___jp_1906_:
{
lean_object* v___x_1909_; size_t v_sz_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1909_ = lean_array_mk(v_ctors_1879_);
v_sz_1910_ = lean_array_size(v___x_1909_);
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_1910_, v___x_1911_, v___x_1909_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1937_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1937_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1937_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_start_1917_; lean_object* v_stop_1918_; lean_object* v_start_1919_; lean_object* v_stop_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v_start_1917_ = lean_ctor_get(v_params_1898_, 1);
lean_inc(v_start_1917_);
v_stop_1918_ = lean_ctor_get(v_params_1898_, 2);
lean_inc(v_stop_1918_);
v_start_1919_ = lean_ctor_get(v_discrs_1901_, 1);
lean_inc(v_start_1919_);
v_stop_1920_ = lean_ctor_get(v_discrs_1901_, 2);
lean_inc(v_stop_1920_);
v___x_1921_ = lean_nat_sub(v_stop_1918_, v_start_1917_);
lean_dec(v_start_1917_);
lean_dec(v_stop_1918_);
v___x_1922_ = lean_nat_sub(v_stop_1920_, v_start_1919_);
lean_dec(v_start_1919_);
lean_dec(v_stop_1920_);
v___x_1923_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
v___x_1924_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1921_);
lean_ctor_set(v___x_1924_, 1, v___x_1922_);
lean_ctor_set(v___x_1924_, 2, v_a_1913_);
lean_ctor_set(v___x_1924_, 3, v___y_1908_);
lean_ctor_set(v___x_1924_, 4, v_discrInfos_1904_);
lean_ctor_set(v___x_1924_, 5, v___x_1923_);
v___x_1925_ = lean_array_mk(v_us_1814_);
v___x_1926_ = l_Subarray_copy___redArg(v_params_1898_);
v___x_1927_ = l_Subarray_copy___redArg(v_discrs_1901_);
v___x_1928_ = l_Subarray_copy___redArg(v_alts_1905_);
v___x_1929_ = l_Subarray_copy___redArg(v___y_1907_);
v___x_1930_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1924_);
lean_ctor_set(v___x_1930_, 1, v_declName_1813_);
lean_ctor_set(v___x_1930_, 2, v___x_1925_);
lean_ctor_set(v___x_1930_, 3, v___x_1926_);
lean_ctor_set(v___x_1930_, 4, v_motive_1900_);
lean_ctor_set(v___x_1930_, 5, v___x_1927_);
lean_ctor_set(v___x_1930_, 6, v___x_1928_);
lean_ctor_set(v___x_1930_, 7, v___x_1929_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 1);
lean_ctor_set(v___x_1874_, 0, v___x_1930_);
v___x_1932_ = v___x_1874_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1932_);
v___x_1934_ = v___x_1915_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_alts_1905_);
lean_dec_ref(v_discrInfos_1904_);
lean_dec_ref(v_discrs_1901_);
lean_dec(v_motive_1900_);
lean_dec_ref(v_params_1898_);
lean_del_object(v___x_1874_);
lean_dec(v_us_1814_);
lean_dec(v_declName_1813_);
v_a_1938_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1912_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1912_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
v___jp_1946_:
{
lean_object* v_levelParams_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v_levelParams_1949_ = lean_ctor_get(v_toConstantVal_1876_, 1);
lean_inc(v_levelParams_1949_);
lean_dec_ref(v_toConstantVal_1876_);
v___x_1950_ = l_Array_toSubarray___redArg(v_args_1885_, v_lower_1947_, v_upper_1948_);
v___x_1951_ = l_List_lengthTR___redArg(v_levelParams_1949_);
lean_dec(v_levelParams_1949_);
v___x_1952_ = l_List_lengthTR___redArg(v_us_1814_);
v___x_1953_ = lean_nat_dec_eq(v___x_1951_, v___x_1952_);
lean_dec(v___x_1952_);
lean_dec(v___x_1951_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
v___x_1954_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3));
v___y_1907_ = v___x_1950_;
v___y_1908_ = v___x_1954_;
goto v___jp_1906_;
}
else
{
v___y_1907_ = v___x_1950_;
v___y_1908_ = v___x_1903_;
goto v___jp_1906_;
}
}
}
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
lean_dec(v_a_1868_);
lean_dec(v_us_1814_);
lean_dec(v_declName_1813_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_e_1799_);
v___x_1957_ = lean_box(0);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1957_);
v___x_1959_ = v___x_1870_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_us_1814_);
lean_dec(v_declName_1813_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_e_1799_);
v_a_1962_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1867_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1867_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
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
lean_dec_ref(v___x_1812_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec_ref(v_e_1799_);
goto v___jp_1806_;
}
}
v___jp_1806_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_1971_, lean_object* v_alsoCasesOn_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1978_; lean_object* v_res_1979_; 
v_alsoCasesOn_boxed_1978_ = lean_unbox(v_alsoCasesOn_1972_);
v_res_1979_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1971_, v_alsoCasesOn_boxed_1978_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_1987_ = l_Lean_Expr_isAppOf(v_e_1980_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_1989_ = l_Lean_Expr_isAppOf(v_e_1980_, v___x_1988_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = 1;
v___x_1991_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1980_, v___x_1990_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2012_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2012_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2012_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
if (lean_obj_tag(v_a_1992_) == 1)
{
lean_object* v_val_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2007_; 
v_val_1996_ = lean_ctor_get(v_a_1992_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_a_1992_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1998_ = v_a_1992_;
v_isShared_1999_ = v_isSharedCheck_2007_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_val_1996_);
lean_dec(v_a_1992_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2007_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_val_1996_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2004_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2002_);
v___x_2004_ = v___x_1994_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
lean_dec(v_a_1992_);
v___x_2008_ = lean_box(0);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2008_);
v___x_2010_ = v___x_1994_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_a_2013_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1991_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1991_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_e_1980_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_e_1980_);
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2034_, v___y_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2048_, lean_object* v_constName_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_constName_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2056_, v_constName_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2064_, lean_object* v_ref_2065_, lean_object* v_constName_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2065_, v_constName_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2073_, lean_object* v_ref_2074_, lean_object* v_constName_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2073_, v_ref_2074_, v_constName_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v_ref_2074_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2082_, lean_object* v_ref_2083_, lean_object* v_msg_2084_, lean_object* v_declHint_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2083_, v_msg_2084_, v_declHint_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2092_, lean_object* v_ref_2093_, lean_object* v_msg_2094_, lean_object* v_declHint_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2092_, v_ref_2093_, v_msg_2094_, v_declHint_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v_ref_2093_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2102_, lean_object* v_declHint_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2102_, v_declHint_2103_, v___y_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2110_, lean_object* v_declHint_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2110_, v_declHint_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2118_, lean_object* v_ref_2119_, lean_object* v_msg_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2119_, v_msg_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_ref_2128_, lean_object* v_msg_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2127_, v_ref_2128_, v_msg_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v_ref_2128_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2136_, lean_object* v_msg_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2144_, lean_object* v_msg_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2144_, v_msg_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
return v_res_2151_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2155_, lean_object* v_e_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v___y_2163_; uint8_t v___y_2182_; lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2193_ = l_Lean_Expr_isAppOf(v_e_2156_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2195_ = l_Lean_Expr_isAppOf(v_e_2156_, v___x_2194_);
v___y_2182_ = v___x_2195_;
goto v___jp_2181_;
}
else
{
v___y_2182_ = v___x_2193_;
goto v___jp_2181_;
}
v___jp_2162_:
{
lean_object* v___x_2164_; 
lean_inc(v_a_2160_);
lean_inc_ref(v_a_2159_);
lean_inc(v_a_2158_);
lean_inc_ref(v_a_2157_);
lean_inc_ref(v___y_2163_);
v___x_2164_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2163_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
if (lean_obj_tag(v_a_2165_) == 1)
{
lean_object* v_val_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec_ref(v___y_2163_);
v_val_2166_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_val_2166_);
lean_dec_ref(v_a_2165_);
v___x_2167_ = l_Lean_mkFVar(v_val_2166_);
v___x_2168_ = l_Lean_Meta_rwIfWith(v___x_2167_, v_e_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec(v_a_2165_);
lean_dec_ref(v_e_2156_);
v___x_2169_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2170_ = l_Lean_MessageData_ofExpr(v___y_2163_);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2171_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
return v___x_2172_;
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v___y_2163_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec_ref(v_e_2156_);
v_a_2173_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2164_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2164_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
v___jp_2181_:
{
if (v___y_2182_ == 0)
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Meta_rwMatcher(v_idx_2155_, v_e_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_c_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = l_Lean_Expr_getAppNumArgs(v_e_2156_);
v___x_2186_ = lean_nat_sub(v___x_2185_, v___x_2184_);
lean_dec(v___x_2185_);
v___x_2187_ = lean_nat_sub(v___x_2186_, v___x_2184_);
lean_dec(v___x_2186_);
v_c_2188_ = l_Lean_Expr_getRevArg_x21(v_e_2156_, v___x_2187_);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_nat_dec_eq(v_idx_2155_, v___x_2189_);
lean_dec(v_idx_2155_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_mkNot(v_c_2188_);
v___y_2163_ = v___x_2191_;
goto v___jp_2162_;
}
else
{
v___y_2163_ = v_c_2188_;
goto v___jp_2162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2196_, lean_object* v_e_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2196_, v_e_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
return v_res_2203_;
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
