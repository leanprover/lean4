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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value)}};
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
lean_inc_ref_n(v_matcherApp_163_, 2);
lean_dec_ref(v_info_127_);
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
v___x_686_ = l_instMonadEIO(lean_box(0));
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_688_ = l_StateRefT_x27_instMonad___redArg(v___x_687_);
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
lean_object* v___x_707_; lean_object* v_toApplicative_708_; lean_object* v_toFunctor_709_; lean_object* v_toSeq_710_; lean_object* v_toSeqLeft_711_; lean_object* v_toSeqRight_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___f_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_toApplicative_726_; lean_object* v_toFunctor_727_; lean_object* v_toSeq_728_; lean_object* v_toSeqLeft_729_; lean_object* v_toSeqRight_730_; lean_object* v___f_731_; lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_toApplicative_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_798_; 
v___x_707_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_708_ = lean_ctor_get(v___x_707_, 0);
v_toFunctor_709_ = lean_ctor_get(v_toApplicative_708_, 0);
v_toSeq_710_ = lean_ctor_get(v_toApplicative_708_, 2);
v_toSeqLeft_711_ = lean_ctor_get(v_toApplicative_708_, 3);
v_toSeqRight_712_ = lean_ctor_get(v_toApplicative_708_, 4);
v___f_713_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_714_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_709_, 2);
v___f_715_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_715_, 0, v_toFunctor_709_);
v___f_716_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_716_, 0, v_toFunctor_709_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___f_715_);
lean_ctor_set(v___x_717_, 1, v___f_716_);
lean_inc(v_toSeqRight_712_);
v___f_718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_718_, 0, v_toSeqRight_712_);
lean_inc(v_toSeqLeft_711_);
v___f_719_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_719_, 0, v_toSeqLeft_711_);
lean_inc(v_toSeq_710_);
v___f_720_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_720_, 0, v_toSeq_710_);
v___x_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_721_, 0, v___x_717_);
lean_ctor_set(v___x_721_, 1, v___f_713_);
lean_ctor_set(v___x_721_, 2, v___f_720_);
lean_ctor_set(v___x_721_, 3, v___f_719_);
lean_ctor_set(v___x_721_, 4, v___f_718_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___f_714_);
v___x_723_ = l_StateRefT_x27_instMonad___redArg(v___x_722_);
v___x_724_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_724_, 0, lean_box(0));
lean_closure_set(v___x_724_, 1, lean_box(0));
lean_closure_set(v___x_724_, 2, v___x_723_);
v___x_725_ = l_instMonadControlTOfPure___redArg(v___x_724_);
v_toApplicative_726_ = lean_ctor_get(v___x_707_, 0);
v_toFunctor_727_ = lean_ctor_get(v_toApplicative_726_, 0);
v_toSeq_728_ = lean_ctor_get(v_toApplicative_726_, 2);
v_toSeqLeft_729_ = lean_ctor_get(v_toApplicative_726_, 3);
v_toSeqRight_730_ = lean_ctor_get(v_toApplicative_726_, 4);
lean_inc_ref_n(v_toFunctor_727_, 2);
v___f_731_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_731_, 0, v_toFunctor_727_);
v___f_732_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_732_, 0, v_toFunctor_727_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___f_731_);
lean_ctor_set(v___x_733_, 1, v___f_732_);
lean_inc(v_toSeqRight_730_);
v___f_734_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_734_, 0, v_toSeqRight_730_);
lean_inc(v_toSeqLeft_729_);
v___f_735_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_735_, 0, v_toSeqLeft_729_);
lean_inc(v_toSeq_728_);
v___f_736_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_736_, 0, v_toSeq_728_);
v___x_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_737_, 0, v___x_733_);
lean_ctor_set(v___x_737_, 1, v___f_713_);
lean_ctor_set(v___x_737_, 2, v___f_736_);
lean_ctor_set(v___x_737_, 3, v___f_735_);
lean_ctor_set(v___x_737_, 4, v___f_734_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___f_714_);
v___x_739_ = l_StateRefT_x27_instMonad___redArg(v___x_738_);
v_toApplicative_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_739_, 1);
lean_dec(v_unused_799_);
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_798_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_toApplicative_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_798_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_toFunctor_744_; lean_object* v_toSeq_745_; lean_object* v_toSeqLeft_746_; lean_object* v_toSeqRight_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_796_; 
v_toFunctor_744_ = lean_ctor_get(v_toApplicative_740_, 0);
v_toSeq_745_ = lean_ctor_get(v_toApplicative_740_, 2);
v_toSeqLeft_746_ = lean_ctor_get(v_toApplicative_740_, 3);
v_toSeqRight_747_ = lean_ctor_get(v_toApplicative_740_, 4);
v_isSharedCheck_796_ = !lean_is_exclusive(v_toApplicative_740_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_toApplicative_740_, 1);
lean_dec(v_unused_797_);
v___x_749_ = v_toApplicative_740_;
v_isShared_750_ = v_isSharedCheck_796_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_toSeqRight_747_);
lean_inc(v_toSeqLeft_746_);
lean_inc(v_toSeq_745_);
lean_inc(v_toFunctor_744_);
lean_dec(v_toApplicative_740_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_796_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___f_756_; lean_object* v___f_757_; lean_object* v___f_758_; lean_object* v___x_760_; 
v___f_751_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_752_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_744_);
v___f_753_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_753_, 0, v_toFunctor_744_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_754_, 0, v_toFunctor_744_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___f_753_);
lean_ctor_set(v___x_755_, 1, v___f_754_);
v___f_756_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_756_, 0, v_toSeqRight_747_);
v___f_757_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_757_, 0, v_toSeqLeft_746_);
v___f_758_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_758_, 0, v_toSeq_745_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 4, v___f_756_);
lean_ctor_set(v___x_749_, 3, v___f_757_);
lean_ctor_set(v___x_749_, 2, v___f_758_);
lean_ctor_set(v___x_749_, 1, v___f_751_);
lean_ctor_set(v___x_749_, 0, v___x_755_);
v___x_760_ = v___x_749_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___f_751_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v___f_758_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v___f_757_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v___f_756_);
v___x_760_ = v_reuseFailAlloc_795_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___f_752_);
lean_ctor_set(v___x_742_, 0, v___x_760_);
v___x_762_ = v___x_742_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___f_752_);
v___x_762_ = v_reuseFailAlloc_794_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
switch(lean_obj_tag(v_info_704_))
{
case 0:
{
lean_object* v_toBind_763_; lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec_ref(v_info_704_);
lean_dec_ref(v___x_762_);
lean_dec_ref(v___x_725_);
v_toBind_763_ = lean_ctor_get(v_inst_703_, 1);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
lean_inc(v_toBind_763_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_764_, 0, v_resTy_705_);
lean_closure_set(v___f_764_, 1, v_k_706_);
lean_closure_set(v___f_764_, 2, v_inst_701_);
lean_closure_set(v___f_764_, 3, v_toBind_763_);
lean_closure_set(v___f_764_, 4, v_inst_702_);
lean_closure_set(v___f_764_, 5, v_inst_703_);
v___x_765_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_766_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_767_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_702_, v_inst_703_, v___x_765_, v___x_766_, v___f_764_);
return v___x_767_;
}
case 1:
{
lean_object* v_toBind_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref(v_info_704_);
lean_dec_ref(v___x_762_);
lean_dec_ref(v___x_725_);
v_toBind_768_ = lean_ctor_get(v_inst_703_, 1);
lean_inc_ref(v_inst_703_);
lean_inc_ref(v_inst_702_);
lean_inc(v_toBind_768_);
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_769_, 0, v_resTy_705_);
lean_closure_set(v___f_769_, 1, v_k_706_);
lean_closure_set(v___f_769_, 2, v_inst_701_);
lean_closure_set(v___f_769_, 3, v_toBind_768_);
lean_closure_set(v___f_769_, 4, v_inst_702_);
lean_closure_set(v___f_769_, 5, v_inst_703_);
v___x_770_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_771_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_772_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_702_, v_inst_703_, v___x_770_, v___x_771_, v___f_769_);
return v___x_772_;
}
default: 
{
lean_object* v_toApplicative_773_; lean_object* v_matcherApp_774_; lean_object* v_toBind_775_; lean_object* v_toPure_776_; lean_object* v_toMatcherInfo_777_; lean_object* v_matcherName_778_; lean_object* v_matcherLevels_779_; lean_object* v_params_780_; lean_object* v_motive_781_; lean_object* v_discrs_782_; lean_object* v_alts_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_toApplicative_773_ = lean_ctor_get(v_inst_703_, 0);
v_matcherApp_774_ = lean_ctor_get(v_info_704_, 0);
lean_inc_ref(v_matcherApp_774_);
lean_dec_ref(v_info_704_);
v_toBind_775_ = lean_ctor_get(v_inst_703_, 1);
lean_inc_n(v_toBind_775_, 3);
v_toPure_776_ = lean_ctor_get(v_toApplicative_773_, 1);
v_toMatcherInfo_777_ = lean_ctor_get(v_matcherApp_774_, 0);
lean_inc_ref(v_toMatcherInfo_777_);
v_matcherName_778_ = lean_ctor_get(v_matcherApp_774_, 1);
lean_inc(v_matcherName_778_);
v_matcherLevels_779_ = lean_ctor_get(v_matcherApp_774_, 2);
lean_inc_ref(v_matcherLevels_779_);
v_params_780_ = lean_ctor_get(v_matcherApp_774_, 3);
lean_inc_ref(v_params_780_);
v_motive_781_ = lean_ctor_get(v_matcherApp_774_, 4);
lean_inc_ref(v_motive_781_);
v_discrs_782_ = lean_ctor_get(v_matcherApp_774_, 5);
lean_inc_ref(v_discrs_782_);
v_alts_783_ = lean_ctor_get(v_matcherApp_774_, 6);
lean_inc_ref(v_alts_783_);
lean_dec_ref(v_matcherApp_774_);
lean_inc_ref(v_resTy_705_);
v___f_784_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed), 8, 1);
lean_closure_set(v___f_784_, 0, v_resTy_705_);
v___f_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
lean_inc(v_inst_701_);
lean_inc_n(v_toPure_776_, 2);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17), 6, 3);
lean_closure_set(v___f_786_, 0, v_toPure_776_);
lean_closure_set(v___f_786_, 1, v_inst_701_);
lean_closure_set(v___f_786_, 2, v_toBind_775_);
lean_inc_ref_n(v_inst_703_, 2);
lean_inc_ref(v_inst_702_);
v___f_787_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___boxed), 18, 17);
lean_closure_set(v___f_787_, 0, v_toMatcherInfo_777_);
lean_closure_set(v___f_787_, 1, v_matcherName_778_);
lean_closure_set(v___f_787_, 2, v_params_780_);
lean_closure_set(v___f_787_, 3, v_k_706_);
lean_closure_set(v___f_787_, 4, v___x_762_);
lean_closure_set(v___f_787_, 5, v_inst_701_);
lean_closure_set(v___f_787_, 6, v_toBind_775_);
lean_closure_set(v___f_787_, 7, v___f_785_);
lean_closure_set(v___f_787_, 8, v_inst_702_);
lean_closure_set(v___f_787_, 9, v_inst_703_);
lean_closure_set(v___f_787_, 10, v_alts_783_);
lean_closure_set(v___f_787_, 11, v_toPure_776_);
lean_closure_set(v___f_787_, 12, v_matcherLevels_779_);
lean_closure_set(v___f_787_, 13, v_resTy_705_);
lean_closure_set(v___f_787_, 14, v___x_725_);
lean_closure_set(v___f_787_, 15, v_motive_781_);
lean_closure_set(v___f_787_, 16, v___f_784_);
v___f_788_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26), 4, 3);
lean_closure_set(v___f_788_, 0, v_inst_702_);
lean_closure_set(v___f_788_, 1, v_inst_703_);
lean_closure_set(v___f_788_, 2, v___f_787_);
v___x_789_ = lean_array_get_size(v_discrs_782_);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_mk_empty_array_with_capacity(v___x_789_);
v___x_792_ = l_Array_mapFinIdxM_map___redArg(v_inst_703_, v_discrs_782_, v___f_786_, v___x_789_, v___x_790_, v___x_791_);
v___x_793_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v___x_792_, v___f_788_);
return v___x_793_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_800_, lean_object* v_00_u03b1_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_info_806_, lean_object* v_resTy_807_, lean_object* v_k_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_802_, v_inst_803_, v_inst_804_, v_info_806_, v_resTy_807_, v_k_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_810_, lean_object* v_00_u03b1_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_info_816_, lean_object* v_resTy_817_, lean_object* v_k_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_810_, v_00_u03b1_811_, v_inst_812_, v_inst_813_, v_inst_814_, v_inst_815_, v_info_816_, v_resTy_817_, v_k_818_);
lean_dec(v_inst_815_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_820_, lean_object* v_resTy_821_, lean_object* v_c_822_, lean_object* v_h_823_, lean_object* v_t_824_, lean_object* v_toPure_825_, lean_object* v_e_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_827_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_828_ = lean_box(0);
v___x_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_829_, 0, v_u_820_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_mkConst(v___x_827_, v___x_829_);
v___x_831_ = l_Lean_mkApp5(v___x_830_, v_resTy_821_, v_c_822_, v_h_823_, v_t_824_, v_e_826_);
v___x_832_ = lean_apply_2(v_toPure_825_, lean_box(0), v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_836_, lean_object* v_resTy_837_, lean_object* v_c_838_, lean_object* v_h_839_, lean_object* v_toPure_840_, lean_object* v_onAlt_841_, lean_object* v___x_842_, lean_object* v___x_843_, lean_object* v_toBind_844_, lean_object* v_t_845_){
_start:
{
lean_object* v___f_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc_ref(v_resTy_837_);
v___f_846_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_846_, 0, v_u_836_);
lean_closure_set(v___f_846_, 1, v_resTy_837_);
lean_closure_set(v___f_846_, 2, v_c_838_);
lean_closure_set(v___f_846_, 3, v_h_839_);
lean_closure_set(v___f_846_, 4, v_t_845_);
lean_closure_set(v___f_846_, 5, v_toPure_840_);
v___x_847_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_848_ = lean_apply_4(v_onAlt_841_, v___x_847_, v_resTy_837_, v___x_842_, v___x_843_);
v___x_849_ = lean_apply_4(v_toBind_844_, lean_box(0), lean_box(0), v___x_848_, v___f_846_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_850_, uint8_t v_useSplitter_851_, lean_object* v_inst_852_, lean_object* v_____do__lift_853_){
_start:
{
uint8_t v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_854_ = 0;
v___x_855_ = 1;
v___x_856_ = lean_box(v___x_854_);
v___x_857_ = lean_box(v_useSplitter_851_);
v___x_858_ = lean_box(v___x_854_);
v___x_859_ = lean_box(v_useSplitter_851_);
v___x_860_ = lean_box(v___x_855_);
v___x_861_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_861_, 0, v___x_850_);
lean_closure_set(v___x_861_, 1, v_____do__lift_853_);
lean_closure_set(v___x_861_, 2, v___x_856_);
lean_closure_set(v___x_861_, 3, v___x_857_);
lean_closure_set(v___x_861_, 4, v___x_858_);
lean_closure_set(v___x_861_, 5, v___x_859_);
lean_closure_set(v___x_861_, 6, v___x_860_);
v___x_862_ = lean_apply_2(v_inst_852_, lean_box(0), v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_863_, lean_object* v_useSplitter_864_, lean_object* v_inst_865_, lean_object* v_____do__lift_866_){
_start:
{
uint8_t v_useSplitter_boxed_867_; lean_object* v_res_868_; 
v_useSplitter_boxed_867_ = lean_unbox(v_useSplitter_864_);
v_res_868_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_863_, v_useSplitter_boxed_867_, v_inst_865_, v_____do__lift_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_872_, uint8_t v_useSplitter_873_, lean_object* v_inst_874_, lean_object* v_onAlt_875_, lean_object* v_resTy_876_, lean_object* v_toBind_877_, lean_object* v_h_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___f_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_879_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
v___x_882_ = lean_mk_empty_array_with_capacity(v___x_872_);
v___x_883_ = lean_array_push(v___x_882_, v_h_878_);
v___x_884_ = lean_box(v_useSplitter_873_);
lean_inc_ref(v___x_883_);
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_885_, 0, v___x_883_);
lean_closure_set(v___f_885_, 1, v___x_884_);
lean_closure_set(v___f_885_, 2, v_inst_874_);
v___x_886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_886_, 0, v___x_881_);
lean_ctor_set(v___x_886_, 1, v___x_883_);
lean_ctor_set(v___x_886_, 2, v___x_881_);
lean_ctor_set(v___x_886_, 3, v___x_881_);
lean_ctor_set(v___x_886_, 4, v___x_881_);
v___x_887_ = lean_apply_4(v_onAlt_875_, v___x_879_, v_resTy_876_, v___x_880_, v___x_886_);
v___x_888_ = lean_apply_4(v_toBind_877_, lean_box(0), lean_box(0), v___x_887_, v___f_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_889_, lean_object* v_useSplitter_890_, lean_object* v_inst_891_, lean_object* v_onAlt_892_, lean_object* v_resTy_893_, lean_object* v_toBind_894_, lean_object* v_h_895_){
_start:
{
uint8_t v_useSplitter_boxed_896_; lean_object* v_res_897_; 
v_useSplitter_boxed_896_ = lean_unbox(v_useSplitter_890_);
v_res_897_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_889_, v_useSplitter_boxed_896_, v_inst_891_, v_onAlt_892_, v_resTy_893_, v_toBind_894_, v_h_895_);
lean_dec(v___x_889_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_898_, uint8_t v_useSplitter_899_, lean_object* v_inst_900_, lean_object* v_onAlt_901_, lean_object* v_resTy_902_, lean_object* v_toBind_903_, lean_object* v_h_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_905_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_906_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
v___x_907_ = lean_mk_empty_array_with_capacity(v___x_898_);
v___x_908_ = lean_array_push(v___x_907_, v_h_904_);
v___x_909_ = lean_box(v_useSplitter_899_);
lean_inc_ref(v___x_908_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_910_, 0, v___x_908_);
lean_closure_set(v___f_910_, 1, v___x_909_);
lean_closure_set(v___f_910_, 2, v_inst_900_);
v___x_911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_908_);
lean_ctor_set(v___x_911_, 2, v___x_906_);
lean_ctor_set(v___x_911_, 3, v___x_906_);
lean_ctor_set(v___x_911_, 4, v___x_906_);
v___x_912_ = lean_apply_4(v_onAlt_901_, v___x_905_, v_resTy_902_, v___x_898_, v___x_911_);
v___x_913_ = lean_apply_4(v_toBind_903_, lean_box(0), lean_box(0), v___x_912_, v___f_910_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_914_, lean_object* v_useSplitter_915_, lean_object* v_inst_916_, lean_object* v_onAlt_917_, lean_object* v_resTy_918_, lean_object* v_toBind_919_, lean_object* v_h_920_){
_start:
{
uint8_t v_useSplitter_boxed_921_; lean_object* v_res_922_; 
v_useSplitter_boxed_921_ = lean_unbox(v_useSplitter_915_);
v_res_922_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_914_, v_useSplitter_boxed_921_, v_inst_916_, v_onAlt_917_, v_resTy_918_, v_toBind_919_, v_h_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_923_, lean_object* v_resTy_924_, lean_object* v_c_925_, lean_object* v_h_926_, lean_object* v_t_927_, lean_object* v_toPure_928_, lean_object* v_e_929_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_930_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_932_, 0, v_u_923_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = l_Lean_mkConst(v___x_930_, v___x_932_);
v___x_934_ = l_Lean_mkApp5(v___x_933_, v_resTy_924_, v_c_925_, v_h_926_, v_t_927_, v_e_929_);
v___x_935_ = lean_apply_2(v_toPure_928_, lean_box(0), v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_936_, lean_object* v_resTy_937_, lean_object* v_c_938_, lean_object* v_h_939_, lean_object* v_toPure_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_n_943_, uint8_t v___x_944_, lean_object* v___f_945_, uint8_t v___x_946_, lean_object* v_toBind_947_, lean_object* v_t_948_){
_start:
{
lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_inc_ref(v_c_938_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_949_, 0, v_u_936_);
lean_closure_set(v___f_949_, 1, v_resTy_937_);
lean_closure_set(v___f_949_, 2, v_c_938_);
lean_closure_set(v___f_949_, 3, v_h_939_);
lean_closure_set(v___f_949_, 4, v_t_948_);
lean_closure_set(v___f_949_, 5, v_toPure_940_);
v___x_950_ = l_Lean_mkNot(v_c_938_);
v___x_951_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_941_, v_inst_942_, v_n_943_, v___x_944_, v___x_950_, v___f_945_, v___x_946_);
v___x_952_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_951_, v___f_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_953_, lean_object* v_resTy_954_, lean_object* v_c_955_, lean_object* v_h_956_, lean_object* v_toPure_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_n_960_, lean_object* v___x_961_, lean_object* v___f_962_, lean_object* v___x_963_, lean_object* v_toBind_964_, lean_object* v_t_965_){
_start:
{
uint8_t v___x_1249__boxed_966_; uint8_t v___x_1251__boxed_967_; lean_object* v_res_968_; 
v___x_1249__boxed_966_ = lean_unbox(v___x_961_);
v___x_1251__boxed_967_ = lean_unbox(v___x_963_);
v_res_968_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_953_, v_resTy_954_, v_c_955_, v_h_956_, v_toPure_957_, v_inst_958_, v_inst_959_, v_n_960_, v___x_1249__boxed_966_, v___f_962_, v___x_1251__boxed_967_, v_toBind_964_, v_t_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_969_, lean_object* v_resTy_970_, lean_object* v_c_971_, lean_object* v_h_972_, lean_object* v_toPure_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v___f_976_, lean_object* v_toBind_977_, lean_object* v___f_978_, lean_object* v_n_979_){
_start:
{
uint8_t v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_980_ = 0;
v___x_981_ = 0;
v___x_982_ = lean_box(v___x_980_);
v___x_983_ = lean_box(v___x_981_);
lean_inc(v_toBind_977_);
lean_inc(v_n_979_);
lean_inc_ref(v_inst_975_);
lean_inc_ref(v_inst_974_);
lean_inc_ref(v_c_971_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_984_, 0, v_u_969_);
lean_closure_set(v___f_984_, 1, v_resTy_970_);
lean_closure_set(v___f_984_, 2, v_c_971_);
lean_closure_set(v___f_984_, 3, v_h_972_);
lean_closure_set(v___f_984_, 4, v_toPure_973_);
lean_closure_set(v___f_984_, 5, v_inst_974_);
lean_closure_set(v___f_984_, 6, v_inst_975_);
lean_closure_set(v___f_984_, 7, v_n_979_);
lean_closure_set(v___f_984_, 8, v___x_982_);
lean_closure_set(v___f_984_, 9, v___f_976_);
lean_closure_set(v___f_984_, 10, v___x_983_);
lean_closure_set(v___f_984_, 11, v_toBind_977_);
v___x_985_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_974_, v_inst_975_, v_n_979_, v___x_980_, v_c_971_, v___f_978_, v___x_981_);
v___x_986_ = lean_apply_4(v_toBind_977_, lean_box(0), lean_box(0), v___x_985_, v___f_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Core_mkFreshUserName(v___x_987_, v___y_990_, v___y_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1008_, uint8_t v_useSplitter_1009_, lean_object* v_resTy_1010_, lean_object* v_toPure_1011_, lean_object* v_onAlt_1012_, lean_object* v_toBind_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_u_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_c_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_h_1026_; 
v___x_1018_ = lean_unsigned_to_nat(1u);
v___x_1019_ = l_Lean_Expr_getAppNumArgs(v_e_1008_);
v___x_1020_ = lean_nat_sub(v___x_1019_, v___x_1018_);
v___x_1021_ = lean_nat_sub(v___x_1020_, v___x_1018_);
lean_dec(v___x_1020_);
v_c_1022_ = l_Lean_Expr_getRevArg_x21(v_e_1008_, v___x_1021_);
v___x_1023_ = lean_unsigned_to_nat(2u);
v___x_1024_ = lean_nat_sub(v___x_1019_, v___x_1023_);
lean_dec(v___x_1019_);
v___x_1025_ = lean_nat_sub(v___x_1024_, v___x_1018_);
lean_dec(v___x_1024_);
v_h_1026_ = l_Lean_Expr_getRevArg_x21(v_e_1008_, v___x_1025_);
if (v_useSplitter_1009_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_inst_1016_);
lean_dec_ref(v_inst_1015_);
lean_dec(v_inst_1014_);
v___x_1027_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1013_);
lean_inc(v_onAlt_1012_);
lean_inc_ref(v_resTy_1010_);
v___f_1030_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1030_, 0, v_u_1017_);
lean_closure_set(v___f_1030_, 1, v_resTy_1010_);
lean_closure_set(v___f_1030_, 2, v_c_1022_);
lean_closure_set(v___f_1030_, 3, v_h_1026_);
lean_closure_set(v___f_1030_, 4, v_toPure_1011_);
lean_closure_set(v___f_1030_, 5, v_onAlt_1012_);
lean_closure_set(v___f_1030_, 6, v___x_1018_);
lean_closure_set(v___f_1030_, 7, v___x_1029_);
lean_closure_set(v___f_1030_, 8, v_toBind_1013_);
v___x_1031_ = lean_apply_4(v_onAlt_1012_, v___x_1027_, v_resTy_1010_, v___x_1028_, v___x_1029_);
v___x_1032_ = lean_apply_4(v_toBind_1013_, lean_box(0), lean_box(0), v___x_1031_, v___f_1030_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1033_ = lean_box(v_useSplitter_1009_);
lean_inc_n(v_toBind_1013_, 3);
lean_inc_ref_n(v_resTy_1010_, 2);
lean_inc(v_onAlt_1012_);
lean_inc_n(v_inst_1014_, 2);
v___f_1034_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1034_, 0, v___x_1018_);
lean_closure_set(v___f_1034_, 1, v___x_1033_);
lean_closure_set(v___f_1034_, 2, v_inst_1014_);
lean_closure_set(v___f_1034_, 3, v_onAlt_1012_);
lean_closure_set(v___f_1034_, 4, v_resTy_1010_);
lean_closure_set(v___f_1034_, 5, v_toBind_1013_);
v___x_1035_ = lean_box(v_useSplitter_1009_);
v___f_1036_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1036_, 0, v___x_1018_);
lean_closure_set(v___f_1036_, 1, v___x_1035_);
lean_closure_set(v___f_1036_, 2, v_inst_1014_);
lean_closure_set(v___f_1036_, 3, v_onAlt_1012_);
lean_closure_set(v___f_1036_, 4, v_resTy_1010_);
lean_closure_set(v___f_1036_, 5, v_toBind_1013_);
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1037_, 0, v_u_1017_);
lean_closure_set(v___f_1037_, 1, v_resTy_1010_);
lean_closure_set(v___f_1037_, 2, v_c_1022_);
lean_closure_set(v___f_1037_, 3, v_h_1026_);
lean_closure_set(v___f_1037_, 4, v_toPure_1011_);
lean_closure_set(v___f_1037_, 5, v_inst_1015_);
lean_closure_set(v___f_1037_, 6, v_inst_1016_);
lean_closure_set(v___f_1037_, 7, v___f_1036_);
lean_closure_set(v___f_1037_, 8, v_toBind_1013_);
lean_closure_set(v___f_1037_, 9, v___f_1034_);
v___f_1038_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1039_ = lean_apply_2(v_inst_1014_, lean_box(0), v___f_1038_);
v___x_1040_ = lean_apply_4(v_toBind_1013_, lean_box(0), lean_box(0), v___x_1039_, v___f_1037_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1041_, lean_object* v_useSplitter_1042_, lean_object* v_resTy_1043_, lean_object* v_toPure_1044_, lean_object* v_onAlt_1045_, lean_object* v_toBind_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_u_1050_){
_start:
{
uint8_t v_useSplitter_boxed_1051_; lean_object* v_res_1052_; 
v_useSplitter_boxed_1051_ = lean_unbox(v_useSplitter_1042_);
v_res_1052_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1041_, v_useSplitter_boxed_1051_, v_resTy_1043_, v_toPure_1044_, v_onAlt_1045_, v_toBind_1046_, v_inst_1047_, v_inst_1048_, v_inst_1049_, v_u_1050_);
lean_dec_ref(v_e_1041_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1053_, lean_object* v_inst_1054_, lean_object* v_____do__lift_1055_){
_start:
{
uint8_t v___x_1056_; uint8_t v___x_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1056_ = 0;
v___x_1057_ = 1;
v___x_1058_ = 1;
v___x_1059_ = lean_box(v___x_1056_);
v___x_1060_ = lean_box(v___x_1057_);
v___x_1061_ = lean_box(v___x_1056_);
v___x_1062_ = lean_box(v___x_1057_);
v___x_1063_ = lean_box(v___x_1058_);
v___x_1064_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1064_, 0, v___x_1053_);
lean_closure_set(v___x_1064_, 1, v_____do__lift_1055_);
lean_closure_set(v___x_1064_, 2, v___x_1059_);
lean_closure_set(v___x_1064_, 3, v___x_1060_);
lean_closure_set(v___x_1064_, 4, v___x_1061_);
lean_closure_set(v___x_1064_, 5, v___x_1062_);
lean_closure_set(v___x_1064_, 6, v___x_1063_);
v___x_1065_ = lean_apply_2(v_inst_1054_, lean_box(0), v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1066_, lean_object* v_onAlt_1067_, lean_object* v_resTy_1068_, lean_object* v_toBind_1069_, lean_object* v_h_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = lean_mk_empty_array_with_capacity(v___x_1073_);
v___x_1075_ = lean_array_push(v___x_1074_, v_h_1070_);
lean_inc_ref_n(v___x_1075_, 2);
v___f_1076_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1076_, 0, v___x_1075_);
lean_closure_set(v___f_1076_, 1, v_inst_1066_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
v___x_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1075_);
lean_ctor_set(v___x_1078_, 1, v___x_1075_);
lean_ctor_set(v___x_1078_, 2, v___x_1077_);
lean_ctor_set(v___x_1078_, 3, v___x_1077_);
lean_ctor_set(v___x_1078_, 4, v___x_1077_);
v___x_1079_ = lean_apply_4(v_onAlt_1067_, v___x_1071_, v_resTy_1068_, v___x_1072_, v___x_1078_);
v___x_1080_ = lean_apply_4(v_toBind_1069_, lean_box(0), lean_box(0), v___x_1079_, v___f_1076_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1081_, lean_object* v_inst_1082_, lean_object* v_onAlt_1083_, lean_object* v_resTy_1084_, lean_object* v_toBind_1085_, lean_object* v_h_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1088_ = lean_mk_empty_array_with_capacity(v___x_1081_);
v___x_1089_ = lean_array_push(v___x_1088_, v_h_1086_);
lean_inc_ref_n(v___x_1089_, 2);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1090_, 0, v___x_1089_);
lean_closure_set(v___f_1090_, 1, v_inst_1082_);
v___x_1091_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0));
v___x_1092_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1089_);
lean_ctor_set(v___x_1092_, 1, v___x_1089_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
lean_ctor_set(v___x_1092_, 3, v___x_1091_);
lean_ctor_set(v___x_1092_, 4, v___x_1091_);
v___x_1093_ = lean_apply_4(v_onAlt_1083_, v___x_1087_, v_resTy_1084_, v___x_1081_, v___x_1092_);
v___x_1094_ = lean_apply_4(v_toBind_1085_, lean_box(0), lean_box(0), v___x_1093_, v___f_1090_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1095_, lean_object* v_onAlt_1096_, lean_object* v_resTy_1097_, lean_object* v_toBind_1098_, lean_object* v_e_1099_, lean_object* v_toPure_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v___f_1103_, lean_object* v_u_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_c_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_h_1114_; lean_object* v___f_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1105_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_toBind_1098_, 2);
lean_inc_ref(v_resTy_1097_);
lean_inc(v_inst_1095_);
v___f_1106_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1106_, 0, v___x_1105_);
lean_closure_set(v___f_1106_, 1, v_inst_1095_);
lean_closure_set(v___f_1106_, 2, v_onAlt_1096_);
lean_closure_set(v___f_1106_, 3, v_resTy_1097_);
lean_closure_set(v___f_1106_, 4, v_toBind_1098_);
v___x_1107_ = l_Lean_Expr_getAppNumArgs(v_e_1099_);
v___x_1108_ = lean_nat_sub(v___x_1107_, v___x_1105_);
v___x_1109_ = lean_nat_sub(v___x_1108_, v___x_1105_);
lean_dec(v___x_1108_);
v_c_1110_ = l_Lean_Expr_getRevArg_x21(v_e_1099_, v___x_1109_);
v___x_1111_ = lean_unsigned_to_nat(2u);
v___x_1112_ = lean_nat_sub(v___x_1107_, v___x_1111_);
lean_dec(v___x_1107_);
v___x_1113_ = lean_nat_sub(v___x_1112_, v___x_1105_);
lean_dec(v___x_1112_);
v_h_1114_ = l_Lean_Expr_getRevArg_x21(v_e_1099_, v___x_1113_);
v___f_1115_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1115_, 0, v_u_1104_);
lean_closure_set(v___f_1115_, 1, v_resTy_1097_);
lean_closure_set(v___f_1115_, 2, v_c_1110_);
lean_closure_set(v___f_1115_, 3, v_h_1114_);
lean_closure_set(v___f_1115_, 4, v_toPure_1100_);
lean_closure_set(v___f_1115_, 5, v_inst_1101_);
lean_closure_set(v___f_1115_, 6, v_inst_1102_);
lean_closure_set(v___f_1115_, 7, v___f_1106_);
lean_closure_set(v___f_1115_, 8, v_toBind_1098_);
lean_closure_set(v___f_1115_, 9, v___f_1103_);
v___f_1116_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1117_ = lean_apply_2(v_inst_1095_, lean_box(0), v___f_1116_);
v___x_1118_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v___x_1117_, v___f_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1119_, lean_object* v_onAlt_1120_, lean_object* v_resTy_1121_, lean_object* v_toBind_1122_, lean_object* v_e_1123_, lean_object* v_toPure_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v___f_1127_, lean_object* v_u_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1119_, v_onAlt_1120_, v_resTy_1121_, v_toBind_1122_, v_e_1123_, v_toPure_1124_, v_inst_1125_, v_inst_1126_, v___f_1127_, v_u_1128_);
lean_dec_ref(v_e_1123_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_onAlt_1130_, lean_object* v_idx_1131_, lean_object* v_expAltType_1132_, lean_object* v_altFVars_1133_, lean_object* v___alt_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1135_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_add(v_idx_1131_, v___x_1136_);
v___x_1138_ = lean_name_append_index_after(v___x_1135_, v___x_1137_);
v___x_1139_ = lean_apply_4(v_onAlt_1130_, v___x_1138_, v_expAltType_1132_, v_idx_1131_, v_altFVars_1133_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(lean_object* v_onAlt_1140_, lean_object* v_idx_1141_, lean_object* v_expAltType_1142_, lean_object* v_altFVars_1143_, lean_object* v___alt_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(v_onAlt_1140_, v_idx_1141_, v_expAltType_1142_, v_altFVars_1143_, v___alt_1144_);
lean_dec_ref(v___alt_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_mask_1146_, lean_object* v_absMotiveBody_1147_, lean_object* v_toPure_1148_, lean_object* v_xs_1149_, lean_object* v___body_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = l_Array_mask___redArg(v_mask_1146_, v_xs_1149_);
v___x_1152_ = lean_expr_instantiate_rev(v_absMotiveBody_1147_, v___x_1151_);
lean_dec(v___x_1151_);
v___x_1153_ = lean_apply_2(v_toPure_1148_, lean_box(0), v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(lean_object* v_mask_1154_, lean_object* v_absMotiveBody_1155_, lean_object* v_toPure_1156_, lean_object* v_xs_1157_, lean_object* v___body_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(v_mask_1154_, v_absMotiveBody_1155_, v_toPure_1156_, v_xs_1157_, v___body_1158_);
lean_dec_ref(v___body_1158_);
lean_dec_ref(v_absMotiveBody_1155_);
lean_dec_ref(v_mask_1154_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v_toFunctor_1160_, lean_object* v_mask_1161_, lean_object* v_toPure_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_, lean_object* v_matcherApp_1168_, uint8_t v_useSplitter_1169_, lean_object* v___f_1170_, lean_object* v___f_1171_, lean_object* v_absMotiveBody_1172_){
_start:
{
lean_object* v_map_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_map_1173_ = lean_ctor_get(v_toFunctor_1160_, 0);
lean_inc(v_map_1173_);
lean_dec_ref(v_toFunctor_1160_);
lean_inc(v_toPure_1162_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_1174_, 0, v_mask_1161_);
lean_closure_set(v___f_1174_, 1, v_absMotiveBody_1172_);
lean_closure_set(v___f_1174_, 2, v_toPure_1162_);
v___x_1175_ = lean_apply_1(v_toPure_1162_, lean_box(0));
lean_inc(v___x_1175_);
v___x_1176_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v_inst_1167_, v_matcherApp_1168_, v_useSplitter_1169_, v_useSplitter_1169_, v___x_1175_, v___f_1174_, v___f_1170_, v___x_1175_);
v___x_1177_ = lean_apply_4(v_map_1173_, lean_box(0), lean_box(0), v___f_1171_, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v_toFunctor_1178_, lean_object* v_mask_1179_, lean_object* v_toPure_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_matcherApp_1186_, lean_object* v_useSplitter_1187_, lean_object* v___f_1188_, lean_object* v___f_1189_, lean_object* v_absMotiveBody_1190_){
_start:
{
uint8_t v_useSplitter_boxed_1191_; lean_object* v_res_1192_; 
v_useSplitter_boxed_1191_ = lean_unbox(v_useSplitter_1187_);
v_res_1192_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v_toFunctor_1178_, v_mask_1179_, v_toPure_1180_, v_inst_1181_, v_inst_1182_, v_inst_1183_, v_inst_1184_, v_inst_1185_, v_matcherApp_1186_, v_useSplitter_boxed_1191_, v___f_1188_, v___f_1189_, v_absMotiveBody_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_info_1200_, lean_object* v_resTy_1201_, lean_object* v_onAlt_1202_, uint8_t v_useSplitter_1203_){
_start:
{
switch(lean_obj_tag(v_info_1200_))
{
case 0:
{
lean_object* v_toApplicative_1204_; lean_object* v_toBind_1205_; lean_object* v_toPure_1206_; lean_object* v_e_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_toApplicative_1204_ = lean_ctor_get(v_inst_1197_, 0);
lean_dec_ref(v_inst_1199_);
lean_dec_ref(v_inst_1198_);
v_toBind_1205_ = lean_ctor_get(v_inst_1197_, 1);
lean_inc_n(v_toBind_1205_, 2);
v_toPure_1206_ = lean_ctor_get(v_toApplicative_1204_, 1);
lean_inc(v_toPure_1206_);
v_e_1207_ = lean_ctor_get(v_info_1200_, 0);
lean_inc_ref(v_e_1207_);
lean_dec_ref(v_info_1200_);
v___x_1208_ = lean_box(v_useSplitter_1203_);
lean_inc(v_inst_1195_);
lean_inc_ref(v_resTy_1201_);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1209_, 0, v_e_1207_);
lean_closure_set(v___f_1209_, 1, v___x_1208_);
lean_closure_set(v___f_1209_, 2, v_resTy_1201_);
lean_closure_set(v___f_1209_, 3, v_toPure_1206_);
lean_closure_set(v___f_1209_, 4, v_onAlt_1202_);
lean_closure_set(v___f_1209_, 5, v_toBind_1205_);
lean_closure_set(v___f_1209_, 6, v_inst_1195_);
lean_closure_set(v___f_1209_, 7, v_inst_1196_);
lean_closure_set(v___f_1209_, 8, v_inst_1197_);
v___x_1210_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1210_, 0, v_resTy_1201_);
v___x_1211_ = lean_apply_2(v_inst_1195_, lean_box(0), v___x_1210_);
v___x_1212_ = lean_apply_4(v_toBind_1205_, lean_box(0), lean_box(0), v___x_1211_, v___f_1209_);
return v___x_1212_;
}
case 1:
{
lean_object* v_toApplicative_1213_; lean_object* v_toBind_1214_; lean_object* v_toPure_1215_; lean_object* v_e_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_toApplicative_1213_ = lean_ctor_get(v_inst_1197_, 0);
lean_dec_ref(v_inst_1199_);
lean_dec_ref(v_inst_1198_);
v_toBind_1214_ = lean_ctor_get(v_inst_1197_, 1);
lean_inc_n(v_toBind_1214_, 3);
v_toPure_1215_ = lean_ctor_get(v_toApplicative_1213_, 1);
lean_inc(v_toPure_1215_);
v_e_1216_ = lean_ctor_get(v_info_1200_, 0);
lean_inc_ref(v_e_1216_);
lean_dec_ref(v_info_1200_);
lean_inc_ref_n(v_resTy_1201_, 2);
lean_inc(v_onAlt_1202_);
lean_inc_n(v_inst_1195_, 2);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1217_, 0, v_inst_1195_);
lean_closure_set(v___f_1217_, 1, v_onAlt_1202_);
lean_closure_set(v___f_1217_, 2, v_resTy_1201_);
lean_closure_set(v___f_1217_, 3, v_toBind_1214_);
v___f_1218_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1218_, 0, v_inst_1195_);
lean_closure_set(v___f_1218_, 1, v_onAlt_1202_);
lean_closure_set(v___f_1218_, 2, v_resTy_1201_);
lean_closure_set(v___f_1218_, 3, v_toBind_1214_);
lean_closure_set(v___f_1218_, 4, v_e_1216_);
lean_closure_set(v___f_1218_, 5, v_toPure_1215_);
lean_closure_set(v___f_1218_, 6, v_inst_1196_);
lean_closure_set(v___f_1218_, 7, v_inst_1197_);
lean_closure_set(v___f_1218_, 8, v___f_1217_);
v___x_1219_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1219_, 0, v_resTy_1201_);
v___x_1220_ = lean_apply_2(v_inst_1195_, lean_box(0), v___x_1219_);
v___x_1221_ = lean_apply_4(v_toBind_1214_, lean_box(0), lean_box(0), v___x_1220_, v___f_1218_);
return v___x_1221_;
}
default: 
{
lean_object* v_toApplicative_1222_; lean_object* v_matcherApp_1223_; lean_object* v_toBind_1224_; lean_object* v_toFunctor_1225_; lean_object* v_toPure_1226_; lean_object* v_discrs_1227_; lean_object* v___f_1228_; lean_object* v___f_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; size_t v_sz_1232_; size_t v___x_1233_; lean_object* v_mask_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v_maskedDiscrs_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_toApplicative_1222_ = lean_ctor_get(v_inst_1197_, 0);
v_matcherApp_1223_ = lean_ctor_get(v_info_1200_, 0);
lean_inc_ref(v_matcherApp_1223_);
lean_dec_ref(v_info_1200_);
v_toBind_1224_ = lean_ctor_get(v_inst_1197_, 1);
lean_inc(v_toBind_1224_);
v_toFunctor_1225_ = lean_ctor_get(v_toApplicative_1222_, 0);
lean_inc_ref(v_toFunctor_1225_);
v_toPure_1226_ = lean_ctor_get(v_toApplicative_1222_, 1);
lean_inc(v_toPure_1226_);
v_discrs_1227_ = lean_ctor_get(v_matcherApp_1223_, 5);
lean_inc_ref_n(v_discrs_1227_, 2);
v___f_1228_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed), 5, 1);
lean_closure_set(v___f_1229_, 0, v_onAlt_1202_);
v___f_1230_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1));
v___x_1231_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9));
v_sz_1232_ = lean_array_size(v_discrs_1227_);
v___x_1233_ = ((size_t)0ULL);
v_mask_1234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1231_, v___f_1230_, v_sz_1232_, v___x_1233_, v_discrs_1227_);
v___x_1235_ = lean_box(v_useSplitter_1203_);
lean_inc(v_inst_1195_);
lean_inc(v_mask_1234_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 13, 12);
lean_closure_set(v___f_1236_, 0, v_toFunctor_1225_);
lean_closure_set(v___f_1236_, 1, v_mask_1234_);
lean_closure_set(v___f_1236_, 2, v_toPure_1226_);
lean_closure_set(v___f_1236_, 3, v_inst_1195_);
lean_closure_set(v___f_1236_, 4, v_inst_1196_);
lean_closure_set(v___f_1236_, 5, v_inst_1197_);
lean_closure_set(v___f_1236_, 6, v_inst_1198_);
lean_closure_set(v___f_1236_, 7, v_inst_1199_);
lean_closure_set(v___f_1236_, 8, v_matcherApp_1223_);
lean_closure_set(v___f_1236_, 9, v___x_1235_);
lean_closure_set(v___f_1236_, 10, v___f_1229_);
lean_closure_set(v___f_1236_, 11, v___f_1228_);
v_maskedDiscrs_1237_ = l_Array_mask___redArg(v_mask_1234_, v_discrs_1227_);
lean_dec(v_mask_1234_);
v___x_1238_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1238_, 0, v_resTy_1201_);
lean_closure_set(v___x_1238_, 1, v_maskedDiscrs_1237_);
v___x_1239_ = lean_apply_2(v_inst_1195_, lean_box(0), v___x_1238_);
v___x_1240_ = lean_apply_4(v_toBind_1224_, lean_box(0), lean_box(0), v___x_1239_, v___f_1236_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_info_1246_, lean_object* v_resTy_1247_, lean_object* v_onAlt_1248_, lean_object* v_useSplitter_1249_){
_start:
{
uint8_t v_useSplitter_boxed_1250_; lean_object* v_res_1251_; 
v_useSplitter_boxed_1250_ = lean_unbox(v_useSplitter_1249_);
v_res_1251_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1241_, v_inst_1242_, v_inst_1243_, v_inst_1244_, v_inst_1245_, v_info_1246_, v_resTy_1247_, v_onAlt_1248_, v_useSplitter_boxed_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_info_1261_, lean_object* v_resTy_1262_, lean_object* v_onAlt_1263_, uint8_t v_useSplitter_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1253_, v_inst_1254_, v_inst_1255_, v_inst_1256_, v_inst_1257_, v_info_1261_, v_resTy_1262_, v_onAlt_1263_, v_useSplitter_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_info_1275_, lean_object* v_resTy_1276_, lean_object* v_onAlt_1277_, lean_object* v_useSplitter_1278_){
_start:
{
uint8_t v_useSplitter_boxed_1279_; lean_object* v_res_1280_; 
v_useSplitter_boxed_1279_ = lean_unbox(v_useSplitter_1278_);
v_res_1280_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1266_, v_inst_1267_, v_inst_1268_, v_inst_1269_, v_inst_1270_, v_inst_1271_, v_inst_1272_, v_inst_1273_, v_inst_1274_, v_info_1275_, v_resTy_1276_, v_onAlt_1277_, v_useSplitter_boxed_1279_);
lean_dec(v_inst_1274_);
lean_dec(v_inst_1273_);
lean_dec_ref(v_inst_1272_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1281_, lean_object* v_e_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
if (lean_obj_tag(v_info_1281_) == 2)
{
lean_object* v_matcherApp_1291_; lean_object* v_toMatcherInfo_1292_; lean_object* v___x_1293_; 
v_matcherApp_1291_ = lean_ctor_get(v_info_1281_, 0);
lean_inc_ref(v_matcherApp_1291_);
lean_dec_ref(v_info_1281_);
v_toMatcherInfo_1292_ = lean_ctor_get(v_matcherApp_1291_, 0);
lean_inc_ref(v_toMatcherInfo_1292_);
lean_dec_ref(v_matcherApp_1291_);
v___x_1293_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1292_, v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec_ref(v_e_1282_);
lean_dec_ref(v_info_1281_);
v___x_1294_ = lean_box(0);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1296_, lean_object* v_e_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1296_, v_e_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v_env_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1310_ = lean_st_ref_get(v___y_1308_);
v_env_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc_ref(v_env_1311_);
lean_dec(v___x_1310_);
v___x_1312_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1311_, v_declName_1307_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1314_, v___y_1315_);
lean_dec(v___y_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v_env_1325_; lean_object* v___x_1326_; lean_object* v_mctx_1327_; lean_object* v_lctx_1328_; lean_object* v_options_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1324_ = lean_st_ref_get(v___y_1322_);
v_env_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_env_1325_);
lean_dec(v___x_1324_);
v___x_1326_ = lean_st_ref_get(v___y_1320_);
v_mctx_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc_ref(v_mctx_1327_);
lean_dec(v___x_1326_);
v_lctx_1328_ = lean_ctor_get(v___y_1319_, 2);
v_options_1329_ = lean_ctor_get(v___y_1321_, 2);
lean_inc_ref(v_options_1329_);
lean_inc_ref(v_lctx_1328_);
v___x_1330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1330_, 0, v_env_1325_);
lean_ctor_set(v___x_1330_, 1, v_mctx_1327_);
lean_ctor_set(v___x_1330_, 2, v_lctx_1328_);
lean_ctor_set(v___x_1330_, 3, v_options_1329_);
v___x_1331_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v_msgData_1318_);
v___x_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_ref_1346_; lean_object* v___x_1347_; lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1356_; 
v_ref_1346_ = lean_ctor_get(v___y_1343_, 5);
v___x_1347_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1356_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
lean_inc(v_ref_1346_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_ref_1346_);
lean_ctor_set(v___x_1352_, 1, v_a_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set_tag(v___x_1350_, 1);
lean_ctor_set(v___x_1350_, 0, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_1364_, lean_object* v_msg_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_fileName_1371_; lean_object* v_fileMap_1372_; lean_object* v_options_1373_; lean_object* v_currRecDepth_1374_; lean_object* v_maxRecDepth_1375_; lean_object* v_ref_1376_; lean_object* v_currNamespace_1377_; lean_object* v_openDecls_1378_; lean_object* v_initHeartbeats_1379_; lean_object* v_maxHeartbeats_1380_; lean_object* v_quotContext_1381_; lean_object* v_currMacroScope_1382_; uint8_t v_diag_1383_; lean_object* v_cancelTk_x3f_1384_; uint8_t v_suppressElabErrors_1385_; lean_object* v_inheritedTraceOptions_1386_; lean_object* v_ref_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v_fileName_1371_ = lean_ctor_get(v___y_1368_, 0);
v_fileMap_1372_ = lean_ctor_get(v___y_1368_, 1);
v_options_1373_ = lean_ctor_get(v___y_1368_, 2);
v_currRecDepth_1374_ = lean_ctor_get(v___y_1368_, 3);
v_maxRecDepth_1375_ = lean_ctor_get(v___y_1368_, 4);
v_ref_1376_ = lean_ctor_get(v___y_1368_, 5);
v_currNamespace_1377_ = lean_ctor_get(v___y_1368_, 6);
v_openDecls_1378_ = lean_ctor_get(v___y_1368_, 7);
v_initHeartbeats_1379_ = lean_ctor_get(v___y_1368_, 8);
v_maxHeartbeats_1380_ = lean_ctor_get(v___y_1368_, 9);
v_quotContext_1381_ = lean_ctor_get(v___y_1368_, 10);
v_currMacroScope_1382_ = lean_ctor_get(v___y_1368_, 11);
v_diag_1383_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*14);
v_cancelTk_x3f_1384_ = lean_ctor_get(v___y_1368_, 12);
v_suppressElabErrors_1385_ = lean_ctor_get_uint8(v___y_1368_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1386_ = lean_ctor_get(v___y_1368_, 13);
v_ref_1387_ = l_Lean_replaceRef(v_ref_1364_, v_ref_1376_);
lean_inc_ref(v_inheritedTraceOptions_1386_);
lean_inc(v_cancelTk_x3f_1384_);
lean_inc(v_currMacroScope_1382_);
lean_inc(v_quotContext_1381_);
lean_inc(v_maxHeartbeats_1380_);
lean_inc(v_initHeartbeats_1379_);
lean_inc(v_openDecls_1378_);
lean_inc(v_currNamespace_1377_);
lean_inc(v_maxRecDepth_1375_);
lean_inc(v_currRecDepth_1374_);
lean_inc_ref(v_options_1373_);
lean_inc_ref(v_fileMap_1372_);
lean_inc_ref(v_fileName_1371_);
v___x_1388_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1388_, 0, v_fileName_1371_);
lean_ctor_set(v___x_1388_, 1, v_fileMap_1372_);
lean_ctor_set(v___x_1388_, 2, v_options_1373_);
lean_ctor_set(v___x_1388_, 3, v_currRecDepth_1374_);
lean_ctor_set(v___x_1388_, 4, v_maxRecDepth_1375_);
lean_ctor_set(v___x_1388_, 5, v_ref_1387_);
lean_ctor_set(v___x_1388_, 6, v_currNamespace_1377_);
lean_ctor_set(v___x_1388_, 7, v_openDecls_1378_);
lean_ctor_set(v___x_1388_, 8, v_initHeartbeats_1379_);
lean_ctor_set(v___x_1388_, 9, v_maxHeartbeats_1380_);
lean_ctor_set(v___x_1388_, 10, v_quotContext_1381_);
lean_ctor_set(v___x_1388_, 11, v_currMacroScope_1382_);
lean_ctor_set(v___x_1388_, 12, v_cancelTk_x3f_1384_);
lean_ctor_set(v___x_1388_, 13, v_inheritedTraceOptions_1386_);
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*14, v_diag_1383_);
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*14 + 1, v_suppressElabErrors_1385_);
v___x_1389_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1365_, v___y_1366_, v___y_1367_, v___x_1388_, v___y_1369_);
lean_dec_ref(v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1390_, lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1390_, v_msg_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v_ref_1390_);
return v_res_1397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
lean_ctor_set(v___x_1403_, 2, v___x_1402_);
lean_ctor_set(v___x_1403_, 3, v___x_1402_);
lean_ctor_set(v___x_1403_, 4, v___x_1401_);
lean_ctor_set(v___x_1403_, 5, v___x_1401_);
lean_ctor_set(v___x_1403_, 6, v___x_1401_);
lean_ctor_set(v___x_1403_, 7, v___x_1401_);
lean_ctor_set(v___x_1403_, 8, v___x_1401_);
lean_ctor_set(v___x_1403_, 9, v___x_1401_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_unsigned_to_nat(32u);
v___x_1405_ = lean_mk_empty_array_with_capacity(v___x_1404_);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1407_ = ((size_t)5ULL);
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_unsigned_to_nat(32u);
v___x_1410_ = lean_mk_empty_array_with_capacity(v___x_1409_);
v___x_1411_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1412_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v___x_1410_);
lean_ctor_set(v___x_1412_, 2, v___x_1408_);
lean_ctor_set(v___x_1412_, 3, v___x_1408_);
lean_ctor_set_usize(v___x_1412_, 4, v___x_1407_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1413_ = lean_box(1);
v___x_1414_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1415_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v___x_1414_);
lean_ctor_set(v___x_1416_, 2, v___x_1413_);
return v___x_1416_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1422_ = l_Lean_stringToMessageData(v___x_1421_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1425_ = l_Lean_stringToMessageData(v___x_1424_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1428_ = l_Lean_stringToMessageData(v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1434_ = l_Lean_stringToMessageData(v___x_1433_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1437_ = l_Lean_stringToMessageData(v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1438_, lean_object* v_declHint_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v_env_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_st_ref_get(v___y_1440_);
v_env_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc_ref(v_env_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = l_Lean_Name_isAnonymous(v_declHint_1439_);
if (v___x_1444_ == 0)
{
uint8_t v_isExporting_1445_; 
v_isExporting_1445_ = lean_ctor_get_uint8(v_env_1443_, sizeof(void*)*8);
if (v_isExporting_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_dec_ref(v_env_1443_);
lean_dec(v_declHint_1439_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v_msg_1438_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
lean_inc_ref(v_env_1443_);
v___x_1447_ = l_Lean_Environment_setExporting(v_env_1443_, v___x_1444_);
lean_inc(v_declHint_1439_);
lean_inc_ref(v___x_1447_);
v___x_1448_ = l_Lean_Environment_contains(v___x_1447_, v_declHint_1439_, v_isExporting_1445_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec_ref(v___x_1447_);
lean_dec_ref(v_env_1443_);
lean_dec(v_declHint_1439_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_msg_1438_);
return v___x_1449_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_c_1455_; lean_object* v___x_1456_; 
v___x_1450_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1452_ = l_Lean_Options_empty;
v___x_1453_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1447_);
lean_ctor_set(v___x_1453_, 1, v___x_1450_);
lean_ctor_set(v___x_1453_, 2, v___x_1451_);
lean_ctor_set(v___x_1453_, 3, v___x_1452_);
lean_inc(v_declHint_1439_);
v___x_1454_ = l_Lean_MessageData_ofConstName(v_declHint_1439_, v___x_1444_);
v_c_1455_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1455_, 0, v___x_1453_);
lean_ctor_set(v_c_1455_, 1, v___x_1454_);
v___x_1456_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1443_, v_declHint_1439_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref(v_env_1443_);
lean_dec(v_declHint_1439_);
v___x_1457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v_c_1455_);
v___x_1459_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_MessageData_note(v___x_1460_);
v___x_1462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_msg_1438_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
else
{
lean_object* v_val_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1499_; 
v_val_1464_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1466_ = v___x_1456_;
v_isShared_1467_ = v_isSharedCheck_1499_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_val_1464_);
lean_dec(v___x_1456_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1499_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_mod_1471_; uint8_t v___x_1472_; 
v___x_1468_ = lean_box(0);
v___x_1469_ = l_Lean_Environment_header(v_env_1443_);
lean_dec_ref(v_env_1443_);
v___x_1470_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1469_);
v_mod_1471_ = lean_array_get(v___x_1468_, v___x_1470_, v_val_1464_);
lean_dec(v_val_1464_);
lean_dec_ref(v___x_1470_);
v___x_1472_ = l_Lean_isPrivateName(v_declHint_1439_);
lean_dec(v_declHint_1439_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v_c_1455_);
v___x_1475_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = l_Lean_MessageData_ofName(v_mod_1471_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = l_Lean_MessageData_note(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_msg_1438_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1482_);
v___x_1484_ = v___x_1466_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v_c_1455_);
v___x_1488_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Lean_MessageData_ofName(v_mod_1471_);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = l_Lean_MessageData_note(v___x_1493_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_msg_1438_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1495_);
v___x_1497_ = v___x_1466_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1500_; 
lean_dec_ref(v_env_1443_);
lean_dec(v_declHint_1439_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_msg_1438_);
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1501_, lean_object* v_declHint_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1501_, v_declHint_1502_, v___y_1503_);
lean_dec(v___y_1503_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1506_, lean_object* v_declHint_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1523_; 
v___x_1513_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1506_, v_declHint_1507_, v___y_1511_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1523_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1523_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1518_ = l_Lean_unknownIdentifierMessageTag;
v___x_1519_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v_a_1514_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1519_);
v___x_1521_ = v___x_1516_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1524_, lean_object* v_declHint_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1524_, v_declHint_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1532_, lean_object* v_msg_1533_, lean_object* v_declHint_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v_a_1541_; lean_object* v___x_1542_; 
v___x_1540_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1533_, v_declHint_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1532_, v_a_1541_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1543_, lean_object* v_msg_1544_, lean_object* v_declHint_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1543_, v_msg_1544_, v_declHint_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v_ref_1543_);
return v_res_1551_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1558_, lean_object* v_constName_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1565_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1566_ = 0;
lean_inc(v_constName_1559_);
v___x_1567_ = l_Lean_MessageData_ofConstName(v_constName_1559_, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1565_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1558_, v___x_1570_, v_constName_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1572_, lean_object* v_constName_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1572_, v_constName_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v_ref_1572_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_ref_1586_; lean_object* v___x_1587_; 
v_ref_1586_ = lean_ctor_get(v___y_1583_, 5);
v___x_1587_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1586_, v_constName_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v_env_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; 
v___x_1601_ = lean_st_ref_get(v___y_1599_);
v_env_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc_ref(v_env_1602_);
lean_dec(v___x_1601_);
v___x_1603_ = 0;
lean_inc(v_constName_1595_);
v___x_1604_ = l_Lean_Environment_find_x3f(v_env_1602_, v_constName_1595_, v___x_1603_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
return v___x_1605_;
}
else
{
lean_object* v_val_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_constName_1595_);
v_val_1606_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1604_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_val_1606_);
lean_dec(v___x_1604_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set_tag(v___x_1608_, 0);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_val_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; lean_object* v_toApplicative_1628_; lean_object* v_toFunctor_1629_; lean_object* v_toSeq_1630_; lean_object* v_toSeqLeft_1631_; lean_object* v_toSeqRight_1632_; lean_object* v___f_1633_; lean_object* v___f_1634_; lean_object* v___f_1635_; lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___f_1638_; lean_object* v___f_1639_; lean_object* v___f_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_toApplicative_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1675_; 
v___x_1627_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_1628_ = lean_ctor_get(v___x_1627_, 0);
v_toFunctor_1629_ = lean_ctor_get(v_toApplicative_1628_, 0);
v_toSeq_1630_ = lean_ctor_get(v_toApplicative_1628_, 2);
v_toSeqLeft_1631_ = lean_ctor_get(v_toApplicative_1628_, 3);
v_toSeqRight_1632_ = lean_ctor_get(v_toApplicative_1628_, 4);
v___f_1633_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_1634_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1629_, 2);
v___f_1635_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1635_, 0, v_toFunctor_1629_);
v___f_1636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1636_, 0, v_toFunctor_1629_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___f_1635_);
lean_ctor_set(v___x_1637_, 1, v___f_1636_);
lean_inc(v_toSeqRight_1632_);
v___f_1638_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1638_, 0, v_toSeqRight_1632_);
lean_inc(v_toSeqLeft_1631_);
v___f_1639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1639_, 0, v_toSeqLeft_1631_);
lean_inc(v_toSeq_1630_);
v___f_1640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1640_, 0, v_toSeq_1630_);
v___x_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1637_);
lean_ctor_set(v___x_1641_, 1, v___f_1633_);
lean_ctor_set(v___x_1641_, 2, v___f_1640_);
lean_ctor_set(v___x_1641_, 3, v___f_1639_);
lean_ctor_set(v___x_1641_, 4, v___f_1638_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___f_1634_);
v___x_1643_ = l_StateRefT_x27_instMonad___redArg(v___x_1642_);
v_toApplicative_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v___x_1643_, 1);
lean_dec(v_unused_1676_);
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1675_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_toApplicative_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1675_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v_toFunctor_1648_; lean_object* v_toSeq_1649_; lean_object* v_toSeqLeft_1650_; lean_object* v_toSeqRight_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1673_; 
v_toFunctor_1648_ = lean_ctor_get(v_toApplicative_1644_, 0);
v_toSeq_1649_ = lean_ctor_get(v_toApplicative_1644_, 2);
v_toSeqLeft_1650_ = lean_ctor_get(v_toApplicative_1644_, 3);
v_toSeqRight_1651_ = lean_ctor_get(v_toApplicative_1644_, 4);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_toApplicative_1644_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v_toApplicative_1644_, 1);
lean_dec(v_unused_1674_);
v___x_1653_ = v_toApplicative_1644_;
v_isShared_1654_ = v_isSharedCheck_1673_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_toSeqRight_1651_);
lean_inc(v_toSeqLeft_1650_);
lean_inc(v_toSeq_1649_);
lean_inc(v_toFunctor_1648_);
lean_dec(v_toApplicative_1644_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1673_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___f_1655_; lean_object* v___f_1656_; lean_object* v___f_1657_; lean_object* v___f_1658_; lean_object* v___x_1659_; lean_object* v___f_1660_; lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v___x_1664_; 
v___f_1655_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_1656_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_1648_);
v___f_1657_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1657_, 0, v_toFunctor_1648_);
v___f_1658_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1658_, 0, v_toFunctor_1648_);
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___f_1657_);
lean_ctor_set(v___x_1659_, 1, v___f_1658_);
v___f_1660_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1660_, 0, v_toSeqRight_1651_);
v___f_1661_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1661_, 0, v_toSeqLeft_1650_);
v___f_1662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1662_, 0, v_toSeq_1649_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v___f_1660_);
lean_ctor_set(v___x_1653_, 3, v___f_1661_);
lean_ctor_set(v___x_1653_, 2, v___f_1662_);
lean_ctor_set(v___x_1653_, 1, v___f_1655_);
lean_ctor_set(v___x_1653_, 0, v___x_1659_);
v___x_1664_ = v___x_1653_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___f_1655_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v___f_1662_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v___f_1661_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v___f_1660_);
v___x_1664_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 1, v___f_1656_);
lean_ctor_set(v___x_1646_, 0, v___x_1664_);
v___x_1666_ = v___x_1646_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v___f_1656_);
v___x_1666_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_2921__overap_1669_; lean_object* v___x_1670_; 
v___x_1667_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1668_ = l_instInhabitedOfMonad___redArg(v___x_1666_, v___x_1667_);
v___x_2921__overap_1669_ = lean_panic_fn_borrowed(v___x_1668_, v_msg_1621_);
lean_dec(v___x_1668_);
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1670_ = lean_apply_5(v___x_2921__overap_1669_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
return v___x_1670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1683_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_1688_ = lean_unsigned_to_nat(53u);
v___x_1689_ = lean_unsigned_to_nat(62u);
v___x_1690_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_1691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_1692_ = l_mkPanicMessageWithDecl(v___x_1691_, v___x_1690_, v___x_1689_, v___x_1688_, v___x_1687_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_1693_, size_t v_i_1694_, lean_object* v_bs_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_usize_dec_lt(v_i_1694_, v_sz_1693_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_bs_1695_);
return v___x_1702_;
}
else
{
lean_object* v_v_1703_; lean_object* v___x_1704_; 
v_v_1703_ = lean_array_uget_borrowed(v_bs_1695_, v_i_1694_);
lean_inc(v_v_1703_);
v___x_1704_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_1703_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1706_; lean_object* v_bs_x27_1707_; lean_object* v_a_1709_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref(v___x_1704_);
v___x_1706_ = lean_unsigned_to_nat(0u);
v_bs_x27_1707_ = lean_array_uset(v_bs_1695_, v_i_1694_, v___x_1706_);
if (lean_obj_tag(v_a_1705_) == 6)
{
lean_object* v_val_1714_; lean_object* v_numFields_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; 
v_val_1714_ = lean_ctor_get(v_a_1705_, 0);
lean_inc_ref(v_val_1714_);
lean_dec_ref(v_a_1705_);
v_numFields_1715_ = lean_ctor_get(v_val_1714_, 4);
lean_inc(v_numFields_1715_);
lean_dec_ref(v_val_1714_);
v___x_1716_ = 0;
v___x_1717_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1717_, 0, v_numFields_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1706_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*2, v___x_1716_);
v_a_1709_ = v___x_1717_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v_a_1705_);
v___x_1718_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
v___x_1719_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_1718_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref(v___x_1719_);
v_a_1709_ = v_a_1720_;
goto v___jp_1708_;
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v_bs_x27_1707_);
v_a_1721_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1719_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1719_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
v___jp_1708_:
{
size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1694_, v___x_1710_);
v___x_1712_ = lean_array_uset(v_bs_x27_1707_, v_i_1694_, v_a_1709_);
v_i_1694_ = v___x_1711_;
v_bs_1695_ = v___x_1712_;
goto _start;
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v_bs_1695_);
v_a_1729_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1704_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1704_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_1737_, lean_object* v_i_1738_, lean_object* v_bs_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
size_t v_sz_boxed_1745_; size_t v_i_boxed_1746_; lean_object* v_res_1747_; 
v_sz_boxed_1745_ = lean_unbox_usize(v_sz_1737_);
lean_dec(v_sz_1737_);
v_i_boxed_1746_ = lean_unbox_usize(v_i_1738_);
lean_dec(v_i_1738_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_1745_, v_i_boxed_1746_, v_bs_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
return v_res_1747_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1748_; lean_object* v_dummy_1749_; 
v___x_1748_ = lean_box(0);
v_dummy_1749_ = l_Lean_Expr_sort___override(v___x_1748_);
return v_dummy_1749_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_unsigned_to_nat(16u);
v___x_1752_ = lean_mk_array(v___x_1751_, v___x_1750_);
return v___x_1752_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___x_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_1758_, uint8_t v_alsoCasesOn_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v___x_1768_; 
v___x_1768_ = l_Lean_Expr_isApp(v_e_1758_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v_e_1758_);
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Expr_getAppFn(v_e_1758_);
if (lean_obj_tag(v___x_1771_) == 4)
{
lean_object* v_declName_1772_; lean_object* v_us_1773_; lean_object* v___x_1774_; lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1929_; 
v_declName_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_n(v_declName_1772_, 2);
v_us_1773_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_us_1773_);
lean_dec_ref(v___x_1771_);
v___x_1774_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1772_, v___y_1763_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1929_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1929_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
if (lean_obj_tag(v_a_1775_) == 1)
{
lean_object* v_val_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1821_; 
v_val_1779_ = lean_ctor_get(v_a_1775_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1781_ = v_a_1775_;
v_isShared_1782_ = v_isSharedCheck_1821_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_val_1779_);
lean_dec(v_a_1775_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1821_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_dummy_1783_; lean_object* v_nargs_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_args_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_dummy_1783_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v_nargs_1784_ = l_Lean_Expr_getAppNumArgs(v_e_1758_);
lean_inc(v_nargs_1784_);
v___x_1785_ = lean_mk_array(v_nargs_1784_, v_dummy_1783_);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = lean_nat_sub(v_nargs_1784_, v___x_1786_);
lean_dec(v_nargs_1784_);
v_args_1788_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1758_, v___x_1785_, v___x_1787_);
v___x_1789_ = lean_array_get_size(v_args_1788_);
v___x_1790_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1779_);
v___x_1791_ = lean_nat_dec_lt(v___x_1789_, v___x_1790_);
lean_dec(v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v_numParams_1792_; lean_object* v_numDiscrs_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1812_; 
v_numParams_1792_ = lean_ctor_get(v_val_1779_, 0);
v_numDiscrs_1793_ = lean_ctor_get(v_val_1779_, 1);
v___x_1794_ = lean_array_mk(v_us_1773_);
v___x_1795_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1792_);
v___x_1796_ = l_Array_extract___redArg(v_args_1788_, v___x_1795_, v_numParams_1792_);
v___x_1797_ = l_Lean_instInhabitedExpr;
v___x_1798_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1779_);
v___x_1799_ = lean_array_get(v___x_1797_, v_args_1788_, v___x_1798_);
lean_dec(v___x_1798_);
v___x_1800_ = lean_nat_add(v_numParams_1792_, v___x_1786_);
v___x_1801_ = lean_nat_add(v___x_1800_, v_numDiscrs_1793_);
lean_inc(v___x_1801_);
lean_inc_ref_n(v_args_1788_, 2);
v___x_1802_ = l_Array_toSubarray___redArg(v_args_1788_, v___x_1800_, v___x_1801_);
v___x_1803_ = l_Subarray_copy___redArg(v___x_1802_);
v___x_1804_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1779_);
v___x_1805_ = lean_nat_add(v___x_1801_, v___x_1804_);
lean_dec(v___x_1804_);
lean_inc(v___x_1805_);
v___x_1806_ = l_Array_toSubarray___redArg(v_args_1788_, v___x_1801_, v___x_1805_);
v___x_1807_ = l_Subarray_copy___redArg(v___x_1806_);
v___x_1808_ = l_Array_toSubarray___redArg(v_args_1788_, v___x_1805_, v___x_1789_);
v___x_1809_ = l_Subarray_copy___redArg(v___x_1808_);
v___x_1810_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1810_, 0, v_val_1779_);
lean_ctor_set(v___x_1810_, 1, v_declName_1772_);
lean_ctor_set(v___x_1810_, 2, v___x_1794_);
lean_ctor_set(v___x_1810_, 3, v___x_1796_);
lean_ctor_set(v___x_1810_, 4, v___x_1799_);
lean_ctor_set(v___x_1810_, 5, v___x_1803_);
lean_ctor_set(v___x_1810_, 6, v___x_1807_);
lean_ctor_set(v___x_1810_, 7, v___x_1809_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1810_);
v___x_1812_ = v___x_1781_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1812_);
v___x_1814_ = v___x_1777_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
lean_dec_ref(v_args_1788_);
lean_del_object(v___x_1781_);
lean_dec(v_val_1779_);
lean_dec(v_us_1773_);
lean_dec(v_declName_1772_);
v___x_1817_ = lean_box(0);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1817_);
v___x_1819_ = v___x_1777_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v___x_1822_; 
lean_del_object(v___x_1777_);
lean_dec(v_a_1775_);
v___x_1822_ = lean_st_ref_get(v___y_1763_);
if (v_alsoCasesOn_1759_ == 0)
{
lean_dec(v___x_1822_);
lean_dec(v_us_1773_);
lean_dec(v_declName_1772_);
lean_dec_ref(v_e_1758_);
goto v___jp_1765_;
}
else
{
lean_object* v_env_1823_; uint8_t v___x_1824_; 
v_env_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc_ref(v_env_1823_);
lean_dec(v___x_1822_);
lean_inc(v_declName_1772_);
v___x_1824_ = l_Lean_isCasesOnRecursor(v_env_1823_, v_declName_1772_);
if (v___x_1824_ == 0)
{
lean_dec(v_us_1773_);
lean_dec(v_declName_1772_);
lean_dec_ref(v_e_1758_);
goto v___jp_1765_;
}
else
{
lean_object* v_indName_1825_; lean_object* v___x_1826_; 
v_indName_1825_ = l_Lean_Name_getPrefix(v_declName_1772_);
v___x_1826_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_1825_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1920_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1920_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1920_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
if (lean_obj_tag(v_a_1827_) == 5)
{
lean_object* v_val_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1915_; 
v_val_1831_ = lean_ctor_get(v_a_1827_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_a_1827_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1833_ = v_a_1827_;
v_isShared_1834_ = v_isSharedCheck_1915_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_val_1831_);
lean_dec(v_a_1827_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1915_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_toConstantVal_1835_; lean_object* v_numParams_1836_; lean_object* v_numIndices_1837_; lean_object* v_ctors_1838_; lean_object* v_nargs_1839_; lean_object* v_dummy_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v_args_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_toConstantVal_1835_ = lean_ctor_get(v_val_1831_, 0);
lean_inc_ref(v_toConstantVal_1835_);
v_numParams_1836_ = lean_ctor_get(v_val_1831_, 1);
lean_inc(v_numParams_1836_);
v_numIndices_1837_ = lean_ctor_get(v_val_1831_, 2);
lean_inc(v_numIndices_1837_);
v_ctors_1838_ = lean_ctor_get(v_val_1831_, 4);
lean_inc(v_ctors_1838_);
v_nargs_1839_ = l_Lean_Expr_getAppNumArgs(v_e_1758_);
v_dummy_1840_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
lean_inc(v_nargs_1839_);
v___x_1841_ = lean_mk_array(v_nargs_1839_, v_dummy_1840_);
v___x_1842_ = lean_unsigned_to_nat(1u);
v___x_1843_ = lean_nat_sub(v_nargs_1839_, v___x_1842_);
lean_dec(v_nargs_1839_);
v_args_1844_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1758_, v___x_1841_, v___x_1843_);
v___x_1845_ = lean_nat_add(v_numParams_1836_, v___x_1842_);
v___x_1846_ = lean_nat_add(v___x_1845_, v_numIndices_1837_);
v___x_1847_ = lean_nat_add(v___x_1846_, v___x_1842_);
lean_dec(v___x_1846_);
v___x_1848_ = l_Lean_InductiveVal_numCtors(v_val_1831_);
lean_dec_ref(v_val_1831_);
v___x_1849_ = lean_nat_add(v___x_1847_, v___x_1848_);
lean_dec(v___x_1848_);
v___x_1850_ = lean_array_get_size(v_args_1844_);
v___x_1851_ = lean_nat_dec_le(v___x_1849_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
lean_dec(v___x_1849_);
lean_dec(v___x_1847_);
lean_dec(v___x_1845_);
lean_dec_ref(v_args_1844_);
lean_dec(v_ctors_1838_);
lean_dec(v_numIndices_1837_);
lean_dec(v_numParams_1836_);
lean_dec_ref(v_toConstantVal_1835_);
lean_del_object(v___x_1833_);
lean_dec(v_us_1773_);
lean_dec(v_declName_1772_);
v___x_1852_ = lean_box(0);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1852_);
v___x_1854_ = v___x_1829_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
else
{
lean_object* v___x_1856_; lean_object* v_params_1857_; lean_object* v___x_1858_; lean_object* v_motive_1859_; lean_object* v_discrs_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v_discrInfos_1863_; lean_object* v_alts_1864_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v_lower_1906_; lean_object* v_upper_1907_; uint8_t v___x_1914_; 
lean_del_object(v___x_1829_);
v___x_1856_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1836_);
lean_inc_ref_n(v_args_1844_, 3);
v_params_1857_ = l_Array_toSubarray___redArg(v_args_1844_, v___x_1856_, v_numParams_1836_);
v___x_1858_ = l_Lean_instInhabitedExpr;
v_motive_1859_ = lean_array_get(v___x_1858_, v_args_1844_, v_numParams_1836_);
lean_dec(v_numParams_1836_);
lean_inc(v___x_1847_);
v_discrs_1860_ = l_Array_toSubarray___redArg(v_args_1844_, v___x_1845_, v___x_1847_);
v___x_1861_ = lean_nat_add(v_numIndices_1837_, v___x_1842_);
lean_dec(v_numIndices_1837_);
v___x_1862_ = lean_box(0);
v_discrInfos_1863_ = lean_mk_array(v___x_1861_, v___x_1862_);
lean_inc(v___x_1849_);
v_alts_1864_ = l_Array_toSubarray___redArg(v_args_1844_, v___x_1847_, v___x_1849_);
v___x_1914_ = lean_nat_dec_le(v___x_1849_, v___x_1856_);
if (v___x_1914_ == 0)
{
v_lower_1906_ = v___x_1849_;
v_upper_1907_ = v___x_1850_;
goto v___jp_1905_;
}
else
{
lean_dec(v___x_1849_);
v_lower_1906_ = v___x_1856_;
v_upper_1907_ = v___x_1850_;
goto v___jp_1905_;
}
v___jp_1865_:
{
lean_object* v___x_1868_; size_t v_sz_1869_; size_t v___x_1870_; lean_object* v___x_1871_; 
v___x_1868_ = lean_array_mk(v_ctors_1838_);
v_sz_1869_ = lean_array_size(v___x_1868_);
v___x_1870_ = ((size_t)0ULL);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_1869_, v___x_1870_, v___x_1868_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1896_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1896_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1896_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_start_1876_; lean_object* v_stop_1877_; lean_object* v_start_1878_; lean_object* v_stop_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v_start_1876_ = lean_ctor_get(v_params_1857_, 1);
lean_inc(v_start_1876_);
v_stop_1877_ = lean_ctor_get(v_params_1857_, 2);
lean_inc(v_stop_1877_);
v_start_1878_ = lean_ctor_get(v_discrs_1860_, 1);
lean_inc(v_start_1878_);
v_stop_1879_ = lean_ctor_get(v_discrs_1860_, 2);
lean_inc(v_stop_1879_);
v___x_1880_ = lean_nat_sub(v_stop_1877_, v_start_1876_);
lean_dec(v_start_1876_);
lean_dec(v_stop_1877_);
v___x_1881_ = lean_nat_sub(v_stop_1879_, v_start_1878_);
lean_dec(v_start_1878_);
lean_dec(v_stop_1879_);
v___x_1882_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
v___x_1883_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1880_);
lean_ctor_set(v___x_1883_, 1, v___x_1881_);
lean_ctor_set(v___x_1883_, 2, v_a_1872_);
lean_ctor_set(v___x_1883_, 3, v___y_1867_);
lean_ctor_set(v___x_1883_, 4, v_discrInfos_1863_);
lean_ctor_set(v___x_1883_, 5, v___x_1882_);
v___x_1884_ = lean_array_mk(v_us_1773_);
v___x_1885_ = l_Subarray_copy___redArg(v_params_1857_);
v___x_1886_ = l_Subarray_copy___redArg(v_discrs_1860_);
v___x_1887_ = l_Subarray_copy___redArg(v_alts_1864_);
v___x_1888_ = l_Subarray_copy___redArg(v___y_1866_);
v___x_1889_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1883_);
lean_ctor_set(v___x_1889_, 1, v_declName_1772_);
lean_ctor_set(v___x_1889_, 2, v___x_1884_);
lean_ctor_set(v___x_1889_, 3, v___x_1885_);
lean_ctor_set(v___x_1889_, 4, v_motive_1859_);
lean_ctor_set(v___x_1889_, 5, v___x_1886_);
lean_ctor_set(v___x_1889_, 6, v___x_1887_);
lean_ctor_set(v___x_1889_, 7, v___x_1888_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set_tag(v___x_1833_, 1);
lean_ctor_set(v___x_1833_, 0, v___x_1889_);
v___x_1891_ = v___x_1833_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1891_);
v___x_1893_ = v___x_1874_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v_alts_1864_);
lean_dec_ref(v_discrInfos_1863_);
lean_dec_ref(v_discrs_1860_);
lean_dec(v_motive_1859_);
lean_dec_ref(v_params_1857_);
lean_del_object(v___x_1833_);
lean_dec(v_us_1773_);
lean_dec(v_declName_1772_);
v_a_1897_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1871_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1871_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
v___jp_1905_:
{
lean_object* v_levelParams_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v_levelParams_1908_ = lean_ctor_get(v_toConstantVal_1835_, 1);
lean_inc(v_levelParams_1908_);
lean_dec_ref(v_toConstantVal_1835_);
v___x_1909_ = l_Array_toSubarray___redArg(v_args_1844_, v_lower_1906_, v_upper_1907_);
v___x_1910_ = l_List_lengthTR___redArg(v_levelParams_1908_);
lean_dec(v_levelParams_1908_);
v___x_1911_ = l_List_lengthTR___redArg(v_us_1773_);
v___x_1912_ = lean_nat_dec_eq(v___x_1910_, v___x_1911_);
lean_dec(v___x_1911_);
lean_dec(v___x_1910_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3));
v___y_1866_ = v___x_1909_;
v___y_1867_ = v___x_1913_;
goto v___jp_1865_;
}
else
{
v___y_1866_ = v___x_1909_;
v___y_1867_ = v___x_1862_;
goto v___jp_1865_;
}
}
}
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
lean_dec(v_a_1827_);
lean_dec(v_us_1773_);
lean_dec(v_declName_1772_);
lean_dec_ref(v_e_1758_);
v___x_1916_ = lean_box(0);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1916_);
v___x_1918_ = v___x_1829_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_us_1773_);
lean_dec(v_declName_1772_);
lean_dec_ref(v_e_1758_);
v_a_1921_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1826_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1826_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
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
lean_dec_ref(v___x_1771_);
lean_dec_ref(v_e_1758_);
goto v___jp_1765_;
}
}
v___jp_1765_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_1930_, lean_object* v_alsoCasesOn_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1937_; lean_object* v_res_1938_; 
v_alsoCasesOn_boxed_1937_ = lean_unbox(v_alsoCasesOn_1931_);
v_res_1938_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1930_, v_alsoCasesOn_boxed_1937_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_1946_ = l_Lean_Expr_isAppOf(v_e_1939_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1947_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_1948_ = l_Lean_Expr_isAppOf(v_e_1939_, v___x_1947_);
if (v___x_1948_ == 0)
{
uint8_t v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = 1;
v___x_1950_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1939_, v___x_1949_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1971_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1971_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1971_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
if (lean_obj_tag(v_a_1951_) == 1)
{
lean_object* v_val_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1966_; 
v_val_1955_ = lean_ctor_get(v_a_1951_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_a_1951_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1957_ = v_a_1951_;
v_isShared_1958_ = v_isSharedCheck_1966_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_val_1955_);
lean_dec(v_a_1951_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1966_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1959_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_val_1955_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1959_);
v___x_1961_ = v___x_1957_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1963_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1961_);
v___x_1963_ = v___x_1953_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
lean_dec(v_a_1951_);
v___x_1967_ = lean_box(0);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_1967_);
v___x_1969_ = v___x_1953_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1950_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1950_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
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
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v_e_1939_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_e_1939_);
v___x_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1993_, v___y_1997_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2007_, lean_object* v_constName_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2015_, lean_object* v_constName_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2015_, v_constName_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2023_, lean_object* v_ref_2024_, lean_object* v_constName_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2024_, v_constName_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2032_, lean_object* v_ref_2033_, lean_object* v_constName_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2032_, v_ref_2033_, v_constName_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v_ref_2033_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2041_, lean_object* v_ref_2042_, lean_object* v_msg_2043_, lean_object* v_declHint_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2042_, v_msg_2043_, v_declHint_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2051_, lean_object* v_ref_2052_, lean_object* v_msg_2053_, lean_object* v_declHint_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2051_, v_ref_2052_, v_msg_2053_, v_declHint_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v_ref_2052_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2061_, lean_object* v_declHint_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2061_, v_declHint_2062_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2069_, lean_object* v_declHint_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2069_, v_declHint_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2077_, lean_object* v_ref_2078_, lean_object* v_msg_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2078_, v_msg_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2086_, lean_object* v_ref_2087_, lean_object* v_msg_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2086_, v_ref_2087_, v_msg_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v_ref_2087_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2095_, lean_object* v_msg_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2103_, lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2103_, v_msg_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2110_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2114_, lean_object* v_e_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___y_2122_; uint8_t v___y_2141_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2152_ = l_Lean_Expr_isAppOf(v_e_2115_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2154_ = l_Lean_Expr_isAppOf(v_e_2115_, v___x_2153_);
v___y_2141_ = v___x_2154_;
goto v___jp_2140_;
}
else
{
v___y_2141_ = v___x_2152_;
goto v___jp_2140_;
}
v___jp_2121_:
{
lean_object* v___x_2123_; 
lean_inc_ref(v___y_2122_);
v___x_2123_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2122_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2123_);
if (lean_obj_tag(v_a_2124_) == 1)
{
lean_object* v_val_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec_ref(v___y_2122_);
v_val_2125_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_val_2125_);
lean_dec_ref(v_a_2124_);
v___x_2126_ = l_Lean_mkFVar(v_val_2125_);
v___x_2127_ = l_Lean_Meta_rwIfWith(v___x_2126_, v_e_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec(v_a_2124_);
lean_dec_ref(v_e_2115_);
v___x_2128_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2129_ = l_Lean_MessageData_ofExpr(v___y_2122_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2130_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2131_;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v___y_2122_);
lean_dec_ref(v_e_2115_);
v_a_2132_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2123_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2123_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
v___jp_2140_:
{
if (v___y_2141_ == 0)
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Meta_rwMatcher(v_idx_2114_, v_e_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2142_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_c_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = l_Lean_Expr_getAppNumArgs(v_e_2115_);
v___x_2145_ = lean_nat_sub(v___x_2144_, v___x_2143_);
lean_dec(v___x_2144_);
v___x_2146_ = lean_nat_sub(v___x_2145_, v___x_2143_);
lean_dec(v___x_2145_);
v_c_2147_ = l_Lean_Expr_getRevArg_x21(v_e_2115_, v___x_2146_);
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = lean_nat_dec_eq(v_idx_2114_, v___x_2148_);
lean_dec(v_idx_2114_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_mkNot(v_c_2147_);
v___y_2122_ = v___x_2150_;
goto v___jp_2121_;
}
else
{
v___y_2122_ = v_c_2147_;
goto v___jp_2121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2155_, lean_object* v_e_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2155_, v_e_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
return v_res_2162_;
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
