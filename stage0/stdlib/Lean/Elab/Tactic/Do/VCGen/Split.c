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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsDND___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Array_mask___redArg(lean_object*, lean_object*);
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object* v_matcherApp_104_, size_t v_sz_105_, size_t v_i_106_, lean_object* v_bs_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_usize_dec_lt(v_i_106_, v_sz_105_);
if (v___x_108_ == 0)
{
return v_bs_107_;
}
else
{
lean_object* v_v_109_; lean_object* v_alts_110_; lean_object* v___x_111_; lean_object* v_bs_x27_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; size_t v___x_117_; size_t v___x_118_; lean_object* v___x_119_; 
v_v_109_ = lean_array_uget(v_bs_107_, v_i_106_);
v_alts_110_ = lean_ctor_get(v_matcherApp_104_, 6);
v___x_111_ = lean_unsigned_to_nat(0u);
v_bs_x27_112_ = lean_array_uset(v_bs_107_, v_i_106_, v___x_111_);
v___x_113_ = l_Lean_instInhabitedExpr;
v___x_114_ = lean_usize_to_nat(v_i_106_);
v___x_115_ = lean_array_get_borrowed(v___x_113_, v_alts_110_, v___x_114_);
lean_dec(v___x_114_);
lean_inc(v___x_115_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_v_109_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_add(v_i_106_, v___x_117_);
v___x_119_ = lean_array_uset(v_bs_x27_112_, v_i_106_, v___x_116_);
v_i_106_ = v___x_118_;
v_bs_107_ = v___x_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object* v_matcherApp_121_, lean_object* v_sz_122_, lean_object* v_i_123_, lean_object* v_bs_124_){
_start:
{
size_t v_sz_boxed_125_; size_t v_i_boxed_126_; lean_object* v_res_127_; 
v_sz_boxed_125_ = lean_unbox_usize(v_sz_122_);
lean_dec(v_sz_122_);
v_i_boxed_126_ = lean_unbox_usize(v_i_123_);
lean_dec(v_i_123_);
v_res_127_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_121_, v_sz_boxed_125_, v_i_boxed_126_, v_bs_124_);
lean_dec_ref(v_matcherApp_121_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object* v_info_128_){
_start:
{
switch(lean_obj_tag(v_info_128_))
{
case 0:
{
lean_object* v_e_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_e_129_ = lean_ctor_get(v_info_128_, 0);
lean_inc_ref(v_e_129_);
lean_dec_ref_known(v_info_128_, 1);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_unsigned_to_nat(3u);
v___x_132_ = l_Lean_Expr_getAppNumArgs(v_e_129_);
v___x_133_ = lean_nat_sub(v___x_132_, v___x_131_);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_sub(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
v___x_136_ = l_Lean_Expr_getRevArg_x21(v_e_129_, v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_130_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_unsigned_to_nat(4u);
v___x_139_ = lean_nat_sub(v___x_132_, v___x_138_);
lean_dec(v___x_132_);
v___x_140_ = lean_nat_sub(v___x_139_, v___x_134_);
lean_dec(v___x_139_);
v___x_141_ = l_Lean_Expr_getRevArg_x21(v_e_129_, v___x_140_);
lean_dec_ref(v_e_129_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_130_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(2u);
v___x_144_ = lean_mk_empty_array_with_capacity(v___x_143_);
v___x_145_ = lean_array_push(v___x_144_, v___x_137_);
v___x_146_ = lean_array_push(v___x_145_, v___x_142_);
return v___x_146_;
}
case 1:
{
lean_object* v_e_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_e_147_ = lean_ctor_get(v_info_128_, 0);
lean_inc_ref(v_e_147_);
lean_dec_ref_known(v_info_128_, 1);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_unsigned_to_nat(3u);
v___x_150_ = l_Lean_Expr_getAppNumArgs(v_e_147_);
v___x_151_ = lean_nat_sub(v___x_150_, v___x_149_);
v___x_152_ = lean_nat_sub(v___x_151_, v___x_148_);
lean_dec(v___x_151_);
v___x_153_ = l_Lean_Expr_getRevArg_x21(v_e_147_, v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_148_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(4u);
v___x_156_ = lean_nat_sub(v___x_150_, v___x_155_);
lean_dec(v___x_150_);
v___x_157_ = lean_nat_sub(v___x_156_, v___x_148_);
lean_dec(v___x_156_);
v___x_158_ = l_Lean_Expr_getRevArg_x21(v_e_147_, v___x_157_);
lean_dec_ref(v_e_147_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_148_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(2u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
v___x_162_ = lean_array_push(v___x_161_, v___x_154_);
v___x_163_ = lean_array_push(v___x_162_, v___x_159_);
return v___x_163_;
}
default: 
{
lean_object* v_matcherApp_164_; lean_object* v___x_165_; size_t v_sz_166_; size_t v___x_167_; lean_object* v___x_168_; 
v_matcherApp_164_ = lean_ctor_get(v_info_128_, 0);
lean_inc_ref_n(v_matcherApp_164_, 2);
lean_dec_ref_known(v_info_128_, 1);
v___x_165_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_164_);
v_sz_166_ = lean_array_size(v___x_165_);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_164_, v_sz_166_, v___x_167_, v___x_165_);
lean_dec_ref(v_matcherApp_164_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object* v_matcherApp_169_, lean_object* v_as_170_, size_t v_sz_171_, size_t v_i_172_, lean_object* v_bs_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_169_, v_sz_171_, v_i_172_, v_bs_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object* v_matcherApp_175_, lean_object* v_as_176_, lean_object* v_sz_177_, lean_object* v_i_178_, lean_object* v_bs_179_){
_start:
{
size_t v_sz_boxed_180_; size_t v_i_boxed_181_; lean_object* v_res_182_; 
v_sz_boxed_180_ = lean_unbox_usize(v_sz_177_);
lean_dec(v_sz_177_);
v_i_boxed_181_ = lean_unbox_usize(v_i_178_);
lean_dec(v_i_178_);
v_res_182_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(v_matcherApp_175_, v_as_176_, v_sz_boxed_180_, v_i_boxed_181_, v_bs_179_);
lean_dec_ref(v_as_176_);
lean_dec_ref(v_matcherApp_175_);
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
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v___x_2358__overap_498_; lean_object* v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_2358__overap_498_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_489_, v___x_497_, v_a_496_, lean_box(0));
v___x_499_ = lean_apply_5(v___x_2358__overap_498_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, lean_box(0));
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
lean_object* v___x_601_; size_t v_sz_602_; size_t v___x_603_; lean_object* v_altNamesTypes_604_; uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v_sz_602_ = lean_array_size(v_origAltTypes_600_);
v___x_603_ = ((size_t)0ULL);
lean_inc_ref(v_origAltTypes_600_);
v_altNamesTypes_604_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_601_, v_origAltTypes_600_, v___f_596_, v_sz_602_, v___x_603_, v_origAltTypes_600_);
lean_dec_ref(v_origAltTypes_600_);
v___x_605_ = 0;
v___x_606_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_597_, v_inst_598_, v_altNamesTypes_604_, v___f_599_, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object* v_toMatcherInfo_607_, lean_object* v_matcherName_608_, lean_object* v_params_609_, lean_object* v_motive_610_, lean_object* v_discrs_611_, lean_object* v_k_612_, lean_object* v___x_613_, lean_object* v_inst_614_, lean_object* v_toBind_615_, lean_object* v___f_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_alts_619_, lean_object* v_matcherLevels_620_){
_start:
{
lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_matcherPartial_625_; lean_object* v_matcherPartial_626_; lean_object* v_matcherPartial_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_inc(v_toBind_615_);
lean_inc(v_inst_614_);
lean_inc_ref(v_discrs_611_);
lean_inc_ref(v_motive_610_);
lean_inc_ref(v_params_609_);
lean_inc_ref(v_matcherLevels_620_);
lean_inc(v_matcherName_608_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21), 11, 10);
lean_closure_set(v___f_621_, 0, v_toMatcherInfo_607_);
lean_closure_set(v___f_621_, 1, v_matcherName_608_);
lean_closure_set(v___f_621_, 2, v_matcherLevels_620_);
lean_closure_set(v___f_621_, 3, v_params_609_);
lean_closure_set(v___f_621_, 4, v_motive_610_);
lean_closure_set(v___f_621_, 5, v_discrs_611_);
lean_closure_set(v___f_621_, 6, v_k_612_);
lean_closure_set(v___f_621_, 7, v___x_613_);
lean_closure_set(v___f_621_, 8, v_inst_614_);
lean_closure_set(v___f_621_, 9, v_toBind_615_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 5, 4);
lean_closure_set(v___f_622_, 0, v___f_616_);
lean_closure_set(v___f_622_, 1, v_inst_617_);
lean_closure_set(v___f_622_, 2, v_inst_618_);
lean_closure_set(v___f_622_, 3, v___f_621_);
v___x_623_ = lean_array_to_list(v_matcherLevels_620_);
v___x_624_ = l_Lean_mkConst(v_matcherName_608_, v___x_623_);
v_matcherPartial_625_ = l_Lean_mkAppN(v___x_624_, v_params_609_);
lean_dec_ref(v_params_609_);
v_matcherPartial_626_ = l_Lean_Expr_app___override(v_matcherPartial_625_, v_motive_610_);
v_matcherPartial_627_ = l_Lean_mkAppN(v_matcherPartial_626_, v_discrs_611_);
lean_dec_ref(v_discrs_611_);
v___x_628_ = lean_array_get_size(v_alts_619_);
v___x_629_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_629_, 0, v___x_628_);
lean_closure_set(v___x_629_, 1, v_matcherPartial_627_);
v___x_630_ = lean_apply_2(v_inst_614_, lean_box(0), v___x_629_);
v___x_631_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v___x_630_, v___f_622_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___boxed(lean_object* v_toMatcherInfo_632_, lean_object* v_matcherName_633_, lean_object* v_params_634_, lean_object* v_motive_635_, lean_object* v_discrs_636_, lean_object* v_k_637_, lean_object* v___x_638_, lean_object* v_inst_639_, lean_object* v_toBind_640_, lean_object* v___f_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_alts_644_, lean_object* v_matcherLevels_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(v_toMatcherInfo_632_, v_matcherName_633_, v_params_634_, v_motive_635_, v_discrs_636_, v_k_637_, v___x_638_, v_inst_639_, v_toBind_640_, v___f_641_, v_inst_642_, v_inst_643_, v_alts_644_, v_matcherLevels_645_);
lean_dec_ref(v_alts_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object* v___f_647_, lean_object* v_matcherLevels_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_apply_1(v___f_647_, v_matcherLevels_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object* v_matcherLevels_650_, lean_object* v_val_651_, lean_object* v_toPure_652_, lean_object* v_toBind_653_, lean_object* v___f_654_, lean_object* v_uElim_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_array_set(v_matcherLevels_650_, v_val_651_, v_uElim_655_);
v___x_657_ = lean_apply_2(v_toPure_652_, lean_box(0), v___x_656_);
v___x_658_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v___x_657_, v___f_654_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___boxed(lean_object* v_matcherLevels_659_, lean_object* v_val_660_, lean_object* v_toPure_661_, lean_object* v_toBind_662_, lean_object* v___f_663_, lean_object* v_uElim_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(v_matcherLevels_659_, v_val_660_, v_toPure_661_, v_toBind_662_, v___f_663_, v_uElim_664_);
lean_dec(v_val_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object* v_toMatcherInfo_666_, lean_object* v_matcherName_667_, lean_object* v_params_668_, lean_object* v_discrs_669_, lean_object* v_k_670_, lean_object* v___x_671_, lean_object* v_inst_672_, lean_object* v_toBind_673_, lean_object* v___f_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_alts_677_, lean_object* v_toPure_678_, lean_object* v_matcherLevels_679_, lean_object* v_resTy_680_, lean_object* v_motive_681_){
_start:
{
lean_object* v_uElimPos_x3f_682_; lean_object* v___f_683_; 
v_uElimPos_x3f_682_ = lean_ctor_get(v_toMatcherInfo_666_, 3);
lean_inc(v_uElimPos_x3f_682_);
lean_inc(v_toBind_673_);
lean_inc(v_inst_672_);
v___f_683_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___boxed), 14, 13);
lean_closure_set(v___f_683_, 0, v_toMatcherInfo_666_);
lean_closure_set(v___f_683_, 1, v_matcherName_667_);
lean_closure_set(v___f_683_, 2, v_params_668_);
lean_closure_set(v___f_683_, 3, v_motive_681_);
lean_closure_set(v___f_683_, 4, v_discrs_669_);
lean_closure_set(v___f_683_, 5, v_k_670_);
lean_closure_set(v___f_683_, 6, v___x_671_);
lean_closure_set(v___f_683_, 7, v_inst_672_);
lean_closure_set(v___f_683_, 8, v_toBind_673_);
lean_closure_set(v___f_683_, 9, v___f_674_);
lean_closure_set(v___f_683_, 10, v_inst_675_);
lean_closure_set(v___f_683_, 11, v_inst_676_);
lean_closure_set(v___f_683_, 12, v_alts_677_);
if (lean_obj_tag(v_uElimPos_x3f_682_) == 0)
{
lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec_ref(v_resTy_680_);
lean_dec(v_inst_672_);
v___f_684_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24), 2, 1);
lean_closure_set(v___f_684_, 0, v___f_683_);
v___x_685_ = lean_apply_2(v_toPure_678_, lean_box(0), v_matcherLevels_679_);
v___x_686_ = lean_apply_4(v_toBind_673_, lean_box(0), lean_box(0), v___x_685_, v___f_684_);
return v___x_686_;
}
else
{
lean_object* v_val_687_; lean_object* v___f_688_; lean_object* v___f_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_val_687_ = lean_ctor_get(v_uElimPos_x3f_682_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v_uElimPos_x3f_682_, 1);
v___f_688_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24), 2, 1);
lean_closure_set(v___f_688_, 0, v___f_683_);
lean_inc(v_toBind_673_);
v___f_689_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___boxed), 6, 5);
lean_closure_set(v___f_689_, 0, v_matcherLevels_679_);
lean_closure_set(v___f_689_, 1, v_val_687_);
lean_closure_set(v___f_689_, 2, v_toPure_678_);
lean_closure_set(v___f_689_, 3, v_toBind_673_);
lean_closure_set(v___f_689_, 4, v___f_688_);
v___x_690_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_690_, 0, v_resTy_680_);
v___x_691_ = lean_apply_2(v_inst_672_, lean_box(0), v___x_690_);
v___x_692_ = lean_apply_4(v_toBind_673_, lean_box(0), lean_box(0), v___x_691_, v___f_689_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object* v_toMatcherInfo_693_, lean_object* v_matcherName_694_, lean_object* v_params_695_, lean_object* v_k_696_, lean_object* v___x_697_, lean_object* v_inst_698_, lean_object* v_toBind_699_, lean_object* v___f_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_alts_703_, lean_object* v_toPure_704_, lean_object* v_matcherLevels_705_, lean_object* v_resTy_706_, lean_object* v___x_707_, lean_object* v_motive_708_, lean_object* v___f_709_, lean_object* v_discrs_710_){
_start:
{
lean_object* v___f_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_inc(v_toBind_699_);
lean_inc(v_inst_698_);
lean_inc_ref(v___x_697_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25), 16, 15);
lean_closure_set(v___f_711_, 0, v_toMatcherInfo_693_);
lean_closure_set(v___f_711_, 1, v_matcherName_694_);
lean_closure_set(v___f_711_, 2, v_params_695_);
lean_closure_set(v___f_711_, 3, v_discrs_710_);
lean_closure_set(v___f_711_, 4, v_k_696_);
lean_closure_set(v___f_711_, 5, v___x_697_);
lean_closure_set(v___f_711_, 6, v_inst_698_);
lean_closure_set(v___f_711_, 7, v_toBind_699_);
lean_closure_set(v___f_711_, 8, v___f_700_);
lean_closure_set(v___f_711_, 9, v_inst_701_);
lean_closure_set(v___f_711_, 10, v_inst_702_);
lean_closure_set(v___f_711_, 11, v_alts_703_);
lean_closure_set(v___f_711_, 12, v_toPure_704_);
lean_closure_set(v___f_711_, 13, v_matcherLevels_705_);
lean_closure_set(v___f_711_, 14, v_resTy_706_);
v___x_712_ = 0;
v___x_713_ = l_Lean_Meta_lambdaTelescope___redArg(v___x_707_, v___x_697_, v_motive_708_, v___f_709_, v___x_712_);
v___x_714_ = lean_apply_2(v_inst_698_, lean_box(0), v___x_713_);
v___x_715_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_714_, v___f_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_716_ = _args[0];
lean_object* v_matcherName_717_ = _args[1];
lean_object* v_params_718_ = _args[2];
lean_object* v_k_719_ = _args[3];
lean_object* v___x_720_ = _args[4];
lean_object* v_inst_721_ = _args[5];
lean_object* v_toBind_722_ = _args[6];
lean_object* v___f_723_ = _args[7];
lean_object* v_inst_724_ = _args[8];
lean_object* v_inst_725_ = _args[9];
lean_object* v_alts_726_ = _args[10];
lean_object* v_toPure_727_ = _args[11];
lean_object* v_matcherLevels_728_ = _args[12];
lean_object* v_resTy_729_ = _args[13];
lean_object* v___x_730_ = _args[14];
lean_object* v_motive_731_ = _args[15];
lean_object* v___f_732_ = _args[16];
lean_object* v_discrs_733_ = _args[17];
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(v_toMatcherInfo_716_, v_matcherName_717_, v_params_718_, v_k_719_, v___x_720_, v_inst_721_, v_toBind_722_, v___f_723_, v_inst_724_, v_inst_725_, v_alts_726_, v_toPure_727_, v_matcherLevels_728_, v_resTy_729_, v___x_730_, v_motive_731_, v___f_732_, v_discrs_733_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_instMonadEIO(lean_box(0));
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_737_ = l_StateRefT_x27_instMonad___redArg(v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = l_Lean_Level_ofNat(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8);
v___x_748_ = l_Lean_mkSort(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_info_753_, lean_object* v_resTy_754_, lean_object* v_k_755_){
_start:
{
lean_object* v___x_756_; lean_object* v_toApplicative_757_; lean_object* v_toFunctor_758_; lean_object* v_toSeq_759_; lean_object* v_toSeqLeft_760_; lean_object* v_toSeqRight_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___x_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_toApplicative_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_848_; 
v___x_756_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_757_ = lean_ctor_get(v___x_756_, 0);
v_toFunctor_758_ = lean_ctor_get(v_toApplicative_757_, 0);
v_toSeq_759_ = lean_ctor_get(v_toApplicative_757_, 2);
v_toSeqLeft_760_ = lean_ctor_get(v_toApplicative_757_, 3);
v_toSeqRight_761_ = lean_ctor_get(v_toApplicative_757_, 4);
v___f_762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_758_, 2);
v___f_764_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_764_, 0, v_toFunctor_758_);
v___f_765_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_765_, 0, v_toFunctor_758_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___f_764_);
lean_ctor_set(v___x_766_, 1, v___f_765_);
lean_inc(v_toSeqRight_761_);
v___f_767_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_767_, 0, v_toSeqRight_761_);
lean_inc(v_toSeqLeft_760_);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_768_, 0, v_toSeqLeft_760_);
lean_inc(v_toSeq_759_);
v___f_769_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_769_, 0, v_toSeq_759_);
v___x_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_770_, 0, v___x_766_);
lean_ctor_set(v___x_770_, 1, v___f_762_);
lean_ctor_set(v___x_770_, 2, v___f_769_);
lean_ctor_set(v___x_770_, 3, v___f_768_);
lean_ctor_set(v___x_770_, 4, v___f_767_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___f_763_);
v___x_772_ = l_StateRefT_x27_instMonad___redArg(v___x_771_);
v_toApplicative_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v___x_772_, 1);
lean_dec(v_unused_849_);
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_848_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_toApplicative_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_848_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_toFunctor_777_; lean_object* v_toSeq_778_; lean_object* v_toSeqLeft_779_; lean_object* v_toSeqRight_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_846_; 
v_toFunctor_777_ = lean_ctor_get(v_toApplicative_773_, 0);
v_toSeq_778_ = lean_ctor_get(v_toApplicative_773_, 2);
v_toSeqLeft_779_ = lean_ctor_get(v_toApplicative_773_, 3);
v_toSeqRight_780_ = lean_ctor_get(v_toApplicative_773_, 4);
v_isSharedCheck_846_ = !lean_is_exclusive(v_toApplicative_773_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_dec(v_unused_847_);
v___x_782_ = v_toApplicative_773_;
v_isShared_783_ = v_isSharedCheck_846_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_toSeqRight_780_);
lean_inc(v_toSeqLeft_779_);
lean_inc(v_toSeq_778_);
lean_inc(v_toFunctor_777_);
lean_dec(v_toApplicative_773_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_846_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_793_; 
v___f_784_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_777_);
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_786_, 0, v_toFunctor_777_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_787_, 0, v_toFunctor_777_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___f_786_);
lean_ctor_set(v___x_788_, 1, v___f_787_);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_789_, 0, v_toSeqRight_780_);
v___f_790_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_790_, 0, v_toSeqLeft_779_);
v___f_791_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_791_, 0, v_toSeq_778_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v___f_789_);
lean_ctor_set(v___x_782_, 3, v___f_790_);
lean_ctor_set(v___x_782_, 2, v___f_791_);
lean_ctor_set(v___x_782_, 1, v___f_784_);
lean_ctor_set(v___x_782_, 0, v___x_788_);
v___x_793_ = v___x_782_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___f_784_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v___f_791_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v___f_790_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v___f_789_);
v___x_793_ = v_reuseFailAlloc_845_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___f_785_);
lean_ctor_set(v___x_775_, 0, v___x_793_);
v___x_795_ = v___x_775_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___f_785_);
v___x_795_ = v_reuseFailAlloc_844_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v_toApplicative_796_; lean_object* v_toFunctor_797_; lean_object* v_toSeq_798_; lean_object* v_toSeqLeft_799_; lean_object* v_toSeqRight_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_toApplicative_796_ = lean_ctor_get(v___x_756_, 0);
v_toFunctor_797_ = lean_ctor_get(v_toApplicative_796_, 0);
v_toSeq_798_ = lean_ctor_get(v_toApplicative_796_, 2);
v_toSeqLeft_799_ = lean_ctor_get(v_toApplicative_796_, 3);
v_toSeqRight_800_ = lean_ctor_get(v_toApplicative_796_, 4);
lean_inc_ref_n(v_toFunctor_797_, 2);
v___f_801_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_801_, 0, v_toFunctor_797_);
v___f_802_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_802_, 0, v_toFunctor_797_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___f_801_);
lean_ctor_set(v___x_803_, 1, v___f_802_);
lean_inc(v_toSeqRight_800_);
v___f_804_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_804_, 0, v_toSeqRight_800_);
lean_inc(v_toSeqLeft_799_);
v___f_805_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_805_, 0, v_toSeqLeft_799_);
lean_inc(v_toSeq_798_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_806_, 0, v_toSeq_798_);
v___x_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_807_, 0, v___x_803_);
lean_ctor_set(v___x_807_, 1, v___f_762_);
lean_ctor_set(v___x_807_, 2, v___f_806_);
lean_ctor_set(v___x_807_, 3, v___f_805_);
lean_ctor_set(v___x_807_, 4, v___f_804_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___f_763_);
v___x_809_ = l_StateRefT_x27_instMonad___redArg(v___x_808_);
v___x_810_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_810_, 0, lean_box(0));
lean_closure_set(v___x_810_, 1, lean_box(0));
lean_closure_set(v___x_810_, 2, v___x_809_);
v___x_811_ = l_instMonadControlTOfPure___redArg(v___x_810_);
switch(lean_obj_tag(v_info_753_))
{
case 0:
{
lean_object* v_toBind_812_; lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec_ref_known(v_info_753_, 1);
lean_dec_ref(v___x_811_);
lean_dec_ref(v___x_795_);
v_toBind_812_ = lean_ctor_get(v_inst_752_, 1);
lean_inc_ref(v_inst_752_);
lean_inc_ref(v_inst_751_);
lean_inc(v_toBind_812_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_813_, 0, v_resTy_754_);
lean_closure_set(v___f_813_, 1, v_k_755_);
lean_closure_set(v___f_813_, 2, v_inst_750_);
lean_closure_set(v___f_813_, 3, v_toBind_812_);
lean_closure_set(v___f_813_, 4, v_inst_751_);
lean_closure_set(v___f_813_, 5, v_inst_752_);
v___x_814_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_815_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_816_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_751_, v_inst_752_, v___x_814_, v___x_815_, v___f_813_);
return v___x_816_;
}
case 1:
{
lean_object* v_toBind_817_; lean_object* v___f_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref_known(v_info_753_, 1);
lean_dec_ref(v___x_811_);
lean_dec_ref(v___x_795_);
v_toBind_817_ = lean_ctor_get(v_inst_752_, 1);
lean_inc_ref(v_inst_752_);
lean_inc_ref(v_inst_751_);
lean_inc(v_toBind_817_);
v___f_818_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_818_, 0, v_resTy_754_);
lean_closure_set(v___f_818_, 1, v_k_755_);
lean_closure_set(v___f_818_, 2, v_inst_750_);
lean_closure_set(v___f_818_, 3, v_toBind_817_);
lean_closure_set(v___f_818_, 4, v_inst_751_);
lean_closure_set(v___f_818_, 5, v_inst_752_);
v___x_819_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_820_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_821_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_751_, v_inst_752_, v___x_819_, v___x_820_, v___f_818_);
return v___x_821_;
}
default: 
{
lean_object* v_toApplicative_822_; lean_object* v_matcherApp_823_; lean_object* v_toBind_824_; lean_object* v_toPure_825_; lean_object* v_toMatcherInfo_826_; lean_object* v_matcherName_827_; lean_object* v_matcherLevels_828_; lean_object* v_params_829_; lean_object* v_motive_830_; lean_object* v_discrs_831_; lean_object* v_alts_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___x_838_; size_t v_sz_839_; size_t v___x_840_; lean_object* v_discrDecls_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v_toApplicative_822_ = lean_ctor_get(v_inst_752_, 0);
v_matcherApp_823_ = lean_ctor_get(v_info_753_, 0);
lean_inc_ref(v_matcherApp_823_);
lean_dec_ref_known(v_info_753_, 1);
v_toBind_824_ = lean_ctor_get(v_inst_752_, 1);
v_toPure_825_ = lean_ctor_get(v_toApplicative_822_, 1);
v_toMatcherInfo_826_ = lean_ctor_get(v_matcherApp_823_, 0);
lean_inc_ref(v_toMatcherInfo_826_);
v_matcherName_827_ = lean_ctor_get(v_matcherApp_823_, 1);
lean_inc(v_matcherName_827_);
v_matcherLevels_828_ = lean_ctor_get(v_matcherApp_823_, 2);
lean_inc_ref(v_matcherLevels_828_);
v_params_829_ = lean_ctor_get(v_matcherApp_823_, 3);
lean_inc_ref(v_params_829_);
v_motive_830_ = lean_ctor_get(v_matcherApp_823_, 4);
lean_inc_ref(v_motive_830_);
v_discrs_831_ = lean_ctor_get(v_matcherApp_823_, 5);
lean_inc_ref_n(v_discrs_831_, 3);
v_alts_832_ = lean_ctor_get(v_matcherApp_823_, 6);
lean_inc_ref(v_alts_832_);
lean_dec_ref(v_matcherApp_823_);
v___f_833_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
lean_inc_ref(v_resTy_754_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed), 8, 1);
lean_closure_set(v___f_834_, 0, v_resTy_754_);
v___x_835_ = l_Lean_instInhabitedExpr;
lean_inc(v_inst_750_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19), 6, 3);
lean_closure_set(v___f_836_, 0, v___x_835_);
lean_closure_set(v___f_836_, 1, v_discrs_831_);
lean_closure_set(v___f_836_, 2, v_inst_750_);
lean_inc(v_toPure_825_);
lean_inc_ref(v_inst_752_);
lean_inc_ref(v_inst_751_);
lean_inc(v_toBind_824_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed), 18, 17);
lean_closure_set(v___f_837_, 0, v_toMatcherInfo_826_);
lean_closure_set(v___f_837_, 1, v_matcherName_827_);
lean_closure_set(v___f_837_, 2, v_params_829_);
lean_closure_set(v___f_837_, 3, v_k_755_);
lean_closure_set(v___f_837_, 4, v___x_795_);
lean_closure_set(v___f_837_, 5, v_inst_750_);
lean_closure_set(v___f_837_, 6, v_toBind_824_);
lean_closure_set(v___f_837_, 7, v___f_833_);
lean_closure_set(v___f_837_, 8, v_inst_751_);
lean_closure_set(v___f_837_, 9, v_inst_752_);
lean_closure_set(v___f_837_, 10, v_alts_832_);
lean_closure_set(v___f_837_, 11, v_toPure_825_);
lean_closure_set(v___f_837_, 12, v_matcherLevels_828_);
lean_closure_set(v___f_837_, 13, v_resTy_754_);
lean_closure_set(v___f_837_, 14, v___x_811_);
lean_closure_set(v___f_837_, 15, v_motive_830_);
lean_closure_set(v___f_837_, 16, v___f_834_);
v___x_838_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v_sz_839_ = lean_array_size(v_discrs_831_);
v___x_840_ = ((size_t)0ULL);
v_discrDecls_841_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_838_, v_discrs_831_, v___f_836_, v_sz_839_, v___x_840_, v_discrs_831_);
lean_dec_ref(v_discrs_831_);
v___x_842_ = 0;
v___x_843_ = l_Lean_Meta_withLocalDeclsD___redArg(v_inst_751_, v_inst_752_, v_discrDecls_841_, v___f_837_, v___x_842_);
return v___x_843_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_850_, lean_object* v_00_u03b1_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_info_856_, lean_object* v_resTy_857_, lean_object* v_k_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_852_, v_inst_853_, v_inst_854_, v_info_856_, v_resTy_857_, v_k_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_860_, lean_object* v_00_u03b1_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_info_866_, lean_object* v_resTy_867_, lean_object* v_k_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_860_, v_00_u03b1_861_, v_inst_862_, v_inst_863_, v_inst_864_, v_inst_865_, v_info_866_, v_resTy_867_, v_k_868_);
lean_dec(v_inst_865_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_870_, lean_object* v_resTy_871_, lean_object* v_c_872_, lean_object* v_h_873_, lean_object* v_t_874_, lean_object* v_toPure_875_, lean_object* v_e_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_879_, 0, v_u_870_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_mkConst(v___x_877_, v___x_879_);
v___x_881_ = l_Lean_mkApp5(v___x_880_, v_resTy_871_, v_c_872_, v_h_873_, v_t_874_, v_e_876_);
v___x_882_ = lean_apply_2(v_toPure_875_, lean_box(0), v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_886_, lean_object* v_resTy_887_, lean_object* v_c_888_, lean_object* v_h_889_, lean_object* v_toPure_890_, lean_object* v_onAlt_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v_toBind_894_, lean_object* v_t_895_){
_start:
{
lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_inc_ref(v_resTy_887_);
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_896_, 0, v_u_886_);
lean_closure_set(v___f_896_, 1, v_resTy_887_);
lean_closure_set(v___f_896_, 2, v_c_888_);
lean_closure_set(v___f_896_, 3, v_h_889_);
lean_closure_set(v___f_896_, 4, v_t_895_);
lean_closure_set(v___f_896_, 5, v_toPure_890_);
v___x_897_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_898_ = lean_apply_4(v_onAlt_891_, v___x_897_, v_resTy_887_, v___x_892_, v___x_893_);
v___x_899_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v___x_898_, v___f_896_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_900_, uint8_t v_useSplitter_901_, lean_object* v_inst_902_, lean_object* v_____do__lift_903_){
_start:
{
uint8_t v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_904_ = 0;
v___x_905_ = 1;
v___x_906_ = lean_box(v___x_904_);
v___x_907_ = lean_box(v_useSplitter_901_);
v___x_908_ = lean_box(v___x_904_);
v___x_909_ = lean_box(v_useSplitter_901_);
v___x_910_ = lean_box(v___x_905_);
v___x_911_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_911_, 0, v___x_900_);
lean_closure_set(v___x_911_, 1, v_____do__lift_903_);
lean_closure_set(v___x_911_, 2, v___x_906_);
lean_closure_set(v___x_911_, 3, v___x_907_);
lean_closure_set(v___x_911_, 4, v___x_908_);
lean_closure_set(v___x_911_, 5, v___x_909_);
lean_closure_set(v___x_911_, 6, v___x_910_);
v___x_912_ = lean_apply_2(v_inst_902_, lean_box(0), v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_913_, lean_object* v_useSplitter_914_, lean_object* v_inst_915_, lean_object* v_____do__lift_916_){
_start:
{
uint8_t v_useSplitter_boxed_917_; lean_object* v_res_918_; 
v_useSplitter_boxed_917_ = lean_unbox(v_useSplitter_914_);
v_res_918_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_913_, v_useSplitter_boxed_917_, v_inst_915_, v_____do__lift_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_922_, uint8_t v_useSplitter_923_, lean_object* v_inst_924_, lean_object* v_onAlt_925_, lean_object* v_resTy_926_, lean_object* v_toBind_927_, lean_object* v_h_928_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_932_ = lean_mk_empty_array_with_capacity(v___x_922_);
v___x_933_ = lean_array_push(v___x_932_, v_h_928_);
v___x_934_ = lean_box(v_useSplitter_923_);
lean_inc_ref(v___x_933_);
v___f_935_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_935_, 0, v___x_933_);
lean_closure_set(v___f_935_, 1, v___x_934_);
lean_closure_set(v___f_935_, 2, v_inst_924_);
v___x_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_936_, 0, v___x_931_);
lean_ctor_set(v___x_936_, 1, v___x_933_);
lean_ctor_set(v___x_936_, 2, v___x_931_);
lean_ctor_set(v___x_936_, 3, v___x_931_);
lean_ctor_set(v___x_936_, 4, v___x_931_);
v___x_937_ = lean_apply_4(v_onAlt_925_, v___x_929_, v_resTy_926_, v___x_930_, v___x_936_);
v___x_938_ = lean_apply_4(v_toBind_927_, lean_box(0), lean_box(0), v___x_937_, v___f_935_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_939_, lean_object* v_useSplitter_940_, lean_object* v_inst_941_, lean_object* v_onAlt_942_, lean_object* v_resTy_943_, lean_object* v_toBind_944_, lean_object* v_h_945_){
_start:
{
uint8_t v_useSplitter_boxed_946_; lean_object* v_res_947_; 
v_useSplitter_boxed_946_ = lean_unbox(v_useSplitter_940_);
v_res_947_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_939_, v_useSplitter_boxed_946_, v_inst_941_, v_onAlt_942_, v_resTy_943_, v_toBind_944_, v_h_945_);
lean_dec(v___x_939_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_948_, uint8_t v_useSplitter_949_, lean_object* v_inst_950_, lean_object* v_onAlt_951_, lean_object* v_resTy_952_, lean_object* v_toBind_953_, lean_object* v_h_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___f_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_955_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_956_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_957_ = lean_mk_empty_array_with_capacity(v___x_948_);
v___x_958_ = lean_array_push(v___x_957_, v_h_954_);
v___x_959_ = lean_box(v_useSplitter_949_);
lean_inc_ref(v___x_958_);
v___f_960_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_960_, 0, v___x_958_);
lean_closure_set(v___f_960_, 1, v___x_959_);
lean_closure_set(v___f_960_, 2, v_inst_950_);
v___x_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_961_, 0, v___x_956_);
lean_ctor_set(v___x_961_, 1, v___x_958_);
lean_ctor_set(v___x_961_, 2, v___x_956_);
lean_ctor_set(v___x_961_, 3, v___x_956_);
lean_ctor_set(v___x_961_, 4, v___x_956_);
v___x_962_ = lean_apply_4(v_onAlt_951_, v___x_955_, v_resTy_952_, v___x_948_, v___x_961_);
v___x_963_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___x_962_, v___f_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_964_, lean_object* v_useSplitter_965_, lean_object* v_inst_966_, lean_object* v_onAlt_967_, lean_object* v_resTy_968_, lean_object* v_toBind_969_, lean_object* v_h_970_){
_start:
{
uint8_t v_useSplitter_boxed_971_; lean_object* v_res_972_; 
v_useSplitter_boxed_971_ = lean_unbox(v_useSplitter_965_);
v_res_972_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_964_, v_useSplitter_boxed_971_, v_inst_966_, v_onAlt_967_, v_resTy_968_, v_toBind_969_, v_h_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_973_, lean_object* v_resTy_974_, lean_object* v_c_975_, lean_object* v_h_976_, lean_object* v_t_977_, lean_object* v_toPure_978_, lean_object* v_e_979_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_980_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v_u_973_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_mkConst(v___x_980_, v___x_982_);
v___x_984_ = l_Lean_mkApp5(v___x_983_, v_resTy_974_, v_c_975_, v_h_976_, v_t_977_, v_e_979_);
v___x_985_ = lean_apply_2(v_toPure_978_, lean_box(0), v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_986_, lean_object* v_resTy_987_, lean_object* v_c_988_, lean_object* v_h_989_, lean_object* v_toPure_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_n_993_, uint8_t v___x_994_, lean_object* v___f_995_, uint8_t v___x_996_, lean_object* v_toBind_997_, lean_object* v_t_998_){
_start:
{
lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_inc_ref(v_c_988_);
v___f_999_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_999_, 0, v_u_986_);
lean_closure_set(v___f_999_, 1, v_resTy_987_);
lean_closure_set(v___f_999_, 2, v_c_988_);
lean_closure_set(v___f_999_, 3, v_h_989_);
lean_closure_set(v___f_999_, 4, v_t_998_);
lean_closure_set(v___f_999_, 5, v_toPure_990_);
v___x_1000_ = l_Lean_mkNot(v_c_988_);
v___x_1001_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_991_, v_inst_992_, v_n_993_, v___x_994_, v___x_1000_, v___f_995_, v___x_996_);
v___x_1002_ = lean_apply_4(v_toBind_997_, lean_box(0), lean_box(0), v___x_1001_, v___f_999_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_1003_, lean_object* v_resTy_1004_, lean_object* v_c_1005_, lean_object* v_h_1006_, lean_object* v_toPure_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_n_1010_, lean_object* v___x_1011_, lean_object* v___f_1012_, lean_object* v___x_1013_, lean_object* v_toBind_1014_, lean_object* v_t_1015_){
_start:
{
uint8_t v___x_1249__boxed_1016_; uint8_t v___x_1251__boxed_1017_; lean_object* v_res_1018_; 
v___x_1249__boxed_1016_ = lean_unbox(v___x_1011_);
v___x_1251__boxed_1017_ = lean_unbox(v___x_1013_);
v_res_1018_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_1003_, v_resTy_1004_, v_c_1005_, v_h_1006_, v_toPure_1007_, v_inst_1008_, v_inst_1009_, v_n_1010_, v___x_1249__boxed_1016_, v___f_1012_, v___x_1251__boxed_1017_, v_toBind_1014_, v_t_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_1019_, lean_object* v_resTy_1020_, lean_object* v_c_1021_, lean_object* v_h_1022_, lean_object* v_toPure_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v___f_1026_, lean_object* v_toBind_1027_, lean_object* v___f_1028_, lean_object* v_n_1029_){
_start:
{
uint8_t v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1030_ = 0;
v___x_1031_ = 0;
v___x_1032_ = lean_box(v___x_1030_);
v___x_1033_ = lean_box(v___x_1031_);
lean_inc(v_toBind_1027_);
lean_inc(v_n_1029_);
lean_inc_ref(v_inst_1025_);
lean_inc_ref(v_inst_1024_);
lean_inc_ref(v_c_1021_);
v___f_1034_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1034_, 0, v_u_1019_);
lean_closure_set(v___f_1034_, 1, v_resTy_1020_);
lean_closure_set(v___f_1034_, 2, v_c_1021_);
lean_closure_set(v___f_1034_, 3, v_h_1022_);
lean_closure_set(v___f_1034_, 4, v_toPure_1023_);
lean_closure_set(v___f_1034_, 5, v_inst_1024_);
lean_closure_set(v___f_1034_, 6, v_inst_1025_);
lean_closure_set(v___f_1034_, 7, v_n_1029_);
lean_closure_set(v___f_1034_, 8, v___x_1032_);
lean_closure_set(v___f_1034_, 9, v___f_1026_);
lean_closure_set(v___f_1034_, 10, v___x_1033_);
lean_closure_set(v___f_1034_, 11, v_toBind_1027_);
v___x_1035_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1024_, v_inst_1025_, v_n_1029_, v___x_1030_, v_c_1021_, v___f_1028_, v___x_1031_);
v___x_1036_ = lean_apply_4(v_toBind_1027_, lean_box(0), lean_box(0), v___x_1035_, v___f_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Core_mkFreshUserName(v___x_1037_, v___y_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1058_, uint8_t v_useSplitter_1059_, lean_object* v_resTy_1060_, lean_object* v_toPure_1061_, lean_object* v_onAlt_1062_, lean_object* v_toBind_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_u_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_c_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_h_1076_; 
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = l_Lean_Expr_getAppNumArgs(v_e_1058_);
v___x_1070_ = lean_nat_sub(v___x_1069_, v___x_1068_);
v___x_1071_ = lean_nat_sub(v___x_1070_, v___x_1068_);
lean_dec(v___x_1070_);
v_c_1072_ = l_Lean_Expr_getRevArg_x21(v_e_1058_, v___x_1071_);
v___x_1073_ = lean_unsigned_to_nat(2u);
v___x_1074_ = lean_nat_sub(v___x_1069_, v___x_1073_);
lean_dec(v___x_1069_);
v___x_1075_ = lean_nat_sub(v___x_1074_, v___x_1068_);
lean_dec(v___x_1074_);
v_h_1076_ = l_Lean_Expr_getRevArg_x21(v_e_1058_, v___x_1075_);
if (v_useSplitter_1059_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v_inst_1066_);
lean_dec_ref(v_inst_1065_);
lean_dec(v_inst_1064_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1063_);
lean_inc(v_onAlt_1062_);
lean_inc_ref(v_resTy_1060_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1080_, 0, v_u_1067_);
lean_closure_set(v___f_1080_, 1, v_resTy_1060_);
lean_closure_set(v___f_1080_, 2, v_c_1072_);
lean_closure_set(v___f_1080_, 3, v_h_1076_);
lean_closure_set(v___f_1080_, 4, v_toPure_1061_);
lean_closure_set(v___f_1080_, 5, v_onAlt_1062_);
lean_closure_set(v___f_1080_, 6, v___x_1068_);
lean_closure_set(v___f_1080_, 7, v___x_1079_);
lean_closure_set(v___f_1080_, 8, v_toBind_1063_);
v___x_1081_ = lean_apply_4(v_onAlt_1062_, v___x_1077_, v_resTy_1060_, v___x_1078_, v___x_1079_);
v___x_1082_ = lean_apply_4(v_toBind_1063_, lean_box(0), lean_box(0), v___x_1081_, v___f_1080_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___f_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1083_ = lean_box(v_useSplitter_1059_);
lean_inc_n(v_toBind_1063_, 3);
lean_inc_ref_n(v_resTy_1060_, 2);
lean_inc(v_onAlt_1062_);
lean_inc_n(v_inst_1064_, 2);
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1084_, 0, v___x_1068_);
lean_closure_set(v___f_1084_, 1, v___x_1083_);
lean_closure_set(v___f_1084_, 2, v_inst_1064_);
lean_closure_set(v___f_1084_, 3, v_onAlt_1062_);
lean_closure_set(v___f_1084_, 4, v_resTy_1060_);
lean_closure_set(v___f_1084_, 5, v_toBind_1063_);
v___x_1085_ = lean_box(v_useSplitter_1059_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1086_, 0, v___x_1068_);
lean_closure_set(v___f_1086_, 1, v___x_1085_);
lean_closure_set(v___f_1086_, 2, v_inst_1064_);
lean_closure_set(v___f_1086_, 3, v_onAlt_1062_);
lean_closure_set(v___f_1086_, 4, v_resTy_1060_);
lean_closure_set(v___f_1086_, 5, v_toBind_1063_);
v___f_1087_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1087_, 0, v_u_1067_);
lean_closure_set(v___f_1087_, 1, v_resTy_1060_);
lean_closure_set(v___f_1087_, 2, v_c_1072_);
lean_closure_set(v___f_1087_, 3, v_h_1076_);
lean_closure_set(v___f_1087_, 4, v_toPure_1061_);
lean_closure_set(v___f_1087_, 5, v_inst_1065_);
lean_closure_set(v___f_1087_, 6, v_inst_1066_);
lean_closure_set(v___f_1087_, 7, v___f_1086_);
lean_closure_set(v___f_1087_, 8, v_toBind_1063_);
lean_closure_set(v___f_1087_, 9, v___f_1084_);
v___f_1088_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1089_ = lean_apply_2(v_inst_1064_, lean_box(0), v___f_1088_);
v___x_1090_ = lean_apply_4(v_toBind_1063_, lean_box(0), lean_box(0), v___x_1089_, v___f_1087_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1091_, lean_object* v_useSplitter_1092_, lean_object* v_resTy_1093_, lean_object* v_toPure_1094_, lean_object* v_onAlt_1095_, lean_object* v_toBind_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_u_1100_){
_start:
{
uint8_t v_useSplitter_boxed_1101_; lean_object* v_res_1102_; 
v_useSplitter_boxed_1101_ = lean_unbox(v_useSplitter_1092_);
v_res_1102_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1091_, v_useSplitter_boxed_1101_, v_resTy_1093_, v_toPure_1094_, v_onAlt_1095_, v_toBind_1096_, v_inst_1097_, v_inst_1098_, v_inst_1099_, v_u_1100_);
lean_dec_ref(v_e_1091_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1103_, lean_object* v_inst_1104_, lean_object* v_____do__lift_1105_){
_start:
{
uint8_t v___x_1106_; uint8_t v___x_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1106_ = 0;
v___x_1107_ = 1;
v___x_1108_ = 1;
v___x_1109_ = lean_box(v___x_1106_);
v___x_1110_ = lean_box(v___x_1107_);
v___x_1111_ = lean_box(v___x_1106_);
v___x_1112_ = lean_box(v___x_1107_);
v___x_1113_ = lean_box(v___x_1108_);
v___x_1114_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1114_, 0, v___x_1103_);
lean_closure_set(v___x_1114_, 1, v_____do__lift_1105_);
lean_closure_set(v___x_1114_, 2, v___x_1109_);
lean_closure_set(v___x_1114_, 3, v___x_1110_);
lean_closure_set(v___x_1114_, 4, v___x_1111_);
lean_closure_set(v___x_1114_, 5, v___x_1112_);
lean_closure_set(v___x_1114_, 6, v___x_1113_);
v___x_1115_ = lean_apply_2(v_inst_1104_, lean_box(0), v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1116_, lean_object* v_onAlt_1117_, lean_object* v_resTy_1118_, lean_object* v_toBind_1119_, lean_object* v_h_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1121_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_mk_empty_array_with_capacity(v___x_1123_);
v___x_1125_ = lean_array_push(v___x_1124_, v_h_1120_);
lean_inc_ref_n(v___x_1125_, 2);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1126_, 0, v___x_1125_);
lean_closure_set(v___f_1126_, 1, v_inst_1116_);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_1128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1125_);
lean_ctor_set(v___x_1128_, 1, v___x_1125_);
lean_ctor_set(v___x_1128_, 2, v___x_1127_);
lean_ctor_set(v___x_1128_, 3, v___x_1127_);
lean_ctor_set(v___x_1128_, 4, v___x_1127_);
v___x_1129_ = lean_apply_4(v_onAlt_1117_, v___x_1121_, v_resTy_1118_, v___x_1122_, v___x_1128_);
v___x_1130_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1129_, v___f_1126_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1131_, lean_object* v_inst_1132_, lean_object* v_onAlt_1133_, lean_object* v_resTy_1134_, lean_object* v_toBind_1135_, lean_object* v_h_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1137_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1138_ = lean_mk_empty_array_with_capacity(v___x_1131_);
v___x_1139_ = lean_array_push(v___x_1138_, v_h_1136_);
lean_inc_ref_n(v___x_1139_, 2);
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1140_, 0, v___x_1139_);
lean_closure_set(v___f_1140_, 1, v_inst_1132_);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_1142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1139_);
lean_ctor_set(v___x_1142_, 1, v___x_1139_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
lean_ctor_set(v___x_1142_, 3, v___x_1141_);
lean_ctor_set(v___x_1142_, 4, v___x_1141_);
v___x_1143_ = lean_apply_4(v_onAlt_1133_, v___x_1137_, v_resTy_1134_, v___x_1131_, v___x_1142_);
v___x_1144_ = lean_apply_4(v_toBind_1135_, lean_box(0), lean_box(0), v___x_1143_, v___f_1140_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1145_, lean_object* v_onAlt_1146_, lean_object* v_resTy_1147_, lean_object* v_toBind_1148_, lean_object* v_e_1149_, lean_object* v_toPure_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v___f_1153_, lean_object* v_u_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_c_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_h_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1155_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_toBind_1148_, 2);
lean_inc_ref(v_resTy_1147_);
lean_inc(v_inst_1145_);
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1156_, 0, v___x_1155_);
lean_closure_set(v___f_1156_, 1, v_inst_1145_);
lean_closure_set(v___f_1156_, 2, v_onAlt_1146_);
lean_closure_set(v___f_1156_, 3, v_resTy_1147_);
lean_closure_set(v___f_1156_, 4, v_toBind_1148_);
v___x_1157_ = l_Lean_Expr_getAppNumArgs(v_e_1149_);
v___x_1158_ = lean_nat_sub(v___x_1157_, v___x_1155_);
v___x_1159_ = lean_nat_sub(v___x_1158_, v___x_1155_);
lean_dec(v___x_1158_);
v_c_1160_ = l_Lean_Expr_getRevArg_x21(v_e_1149_, v___x_1159_);
v___x_1161_ = lean_unsigned_to_nat(2u);
v___x_1162_ = lean_nat_sub(v___x_1157_, v___x_1161_);
lean_dec(v___x_1157_);
v___x_1163_ = lean_nat_sub(v___x_1162_, v___x_1155_);
lean_dec(v___x_1162_);
v_h_1164_ = l_Lean_Expr_getRevArg_x21(v_e_1149_, v___x_1163_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1165_, 0, v_u_1154_);
lean_closure_set(v___f_1165_, 1, v_resTy_1147_);
lean_closure_set(v___f_1165_, 2, v_c_1160_);
lean_closure_set(v___f_1165_, 3, v_h_1164_);
lean_closure_set(v___f_1165_, 4, v_toPure_1150_);
lean_closure_set(v___f_1165_, 5, v_inst_1151_);
lean_closure_set(v___f_1165_, 6, v_inst_1152_);
lean_closure_set(v___f_1165_, 7, v___f_1156_);
lean_closure_set(v___f_1165_, 8, v_toBind_1148_);
lean_closure_set(v___f_1165_, 9, v___f_1153_);
v___f_1166_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1167_ = lean_apply_2(v_inst_1145_, lean_box(0), v___f_1166_);
v___x_1168_ = lean_apply_4(v_toBind_1148_, lean_box(0), lean_box(0), v___x_1167_, v___f_1165_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1169_, lean_object* v_onAlt_1170_, lean_object* v_resTy_1171_, lean_object* v_toBind_1172_, lean_object* v_e_1173_, lean_object* v_toPure_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v___f_1177_, lean_object* v_u_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1169_, v_onAlt_1170_, v_resTy_1171_, v_toBind_1172_, v_e_1173_, v_toPure_1174_, v_inst_1175_, v_inst_1176_, v___f_1177_, v_u_1178_);
lean_dec_ref(v_e_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_onAlt_1180_, lean_object* v_idx_1181_, lean_object* v_expAltType_1182_, lean_object* v_altFVars_1183_, lean_object* v___alt_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_nat_add(v_idx_1181_, v___x_1186_);
v___x_1188_ = lean_name_append_index_after(v___x_1185_, v___x_1187_);
v___x_1189_ = lean_apply_4(v_onAlt_1180_, v___x_1188_, v_expAltType_1182_, v_idx_1181_, v_altFVars_1183_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(lean_object* v_onAlt_1190_, lean_object* v_idx_1191_, lean_object* v_expAltType_1192_, lean_object* v_altFVars_1193_, lean_object* v___alt_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(v_onAlt_1190_, v_idx_1191_, v_expAltType_1192_, v_altFVars_1193_, v___alt_1194_);
lean_dec_ref(v___alt_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_mask_1196_, lean_object* v_absMotiveBody_1197_, lean_object* v_toPure_1198_, lean_object* v_xs_1199_, lean_object* v___body_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = l_Lean_Array_mask___redArg(v_mask_1196_, v_xs_1199_);
v___x_1202_ = lean_expr_instantiate_rev(v_absMotiveBody_1197_, v___x_1201_);
lean_dec(v___x_1201_);
v___x_1203_ = lean_apply_2(v_toPure_1198_, lean_box(0), v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(lean_object* v_mask_1204_, lean_object* v_absMotiveBody_1205_, lean_object* v_toPure_1206_, lean_object* v_xs_1207_, lean_object* v___body_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(v_mask_1204_, v_absMotiveBody_1205_, v_toPure_1206_, v_xs_1207_, v___body_1208_);
lean_dec_ref(v___body_1208_);
lean_dec_ref(v_absMotiveBody_1205_);
lean_dec_ref(v_mask_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v_toFunctor_1210_, lean_object* v_mask_1211_, lean_object* v_toPure_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_matcherApp_1218_, uint8_t v_useSplitter_1219_, lean_object* v___f_1220_, lean_object* v___f_1221_, lean_object* v_absMotiveBody_1222_){
_start:
{
lean_object* v_map_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_map_1223_ = lean_ctor_get(v_toFunctor_1210_, 0);
lean_inc(v_map_1223_);
lean_dec_ref(v_toFunctor_1210_);
lean_inc(v_toPure_1212_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed), 5, 3);
lean_closure_set(v___f_1224_, 0, v_mask_1211_);
lean_closure_set(v___f_1224_, 1, v_absMotiveBody_1222_);
lean_closure_set(v___f_1224_, 2, v_toPure_1212_);
v___x_1225_ = lean_apply_1(v_toPure_1212_, lean_box(0));
lean_inc(v___x_1225_);
v___x_1226_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1213_, v_inst_1214_, v_inst_1215_, v_inst_1216_, v_inst_1217_, v_matcherApp_1218_, v_useSplitter_1219_, v_useSplitter_1219_, v___x_1225_, v___f_1224_, v___f_1220_, v___x_1225_);
v___x_1227_ = lean_apply_4(v_map_1223_, lean_box(0), lean_box(0), v___f_1221_, v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v_toFunctor_1228_, lean_object* v_mask_1229_, lean_object* v_toPure_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_, lean_object* v_matcherApp_1236_, lean_object* v_useSplitter_1237_, lean_object* v___f_1238_, lean_object* v___f_1239_, lean_object* v_absMotiveBody_1240_){
_start:
{
uint8_t v_useSplitter_boxed_1241_; lean_object* v_res_1242_; 
v_useSplitter_boxed_1241_ = lean_unbox(v_useSplitter_1237_);
v_res_1242_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v_toFunctor_1228_, v_mask_1229_, v_toPure_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_inst_1234_, v_inst_1235_, v_matcherApp_1236_, v_useSplitter_boxed_1241_, v___f_1238_, v___f_1239_, v_absMotiveBody_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_info_1250_, lean_object* v_resTy_1251_, lean_object* v_onAlt_1252_, uint8_t v_useSplitter_1253_){
_start:
{
switch(lean_obj_tag(v_info_1250_))
{
case 0:
{
lean_object* v_toApplicative_1254_; lean_object* v_toBind_1255_; lean_object* v_toPure_1256_; lean_object* v_e_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_toApplicative_1254_ = lean_ctor_get(v_inst_1247_, 0);
lean_dec_ref(v_inst_1249_);
lean_dec_ref(v_inst_1248_);
v_toBind_1255_ = lean_ctor_get(v_inst_1247_, 1);
lean_inc_n(v_toBind_1255_, 2);
v_toPure_1256_ = lean_ctor_get(v_toApplicative_1254_, 1);
lean_inc(v_toPure_1256_);
v_e_1257_ = lean_ctor_get(v_info_1250_, 0);
lean_inc_ref(v_e_1257_);
lean_dec_ref_known(v_info_1250_, 1);
v___x_1258_ = lean_box(v_useSplitter_1253_);
lean_inc(v_inst_1245_);
lean_inc_ref(v_resTy_1251_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1259_, 0, v_e_1257_);
lean_closure_set(v___f_1259_, 1, v___x_1258_);
lean_closure_set(v___f_1259_, 2, v_resTy_1251_);
lean_closure_set(v___f_1259_, 3, v_toPure_1256_);
lean_closure_set(v___f_1259_, 4, v_onAlt_1252_);
lean_closure_set(v___f_1259_, 5, v_toBind_1255_);
lean_closure_set(v___f_1259_, 6, v_inst_1245_);
lean_closure_set(v___f_1259_, 7, v_inst_1246_);
lean_closure_set(v___f_1259_, 8, v_inst_1247_);
v___x_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1260_, 0, v_resTy_1251_);
v___x_1261_ = lean_apply_2(v_inst_1245_, lean_box(0), v___x_1260_);
v___x_1262_ = lean_apply_4(v_toBind_1255_, lean_box(0), lean_box(0), v___x_1261_, v___f_1259_);
return v___x_1262_;
}
case 1:
{
lean_object* v_toApplicative_1263_; lean_object* v_toBind_1264_; lean_object* v_toPure_1265_; lean_object* v_e_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_toApplicative_1263_ = lean_ctor_get(v_inst_1247_, 0);
lean_dec_ref(v_inst_1249_);
lean_dec_ref(v_inst_1248_);
v_toBind_1264_ = lean_ctor_get(v_inst_1247_, 1);
lean_inc_n(v_toBind_1264_, 3);
v_toPure_1265_ = lean_ctor_get(v_toApplicative_1263_, 1);
lean_inc(v_toPure_1265_);
v_e_1266_ = lean_ctor_get(v_info_1250_, 0);
lean_inc_ref(v_e_1266_);
lean_dec_ref_known(v_info_1250_, 1);
lean_inc_ref_n(v_resTy_1251_, 2);
lean_inc(v_onAlt_1252_);
lean_inc_n(v_inst_1245_, 2);
v___f_1267_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1267_, 0, v_inst_1245_);
lean_closure_set(v___f_1267_, 1, v_onAlt_1252_);
lean_closure_set(v___f_1267_, 2, v_resTy_1251_);
lean_closure_set(v___f_1267_, 3, v_toBind_1264_);
v___f_1268_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1268_, 0, v_inst_1245_);
lean_closure_set(v___f_1268_, 1, v_onAlt_1252_);
lean_closure_set(v___f_1268_, 2, v_resTy_1251_);
lean_closure_set(v___f_1268_, 3, v_toBind_1264_);
lean_closure_set(v___f_1268_, 4, v_e_1266_);
lean_closure_set(v___f_1268_, 5, v_toPure_1265_);
lean_closure_set(v___f_1268_, 6, v_inst_1246_);
lean_closure_set(v___f_1268_, 7, v_inst_1247_);
lean_closure_set(v___f_1268_, 8, v___f_1267_);
v___x_1269_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1269_, 0, v_resTy_1251_);
v___x_1270_ = lean_apply_2(v_inst_1245_, lean_box(0), v___x_1269_);
v___x_1271_ = lean_apply_4(v_toBind_1264_, lean_box(0), lean_box(0), v___x_1270_, v___f_1268_);
return v___x_1271_;
}
default: 
{
lean_object* v_toApplicative_1272_; lean_object* v_matcherApp_1273_; lean_object* v_toBind_1274_; lean_object* v_toFunctor_1275_; lean_object* v_toPure_1276_; lean_object* v_discrs_1277_; lean_object* v___f_1278_; lean_object* v___f_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; size_t v_sz_1282_; size_t v___x_1283_; lean_object* v_mask_1284_; lean_object* v___x_1285_; lean_object* v___f_1286_; lean_object* v_maskedDiscrs_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_toApplicative_1272_ = lean_ctor_get(v_inst_1247_, 0);
v_matcherApp_1273_ = lean_ctor_get(v_info_1250_, 0);
lean_inc_ref(v_matcherApp_1273_);
lean_dec_ref_known(v_info_1250_, 1);
v_toBind_1274_ = lean_ctor_get(v_inst_1247_, 1);
lean_inc(v_toBind_1274_);
v_toFunctor_1275_ = lean_ctor_get(v_toApplicative_1272_, 0);
lean_inc_ref(v_toFunctor_1275_);
v_toPure_1276_ = lean_ctor_get(v_toApplicative_1272_, 1);
lean_inc(v_toPure_1276_);
v_discrs_1277_ = lean_ctor_get(v_matcherApp_1273_, 5);
lean_inc_ref_n(v_discrs_1277_, 2);
v___f_1278_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed), 5, 1);
lean_closure_set(v___f_1279_, 0, v_onAlt_1252_);
v___f_1280_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1));
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v_sz_1282_ = lean_array_size(v_discrs_1277_);
v___x_1283_ = ((size_t)0ULL);
v_mask_1284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1281_, v___f_1280_, v_sz_1282_, v___x_1283_, v_discrs_1277_);
v___x_1285_ = lean_box(v_useSplitter_1253_);
lean_inc(v_inst_1245_);
lean_inc(v_mask_1284_);
v___f_1286_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 13, 12);
lean_closure_set(v___f_1286_, 0, v_toFunctor_1275_);
lean_closure_set(v___f_1286_, 1, v_mask_1284_);
lean_closure_set(v___f_1286_, 2, v_toPure_1276_);
lean_closure_set(v___f_1286_, 3, v_inst_1245_);
lean_closure_set(v___f_1286_, 4, v_inst_1246_);
lean_closure_set(v___f_1286_, 5, v_inst_1247_);
lean_closure_set(v___f_1286_, 6, v_inst_1248_);
lean_closure_set(v___f_1286_, 7, v_inst_1249_);
lean_closure_set(v___f_1286_, 8, v_matcherApp_1273_);
lean_closure_set(v___f_1286_, 9, v___x_1285_);
lean_closure_set(v___f_1286_, 10, v___f_1279_);
lean_closure_set(v___f_1286_, 11, v___f_1278_);
v_maskedDiscrs_1287_ = l_Lean_Array_mask___redArg(v_mask_1284_, v_discrs_1277_);
lean_dec(v_mask_1284_);
v___x_1288_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1288_, 0, v_resTy_1251_);
lean_closure_set(v___x_1288_, 1, v_maskedDiscrs_1287_);
v___x_1289_ = lean_apply_2(v_inst_1245_, lean_box(0), v___x_1288_);
v___x_1290_ = lean_apply_4(v_toBind_1274_, lean_box(0), lean_box(0), v___x_1289_, v___f_1286_);
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_info_1296_, lean_object* v_resTy_1297_, lean_object* v_onAlt_1298_, lean_object* v_useSplitter_1299_){
_start:
{
uint8_t v_useSplitter_boxed_1300_; lean_object* v_res_1301_; 
v_useSplitter_boxed_1300_ = lean_unbox(v_useSplitter_1299_);
v_res_1301_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1291_, v_inst_1292_, v_inst_1293_, v_inst_1294_, v_inst_1295_, v_info_1296_, v_resTy_1297_, v_onAlt_1298_, v_useSplitter_boxed_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_info_1311_, lean_object* v_resTy_1312_, lean_object* v_onAlt_1313_, uint8_t v_useSplitter_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1303_, v_inst_1304_, v_inst_1305_, v_inst_1306_, v_inst_1307_, v_info_1311_, v_resTy_1312_, v_onAlt_1313_, v_useSplitter_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_info_1325_, lean_object* v_resTy_1326_, lean_object* v_onAlt_1327_, lean_object* v_useSplitter_1328_){
_start:
{
uint8_t v_useSplitter_boxed_1329_; lean_object* v_res_1330_; 
v_useSplitter_boxed_1329_ = lean_unbox(v_useSplitter_1328_);
v_res_1330_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1316_, v_inst_1317_, v_inst_1318_, v_inst_1319_, v_inst_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_inst_1324_, v_info_1325_, v_resTy_1326_, v_onAlt_1327_, v_useSplitter_boxed_1329_);
lean_dec(v_inst_1324_);
lean_dec(v_inst_1323_);
lean_dec_ref(v_inst_1322_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1331_, lean_object* v_e_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
if (lean_obj_tag(v_info_1331_) == 2)
{
lean_object* v_matcherApp_1341_; lean_object* v_toMatcherInfo_1342_; lean_object* v___x_1343_; 
v_matcherApp_1341_ = lean_ctor_get(v_info_1331_, 0);
lean_inc_ref(v_matcherApp_1341_);
lean_dec_ref_known(v_info_1331_, 1);
v_toMatcherInfo_1342_ = lean_ctor_get(v_matcherApp_1341_, 0);
lean_inc_ref(v_toMatcherInfo_1342_);
lean_dec_ref(v_matcherApp_1341_);
v___x_1343_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1342_, v_e_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec_ref(v_e_1332_);
lean_dec_ref(v_info_1331_);
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1346_, lean_object* v_e_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1346_, v_e_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v_env_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1360_ = lean_st_ref_get(v___y_1358_);
v_env_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc_ref(v_env_1361_);
lean_dec(v___x_1360_);
v___x_1362_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1361_, v_declName_1357_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1364_, v___y_1365_);
lean_dec(v___y_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; lean_object* v_env_1375_; lean_object* v___x_1376_; lean_object* v_mctx_1377_; lean_object* v_lctx_1378_; lean_object* v_options_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1374_ = lean_st_ref_get(v___y_1372_);
v_env_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref(v_env_1375_);
lean_dec(v___x_1374_);
v___x_1376_ = lean_st_ref_get(v___y_1370_);
v_mctx_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_mctx_1377_);
lean_dec(v___x_1376_);
v_lctx_1378_ = lean_ctor_get(v___y_1369_, 2);
v_options_1379_ = lean_ctor_get(v___y_1371_, 2);
lean_inc_ref(v_options_1379_);
lean_inc_ref(v_lctx_1378_);
v___x_1380_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1380_, 0, v_env_1375_);
lean_ctor_set(v___x_1380_, 1, v_mctx_1377_);
lean_ctor_set(v___x_1380_, 2, v_lctx_1378_);
lean_ctor_set(v___x_1380_, 3, v_options_1379_);
v___x_1381_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v_msgData_1368_);
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_ref_1396_; lean_object* v___x_1397_; lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
v_ref_1396_ = lean_ctor_get(v___y_1393_, 5);
v___x_1397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_inc(v_ref_1396_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_ref_1396_);
lean_ctor_set(v___x_1402_, 1, v_a_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set_tag(v___x_1400_, 1);
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_1414_, lean_object* v_msg_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_fileName_1421_; lean_object* v_fileMap_1422_; lean_object* v_options_1423_; lean_object* v_currRecDepth_1424_; lean_object* v_maxRecDepth_1425_; lean_object* v_ref_1426_; lean_object* v_currNamespace_1427_; lean_object* v_openDecls_1428_; lean_object* v_initHeartbeats_1429_; lean_object* v_maxHeartbeats_1430_; lean_object* v_quotContext_1431_; lean_object* v_currMacroScope_1432_; uint8_t v_diag_1433_; lean_object* v_cancelTk_x3f_1434_; uint8_t v_suppressElabErrors_1435_; lean_object* v_inheritedTraceOptions_1436_; lean_object* v_ref_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_fileName_1421_ = lean_ctor_get(v___y_1418_, 0);
v_fileMap_1422_ = lean_ctor_get(v___y_1418_, 1);
v_options_1423_ = lean_ctor_get(v___y_1418_, 2);
v_currRecDepth_1424_ = lean_ctor_get(v___y_1418_, 3);
v_maxRecDepth_1425_ = lean_ctor_get(v___y_1418_, 4);
v_ref_1426_ = lean_ctor_get(v___y_1418_, 5);
v_currNamespace_1427_ = lean_ctor_get(v___y_1418_, 6);
v_openDecls_1428_ = lean_ctor_get(v___y_1418_, 7);
v_initHeartbeats_1429_ = lean_ctor_get(v___y_1418_, 8);
v_maxHeartbeats_1430_ = lean_ctor_get(v___y_1418_, 9);
v_quotContext_1431_ = lean_ctor_get(v___y_1418_, 10);
v_currMacroScope_1432_ = lean_ctor_get(v___y_1418_, 11);
v_diag_1433_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*14);
v_cancelTk_x3f_1434_ = lean_ctor_get(v___y_1418_, 12);
v_suppressElabErrors_1435_ = lean_ctor_get_uint8(v___y_1418_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1436_ = lean_ctor_get(v___y_1418_, 13);
v_ref_1437_ = l_Lean_replaceRef(v_ref_1414_, v_ref_1426_);
lean_inc_ref(v_inheritedTraceOptions_1436_);
lean_inc(v_cancelTk_x3f_1434_);
lean_inc(v_currMacroScope_1432_);
lean_inc(v_quotContext_1431_);
lean_inc(v_maxHeartbeats_1430_);
lean_inc(v_initHeartbeats_1429_);
lean_inc(v_openDecls_1428_);
lean_inc(v_currNamespace_1427_);
lean_inc(v_maxRecDepth_1425_);
lean_inc(v_currRecDepth_1424_);
lean_inc_ref(v_options_1423_);
lean_inc_ref(v_fileMap_1422_);
lean_inc_ref(v_fileName_1421_);
v___x_1438_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1438_, 0, v_fileName_1421_);
lean_ctor_set(v___x_1438_, 1, v_fileMap_1422_);
lean_ctor_set(v___x_1438_, 2, v_options_1423_);
lean_ctor_set(v___x_1438_, 3, v_currRecDepth_1424_);
lean_ctor_set(v___x_1438_, 4, v_maxRecDepth_1425_);
lean_ctor_set(v___x_1438_, 5, v_ref_1437_);
lean_ctor_set(v___x_1438_, 6, v_currNamespace_1427_);
lean_ctor_set(v___x_1438_, 7, v_openDecls_1428_);
lean_ctor_set(v___x_1438_, 8, v_initHeartbeats_1429_);
lean_ctor_set(v___x_1438_, 9, v_maxHeartbeats_1430_);
lean_ctor_set(v___x_1438_, 10, v_quotContext_1431_);
lean_ctor_set(v___x_1438_, 11, v_currMacroScope_1432_);
lean_ctor_set(v___x_1438_, 12, v_cancelTk_x3f_1434_);
lean_ctor_set(v___x_1438_, 13, v_inheritedTraceOptions_1436_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*14, v_diag_1433_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*14 + 1, v_suppressElabErrors_1435_);
v___x_1439_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1415_, v___y_1416_, v___y_1417_, v___x_1438_, v___y_1419_);
lean_dec_ref_known(v___x_1438_, 14);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1440_, v_msg_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v_ref_1440_);
return v_res_1447_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
lean_ctor_set(v___x_1453_, 2, v___x_1452_);
lean_ctor_set(v___x_1453_, 3, v___x_1452_);
lean_ctor_set(v___x_1453_, 4, v___x_1451_);
lean_ctor_set(v___x_1453_, 5, v___x_1451_);
lean_ctor_set(v___x_1453_, 6, v___x_1451_);
lean_ctor_set(v___x_1453_, 7, v___x_1451_);
lean_ctor_set(v___x_1453_, 8, v___x_1451_);
lean_ctor_set(v___x_1453_, 9, v___x_1451_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_unsigned_to_nat(32u);
v___x_1455_ = lean_mk_empty_array_with_capacity(v___x_1454_);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1457_ = ((size_t)5ULL);
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = lean_unsigned_to_nat(32u);
v___x_1460_ = lean_mk_empty_array_with_capacity(v___x_1459_);
v___x_1461_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1462_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___x_1460_);
lean_ctor_set(v___x_1462_, 2, v___x_1458_);
lean_ctor_set(v___x_1462_, 3, v___x_1458_);
lean_ctor_set_usize(v___x_1462_, 4, v___x_1457_);
return v___x_1462_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1463_ = lean_box(1);
v___x_1464_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1466_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
lean_ctor_set(v___x_1466_, 1, v___x_1464_);
lean_ctor_set(v___x_1466_, 2, v___x_1463_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1469_ = l_Lean_stringToMessageData(v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1472_ = l_Lean_stringToMessageData(v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1475_ = l_Lean_stringToMessageData(v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1481_ = l_Lean_stringToMessageData(v___x_1480_);
return v___x_1481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1484_ = l_Lean_stringToMessageData(v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1487_ = l_Lean_stringToMessageData(v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1488_, lean_object* v_declHint_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v_env_1493_; uint8_t v___y_1495_; uint8_t v___x_1551_; uint8_t v___x_1552_; 
v___x_1492_ = lean_st_ref_get(v___y_1490_);
v_env_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc_ref(v_env_1493_);
lean_dec(v___x_1492_);
v___x_1551_ = l_Lean_Name_isAnonymous(v_declHint_1489_);
v___x_1552_ = lean_bool_not(v___x_1551_);
if (v___x_1552_ == 0)
{
v___y_1495_ = v___x_1552_;
goto v___jp_1494_;
}
else
{
uint8_t v_isExporting_1553_; 
v_isExporting_1553_ = lean_ctor_get_uint8(v_env_1493_, sizeof(void*)*8);
v___y_1495_ = v_isExporting_1553_;
goto v___jp_1494_;
}
v___jp_1494_:
{
if (v___y_1495_ == 0)
{
lean_object* v___x_1496_; 
lean_dec_ref(v_env_1493_);
lean_dec(v_declHint_1489_);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_msg_1488_);
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v___x_1497_ = 0;
lean_inc_ref(v_env_1493_);
v___x_1498_ = l_Lean_Environment_setExporting(v_env_1493_, v___x_1497_);
lean_inc(v_declHint_1489_);
lean_inc_ref(v___x_1498_);
v___x_1499_ = l_Lean_Environment_contains(v___x_1498_, v_declHint_1489_, v___y_1495_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; 
lean_dec_ref(v___x_1498_);
lean_dec_ref(v_env_1493_);
lean_dec(v_declHint_1489_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_msg_1488_);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_c_1506_; lean_object* v___x_1507_; 
v___x_1501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1502_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1503_ = l_Lean_Options_empty;
v___x_1504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1498_);
lean_ctor_set(v___x_1504_, 1, v___x_1501_);
lean_ctor_set(v___x_1504_, 2, v___x_1502_);
lean_ctor_set(v___x_1504_, 3, v___x_1503_);
lean_inc(v_declHint_1489_);
v___x_1505_ = l_Lean_MessageData_ofConstName(v_declHint_1489_, v___x_1497_);
v_c_1506_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1506_, 0, v___x_1504_);
lean_ctor_set(v_c_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1493_, v_declHint_1489_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref(v_env_1493_);
lean_dec(v_declHint_1489_);
v___x_1508_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v_c_1506_);
v___x_1510_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = l_Lean_MessageData_note(v___x_1511_);
v___x_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_msg_1488_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
else
{
lean_object* v_val_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1550_; 
v_val_1515_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1517_ = v___x_1507_;
v_isShared_1518_ = v_isSharedCheck_1550_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_val_1515_);
lean_dec(v___x_1507_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1550_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v_mod_1522_; uint8_t v___x_1523_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = l_Lean_Environment_header(v_env_1493_);
lean_dec_ref(v_env_1493_);
v___x_1521_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1520_);
v_mod_1522_ = lean_array_get(v___x_1519_, v___x_1521_, v_val_1515_);
lean_dec(v_val_1515_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l_Lean_isPrivateName(v_declHint_1489_);
lean_dec(v_declHint_1489_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1524_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v_c_1506_);
v___x_1526_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = l_Lean_MessageData_ofName(v_mod_1522_);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = l_Lean_MessageData_note(v___x_1531_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v_msg_1488_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1533_);
v___x_1535_ = v___x_1517_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v_c_1506_);
v___x_1539_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_MessageData_ofName(v_mod_1522_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = l_Lean_MessageData_note(v___x_1544_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v_msg_1488_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1546_);
v___x_1548_ = v___x_1517_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1554_, lean_object* v_declHint_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1554_, v_declHint_1555_, v___y_1556_);
lean_dec(v___y_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1559_, lean_object* v_declHint_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1576_; 
v___x_1566_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1559_, v_declHint_1560_, v___y_1564_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1576_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1576_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = l_Lean_unknownIdentifierMessageTag;
v___x_1572_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v_a_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1572_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1577_, lean_object* v_declHint_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1577_, v_declHint_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1585_, lean_object* v_msg_1586_, lean_object* v_declHint_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v_a_1594_; lean_object* v___x_1595_; 
v___x_1593_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1586_, v_declHint_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1585_, v_a_1594_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1596_, lean_object* v_msg_1597_, lean_object* v_declHint_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1596_, v_msg_1597_, v_declHint_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v_ref_1596_);
return v_res_1604_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1611_, lean_object* v_constName_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1618_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1619_ = 0;
lean_inc(v_constName_1612_);
v___x_1620_ = l_Lean_MessageData_ofConstName(v_constName_1612_, v___x_1619_);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1618_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1611_, v___x_1623_, v_constName_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1625_, lean_object* v_constName_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1625_, v_constName_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v_ref_1625_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_ref_1639_; lean_object* v___x_1640_; 
v_ref_1639_ = lean_ctor_get(v___y_1636_, 5);
v___x_1640_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1639_, v_constName_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v_env_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; 
v___x_1654_ = lean_st_ref_get(v___y_1652_);
v_env_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc_ref(v_env_1655_);
lean_dec(v___x_1654_);
v___x_1656_ = 0;
lean_inc(v_constName_1648_);
v___x_1657_ = l_Lean_Environment_find_x3f(v_env_1655_, v_constName_1648_, v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v___x_1658_;
}
else
{
lean_object* v_val_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_constName_1648_);
v_val_1659_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1657_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_val_1659_);
lean_dec(v___x_1657_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set_tag(v___x_1661_, 0);
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_val_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; lean_object* v_toApplicative_1681_; lean_object* v_toFunctor_1682_; lean_object* v_toSeq_1683_; lean_object* v_toSeqLeft_1684_; lean_object* v_toSeqRight_1685_; lean_object* v___f_1686_; lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___f_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_toApplicative_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1728_; 
v___x_1680_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_1681_ = lean_ctor_get(v___x_1680_, 0);
v_toFunctor_1682_ = lean_ctor_get(v_toApplicative_1681_, 0);
v_toSeq_1683_ = lean_ctor_get(v_toApplicative_1681_, 2);
v_toSeqLeft_1684_ = lean_ctor_get(v_toApplicative_1681_, 3);
v_toSeqRight_1685_ = lean_ctor_get(v_toApplicative_1681_, 4);
v___f_1686_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_1687_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1682_, 2);
v___f_1688_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1688_, 0, v_toFunctor_1682_);
v___f_1689_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1689_, 0, v_toFunctor_1682_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___f_1688_);
lean_ctor_set(v___x_1690_, 1, v___f_1689_);
lean_inc(v_toSeqRight_1685_);
v___f_1691_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1691_, 0, v_toSeqRight_1685_);
lean_inc(v_toSeqLeft_1684_);
v___f_1692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1692_, 0, v_toSeqLeft_1684_);
lean_inc(v_toSeq_1683_);
v___f_1693_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1693_, 0, v_toSeq_1683_);
v___x_1694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1690_);
lean_ctor_set(v___x_1694_, 1, v___f_1686_);
lean_ctor_set(v___x_1694_, 2, v___f_1693_);
lean_ctor_set(v___x_1694_, 3, v___f_1692_);
lean_ctor_set(v___x_1694_, 4, v___f_1691_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___f_1687_);
v___x_1696_ = l_StateRefT_x27_instMonad___redArg(v___x_1695_);
v_toApplicative_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v___x_1696_, 1);
lean_dec(v_unused_1729_);
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1728_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_toApplicative_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1728_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v_toFunctor_1701_; lean_object* v_toSeq_1702_; lean_object* v_toSeqLeft_1703_; lean_object* v_toSeqRight_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1726_; 
v_toFunctor_1701_ = lean_ctor_get(v_toApplicative_1697_, 0);
v_toSeq_1702_ = lean_ctor_get(v_toApplicative_1697_, 2);
v_toSeqLeft_1703_ = lean_ctor_get(v_toApplicative_1697_, 3);
v_toSeqRight_1704_ = lean_ctor_get(v_toApplicative_1697_, 4);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_toApplicative_1697_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v_toApplicative_1697_, 1);
lean_dec(v_unused_1727_);
v___x_1706_ = v_toApplicative_1697_;
v_isShared_1707_ = v_isSharedCheck_1726_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_toSeqRight_1704_);
lean_inc(v_toSeqLeft_1703_);
lean_inc(v_toSeq_1702_);
lean_inc(v_toFunctor_1701_);
lean_dec(v_toApplicative_1697_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1726_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; lean_object* v___f_1711_; lean_object* v___x_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___f_1715_; lean_object* v___x_1717_; 
v___f_1708_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_1709_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_1701_);
v___f_1710_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1710_, 0, v_toFunctor_1701_);
v___f_1711_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1711_, 0, v_toFunctor_1701_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___f_1710_);
lean_ctor_set(v___x_1712_, 1, v___f_1711_);
v___f_1713_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1713_, 0, v_toSeqRight_1704_);
v___f_1714_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1714_, 0, v_toSeqLeft_1703_);
v___f_1715_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1715_, 0, v_toSeq_1702_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 4, v___f_1713_);
lean_ctor_set(v___x_1706_, 3, v___f_1714_);
lean_ctor_set(v___x_1706_, 2, v___f_1715_);
lean_ctor_set(v___x_1706_, 1, v___f_1708_);
lean_ctor_set(v___x_1706_, 0, v___x_1712_);
v___x_1717_ = v___x_1706_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___f_1708_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v___f_1715_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v___f_1714_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___f_1713_);
v___x_1717_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___f_1709_);
lean_ctor_set(v___x_1699_, 0, v___x_1717_);
v___x_1719_ = v___x_1699_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___f_1709_);
v___x_1719_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_2921__overap_1722_; lean_object* v___x_1723_; 
v___x_1720_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1721_ = l_instInhabitedOfMonad___redArg(v___x_1719_, v___x_1720_);
v___x_2921__overap_1722_ = lean_panic_fn_borrowed(v___x_1721_, v_msg_1674_);
lean_dec(v___x_1721_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
v___x_1723_ = lean_apply_5(v___x_2921__overap_1722_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, lean_box(0));
return v___x_1723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1736_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_1741_ = lean_unsigned_to_nat(53u);
v___x_1742_ = lean_unsigned_to_nat(62u);
v___x_1743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_1744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_1745_ = l_mkPanicMessageWithDecl(v___x_1744_, v___x_1743_, v___x_1742_, v___x_1741_, v___x_1740_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_1746_, size_t v_i_1747_, lean_object* v_bs_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_usize_dec_lt(v_i_1747_, v_sz_1746_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_bs_1748_);
return v___x_1755_;
}
else
{
lean_object* v_v_1756_; lean_object* v___x_1757_; 
v_v_1756_ = lean_array_uget_borrowed(v_bs_1748_, v_i_1747_);
lean_inc(v_v_1756_);
v___x_1757_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_1756_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v_bs_x27_1760_; lean_object* v_a_1762_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = lean_unsigned_to_nat(0u);
v_bs_x27_1760_ = lean_array_uset(v_bs_1748_, v_i_1747_, v___x_1759_);
if (lean_obj_tag(v_a_1758_) == 6)
{
lean_object* v_val_1767_; lean_object* v_numFields_1768_; uint8_t v___x_1769_; lean_object* v___x_1770_; 
v_val_1767_ = lean_ctor_get(v_a_1758_, 0);
lean_inc_ref(v_val_1767_);
lean_dec_ref_known(v_a_1758_, 1);
v_numFields_1768_ = lean_ctor_get(v_val_1767_, 4);
lean_inc(v_numFields_1768_);
lean_dec_ref(v_val_1767_);
v___x_1769_ = 0;
v___x_1770_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1770_, 0, v_numFields_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1759_);
lean_ctor_set_uint8(v___x_1770_, sizeof(void*)*2, v___x_1769_);
v_a_1762_ = v___x_1770_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec(v_a_1758_);
v___x_1771_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
v___x_1772_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_1771_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v_a_1762_ = v_a_1773_;
goto v___jp_1761_;
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec_ref(v_bs_x27_1760_);
v_a_1774_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1772_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1772_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
v___jp_1761_:
{
size_t v___x_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = ((size_t)1ULL);
v___x_1764_ = lean_usize_add(v_i_1747_, v___x_1763_);
v___x_1765_ = lean_array_uset(v_bs_x27_1760_, v_i_1747_, v_a_1762_);
v_i_1747_ = v___x_1764_;
v_bs_1748_ = v___x_1765_;
goto _start;
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v_bs_1748_);
v_a_1782_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1757_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1757_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_1790_, lean_object* v_i_1791_, lean_object* v_bs_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
size_t v_sz_boxed_1798_; size_t v_i_boxed_1799_; lean_object* v_res_1800_; 
v_sz_boxed_1798_ = lean_unbox_usize(v_sz_1790_);
lean_dec(v_sz_1790_);
v_i_boxed_1799_ = lean_unbox_usize(v_i_1791_);
lean_dec(v_i_1791_);
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_1798_, v_i_boxed_1799_, v_bs_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
return v_res_1800_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1801_; lean_object* v_dummy_1802_; 
v___x_1801_ = lean_box(0);
v_dummy_1802_ = l_Lean_Expr_sort___override(v___x_1801_);
return v_dummy_1802_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = lean_box(0);
v___x_1804_ = lean_unsigned_to_nat(16u);
v___x_1805_ = lean_mk_array(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v___x_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_1811_, uint8_t v_alsoCasesOn_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Lean_Expr_isApp(v_e_1811_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v_e_1811_);
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; 
v___x_1824_ = l_Lean_Expr_getAppFn(v_e_1811_);
if (lean_obj_tag(v___x_1824_) == 4)
{
lean_object* v_declName_1825_; lean_object* v_us_1826_; lean_object* v___x_1827_; lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1982_; 
v_declName_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc_n(v_declName_1825_, 2);
v_us_1826_ = lean_ctor_get(v___x_1824_, 1);
lean_inc(v_us_1826_);
lean_dec_ref_known(v___x_1824_, 2);
v___x_1827_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1825_, v___y_1816_);
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1982_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1982_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
if (lean_obj_tag(v_a_1828_) == 1)
{
lean_object* v_val_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1874_; 
v_val_1832_ = lean_ctor_get(v_a_1828_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v_a_1828_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1834_ = v_a_1828_;
v_isShared_1835_ = v_isSharedCheck_1874_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_val_1832_);
lean_dec(v_a_1828_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1874_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_dummy_1836_; lean_object* v_nargs_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_args_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_dummy_1836_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v_nargs_1837_ = l_Lean_Expr_getAppNumArgs(v_e_1811_);
lean_inc(v_nargs_1837_);
v___x_1838_ = lean_mk_array(v_nargs_1837_, v_dummy_1836_);
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_nat_sub(v_nargs_1837_, v___x_1839_);
lean_dec(v_nargs_1837_);
v_args_1841_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1811_, v___x_1838_, v___x_1840_);
v___x_1842_ = lean_array_get_size(v_args_1841_);
v___x_1843_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1832_);
v___x_1844_ = lean_nat_dec_lt(v___x_1842_, v___x_1843_);
lean_dec(v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v_numParams_1845_; lean_object* v_numDiscrs_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v_numParams_1845_ = lean_ctor_get(v_val_1832_, 0);
v_numDiscrs_1846_ = lean_ctor_get(v_val_1832_, 1);
v___x_1847_ = lean_array_mk(v_us_1826_);
v___x_1848_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1845_);
v___x_1849_ = l_Array_extract___redArg(v_args_1841_, v___x_1848_, v_numParams_1845_);
v___x_1850_ = l_Lean_instInhabitedExpr;
v___x_1851_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1832_);
v___x_1852_ = lean_array_get(v___x_1850_, v_args_1841_, v___x_1851_);
lean_dec(v___x_1851_);
v___x_1853_ = lean_nat_add(v_numParams_1845_, v___x_1839_);
v___x_1854_ = lean_nat_add(v___x_1853_, v_numDiscrs_1846_);
lean_inc(v___x_1854_);
lean_inc_ref_n(v_args_1841_, 2);
v___x_1855_ = l_Array_toSubarray___redArg(v_args_1841_, v___x_1853_, v___x_1854_);
v___x_1856_ = l_Subarray_copy___redArg(v___x_1855_);
v___x_1857_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1832_);
v___x_1858_ = lean_nat_add(v___x_1854_, v___x_1857_);
lean_dec(v___x_1857_);
lean_inc(v___x_1858_);
v___x_1859_ = l_Array_toSubarray___redArg(v_args_1841_, v___x_1854_, v___x_1858_);
v___x_1860_ = l_Subarray_copy___redArg(v___x_1859_);
v___x_1861_ = l_Array_toSubarray___redArg(v_args_1841_, v___x_1858_, v___x_1842_);
v___x_1862_ = l_Subarray_copy___redArg(v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1863_, 0, v_val_1832_);
lean_ctor_set(v___x_1863_, 1, v_declName_1825_);
lean_ctor_set(v___x_1863_, 2, v___x_1847_);
lean_ctor_set(v___x_1863_, 3, v___x_1849_);
lean_ctor_set(v___x_1863_, 4, v___x_1852_);
lean_ctor_set(v___x_1863_, 5, v___x_1856_);
lean_ctor_set(v___x_1863_, 6, v___x_1860_);
lean_ctor_set(v___x_1863_, 7, v___x_1862_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1863_);
v___x_1865_ = v___x_1834_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1865_);
v___x_1867_ = v___x_1830_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec_ref(v_args_1841_);
lean_del_object(v___x_1834_);
lean_dec(v_val_1832_);
lean_dec(v_us_1826_);
lean_dec(v_declName_1825_);
v___x_1870_ = lean_box(0);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1870_);
v___x_1872_ = v___x_1830_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v___x_1875_; 
lean_del_object(v___x_1830_);
lean_dec(v_a_1828_);
v___x_1875_ = lean_st_ref_get(v___y_1816_);
if (v_alsoCasesOn_1812_ == 0)
{
lean_dec(v___x_1875_);
lean_dec(v_us_1826_);
lean_dec(v_declName_1825_);
lean_dec_ref(v_e_1811_);
goto v___jp_1818_;
}
else
{
lean_object* v_env_1876_; uint8_t v___x_1877_; 
v_env_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc_ref(v_env_1876_);
lean_dec(v___x_1875_);
lean_inc(v_declName_1825_);
v___x_1877_ = l_Lean_isCasesOnRecursor(v_env_1876_, v_declName_1825_);
if (v___x_1877_ == 0)
{
lean_dec(v_us_1826_);
lean_dec(v_declName_1825_);
lean_dec_ref(v_e_1811_);
goto v___jp_1818_;
}
else
{
lean_object* v_indName_1878_; lean_object* v___x_1879_; 
v_indName_1878_ = l_Lean_Name_getPrefix(v_declName_1825_);
v___x_1879_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_1878_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1973_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1973_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1973_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
if (lean_obj_tag(v_a_1880_) == 5)
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1968_; 
v_val_1884_ = lean_ctor_get(v_a_1880_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_a_1880_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1886_ = v_a_1880_;
v_isShared_1887_ = v_isSharedCheck_1968_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v_a_1880_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1968_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v_toConstantVal_1888_; lean_object* v_numParams_1889_; lean_object* v_numIndices_1890_; lean_object* v_ctors_1891_; lean_object* v_nargs_1892_; lean_object* v_dummy_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_args_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v_toConstantVal_1888_ = lean_ctor_get(v_val_1884_, 0);
lean_inc_ref(v_toConstantVal_1888_);
v_numParams_1889_ = lean_ctor_get(v_val_1884_, 1);
lean_inc(v_numParams_1889_);
v_numIndices_1890_ = lean_ctor_get(v_val_1884_, 2);
lean_inc(v_numIndices_1890_);
v_ctors_1891_ = lean_ctor_get(v_val_1884_, 4);
lean_inc(v_ctors_1891_);
v_nargs_1892_ = l_Lean_Expr_getAppNumArgs(v_e_1811_);
v_dummy_1893_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
lean_inc(v_nargs_1892_);
v___x_1894_ = lean_mk_array(v_nargs_1892_, v_dummy_1893_);
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = lean_nat_sub(v_nargs_1892_, v___x_1895_);
lean_dec(v_nargs_1892_);
v_args_1897_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1811_, v___x_1894_, v___x_1896_);
v___x_1898_ = lean_nat_add(v_numParams_1889_, v___x_1895_);
v___x_1899_ = lean_nat_add(v___x_1898_, v_numIndices_1890_);
v___x_1900_ = lean_nat_add(v___x_1899_, v___x_1895_);
lean_dec(v___x_1899_);
v___x_1901_ = l_Lean_InductiveVal_numCtors(v_val_1884_);
lean_dec_ref(v_val_1884_);
v___x_1902_ = lean_nat_add(v___x_1900_, v___x_1901_);
lean_dec(v___x_1901_);
v___x_1903_ = lean_array_get_size(v_args_1897_);
v___x_1904_ = lean_nat_dec_le(v___x_1902_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
lean_dec(v___x_1902_);
lean_dec(v___x_1900_);
lean_dec(v___x_1898_);
lean_dec_ref(v_args_1897_);
lean_dec(v_ctors_1891_);
lean_dec(v_numIndices_1890_);
lean_dec(v_numParams_1889_);
lean_dec_ref(v_toConstantVal_1888_);
lean_del_object(v___x_1886_);
lean_dec(v_us_1826_);
lean_dec(v_declName_1825_);
v___x_1905_ = lean_box(0);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1905_);
v___x_1907_ = v___x_1882_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
else
{
lean_object* v___x_1909_; lean_object* v_params_1910_; lean_object* v___x_1911_; lean_object* v_motive_1912_; lean_object* v_discrs_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_discrInfos_1916_; lean_object* v_alts_1917_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v_lower_1959_; lean_object* v_upper_1960_; uint8_t v___x_1967_; 
lean_del_object(v___x_1882_);
v___x_1909_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1889_);
lean_inc_ref_n(v_args_1897_, 3);
v_params_1910_ = l_Array_toSubarray___redArg(v_args_1897_, v___x_1909_, v_numParams_1889_);
v___x_1911_ = l_Lean_instInhabitedExpr;
v_motive_1912_ = lean_array_get(v___x_1911_, v_args_1897_, v_numParams_1889_);
lean_dec(v_numParams_1889_);
lean_inc(v___x_1900_);
v_discrs_1913_ = l_Array_toSubarray___redArg(v_args_1897_, v___x_1898_, v___x_1900_);
v___x_1914_ = lean_nat_add(v_numIndices_1890_, v___x_1895_);
lean_dec(v_numIndices_1890_);
v___x_1915_ = lean_box(0);
v_discrInfos_1916_ = lean_mk_array(v___x_1914_, v___x_1915_);
lean_inc(v___x_1902_);
v_alts_1917_ = l_Array_toSubarray___redArg(v_args_1897_, v___x_1900_, v___x_1902_);
v___x_1967_ = lean_nat_dec_le(v___x_1902_, v___x_1909_);
if (v___x_1967_ == 0)
{
v_lower_1959_ = v___x_1902_;
v_upper_1960_ = v___x_1903_;
goto v___jp_1958_;
}
else
{
lean_dec(v___x_1902_);
v_lower_1959_ = v___x_1909_;
v_upper_1960_ = v___x_1903_;
goto v___jp_1958_;
}
v___jp_1918_:
{
lean_object* v___x_1921_; size_t v_sz_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1921_ = lean_array_mk(v_ctors_1891_);
v_sz_1922_ = lean_array_size(v___x_1921_);
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_1922_, v___x_1923_, v___x_1921_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1949_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1949_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1949_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_start_1929_; lean_object* v_stop_1930_; lean_object* v_start_1931_; lean_object* v_stop_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v_start_1929_ = lean_ctor_get(v_params_1910_, 1);
lean_inc(v_start_1929_);
v_stop_1930_ = lean_ctor_get(v_params_1910_, 2);
lean_inc(v_stop_1930_);
v_start_1931_ = lean_ctor_get(v_discrs_1913_, 1);
lean_inc(v_start_1931_);
v_stop_1932_ = lean_ctor_get(v_discrs_1913_, 2);
lean_inc(v_stop_1932_);
v___x_1933_ = lean_nat_sub(v_stop_1930_, v_start_1929_);
lean_dec(v_start_1929_);
lean_dec(v_stop_1930_);
v___x_1934_ = lean_nat_sub(v_stop_1932_, v_start_1931_);
lean_dec(v_start_1931_);
lean_dec(v_stop_1932_);
v___x_1935_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
v___x_1936_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1933_);
lean_ctor_set(v___x_1936_, 1, v___x_1934_);
lean_ctor_set(v___x_1936_, 2, v_a_1925_);
lean_ctor_set(v___x_1936_, 3, v___y_1920_);
lean_ctor_set(v___x_1936_, 4, v_discrInfos_1916_);
lean_ctor_set(v___x_1936_, 5, v___x_1935_);
v___x_1937_ = lean_array_mk(v_us_1826_);
v___x_1938_ = l_Subarray_copy___redArg(v_params_1910_);
v___x_1939_ = l_Subarray_copy___redArg(v_discrs_1913_);
v___x_1940_ = l_Subarray_copy___redArg(v_alts_1917_);
v___x_1941_ = l_Subarray_copy___redArg(v___y_1919_);
v___x_1942_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1936_);
lean_ctor_set(v___x_1942_, 1, v_declName_1825_);
lean_ctor_set(v___x_1942_, 2, v___x_1937_);
lean_ctor_set(v___x_1942_, 3, v___x_1938_);
lean_ctor_set(v___x_1942_, 4, v_motive_1912_);
lean_ctor_set(v___x_1942_, 5, v___x_1939_);
lean_ctor_set(v___x_1942_, 6, v___x_1940_);
lean_ctor_set(v___x_1942_, 7, v___x_1941_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 1);
lean_ctor_set(v___x_1886_, 0, v___x_1942_);
v___x_1944_ = v___x_1886_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1944_);
v___x_1946_ = v___x_1927_;
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
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec_ref(v_alts_1917_);
lean_dec_ref(v_discrInfos_1916_);
lean_dec_ref(v_discrs_1913_);
lean_dec(v_motive_1912_);
lean_dec_ref(v_params_1910_);
lean_del_object(v___x_1886_);
lean_dec(v_us_1826_);
lean_dec(v_declName_1825_);
v_a_1950_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1924_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1924_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
v___jp_1958_:
{
lean_object* v_levelParams_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_levelParams_1961_ = lean_ctor_get(v_toConstantVal_1888_, 1);
lean_inc(v_levelParams_1961_);
lean_dec_ref(v_toConstantVal_1888_);
v___x_1962_ = l_Array_toSubarray___redArg(v_args_1897_, v_lower_1959_, v_upper_1960_);
v___x_1963_ = l_List_lengthTR___redArg(v_levelParams_1961_);
lean_dec(v_levelParams_1961_);
v___x_1964_ = l_List_lengthTR___redArg(v_us_1826_);
v___x_1965_ = lean_nat_dec_eq(v___x_1963_, v___x_1964_);
lean_dec(v___x_1964_);
lean_dec(v___x_1963_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
v___x_1966_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3));
v___y_1919_ = v___x_1962_;
v___y_1920_ = v___x_1966_;
goto v___jp_1918_;
}
else
{
v___y_1919_ = v___x_1962_;
v___y_1920_ = v___x_1915_;
goto v___jp_1918_;
}
}
}
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
lean_dec(v_a_1880_);
lean_dec(v_us_1826_);
lean_dec(v_declName_1825_);
lean_dec_ref(v_e_1811_);
v___x_1969_ = lean_box(0);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1969_);
v___x_1971_ = v___x_1882_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec(v_us_1826_);
lean_dec(v_declName_1825_);
lean_dec_ref(v_e_1811_);
v_a_1974_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1879_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1879_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
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
lean_dec_ref(v___x_1824_);
lean_dec_ref(v_e_1811_);
goto v___jp_1818_;
}
}
v___jp_1818_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_box(0);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_1983_, lean_object* v_alsoCasesOn_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1990_; lean_object* v_res_1991_; 
v_alsoCasesOn_boxed_1990_ = lean_unbox(v_alsoCasesOn_1984_);
v_res_1991_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1983_, v_alsoCasesOn_boxed_1990_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_1999_ = l_Lean_Expr_isAppOf(v_e_1992_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2001_ = l_Lean_Expr_isAppOf(v_e_1992_, v___x_2000_);
if (v___x_2001_ == 0)
{
uint8_t v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = 1;
v___x_2003_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1992_, v___x_2002_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2024_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2024_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2024_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
if (lean_obj_tag(v_a_2004_) == 1)
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2019_; 
v_val_2008_ = lean_ctor_get(v_a_2004_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_a_2004_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2010_ = v_a_2004_;
v_isShared_2011_ = v_isSharedCheck_2019_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v_a_2004_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2019_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2012_, 0, v_val_2008_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2014_);
v___x_2016_ = v___x_2006_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
lean_dec(v_a_2004_);
v___x_2020_ = lean_box(0);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2020_);
v___x_2022_ = v___x_2006_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_a_2025_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2003_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2003_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_e_1992_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_e_1992_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2046_, v___y_2050_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2060_, lean_object* v_constName_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2068_, lean_object* v_constName_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2068_, v_constName_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2076_, lean_object* v_ref_2077_, lean_object* v_constName_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2077_, v_constName_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2085_, lean_object* v_ref_2086_, lean_object* v_constName_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2085_, v_ref_2086_, v_constName_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v_ref_2086_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2094_, lean_object* v_ref_2095_, lean_object* v_msg_2096_, lean_object* v_declHint_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2095_, v_msg_2096_, v_declHint_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2104_, lean_object* v_ref_2105_, lean_object* v_msg_2106_, lean_object* v_declHint_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2104_, v_ref_2105_, v_msg_2106_, v_declHint_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v_ref_2105_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2114_, lean_object* v_declHint_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2114_, v_declHint_2115_, v___y_2119_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2122_, lean_object* v_declHint_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2122_, v_declHint_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2130_, lean_object* v_ref_2131_, lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2131_, v_msg_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_ref_2140_, lean_object* v_msg_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2139_, v_ref_2140_, v_msg_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v_ref_2140_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2148_, lean_object* v_msg_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2156_, lean_object* v_msg_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2156_, v_msg_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
return v_res_2163_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2166_ = l_Lean_stringToMessageData(v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2167_, lean_object* v_e_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___y_2175_; uint8_t v___y_2194_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2205_ = l_Lean_Expr_isAppOf(v_e_2168_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2207_ = l_Lean_Expr_isAppOf(v_e_2168_, v___x_2206_);
v___y_2194_ = v___x_2207_;
goto v___jp_2193_;
}
else
{
v___y_2194_ = v___x_2205_;
goto v___jp_2193_;
}
v___jp_2174_:
{
lean_object* v___x_2176_; 
lean_inc_ref(v___y_2175_);
v___x_2176_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2175_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
if (lean_obj_tag(v_a_2177_) == 1)
{
lean_object* v_val_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec_ref(v___y_2175_);
v_val_2178_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_val_2178_);
lean_dec_ref_known(v_a_2177_, 1);
v___x_2179_ = l_Lean_mkFVar(v_val_2178_);
v___x_2180_ = l_Lean_Meta_rwIfWith(v___x_2179_, v_e_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec(v_a_2177_);
lean_dec_ref(v_e_2168_);
v___x_2181_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2182_ = l_Lean_MessageData_ofExpr(v___y_2175_);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2183_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2184_;
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v___y_2175_);
lean_dec_ref(v_e_2168_);
v_a_2185_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2176_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2176_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
v___jp_2193_:
{
if (v___y_2194_ == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_Meta_rwMatcher(v_idx_2167_, v_e_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_c_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = l_Lean_Expr_getAppNumArgs(v_e_2168_);
v___x_2198_ = lean_nat_sub(v___x_2197_, v___x_2196_);
lean_dec(v___x_2197_);
v___x_2199_ = lean_nat_sub(v___x_2198_, v___x_2196_);
lean_dec(v___x_2198_);
v_c_2200_ = l_Lean_Expr_getRevArg_x21(v_e_2168_, v___x_2199_);
v___x_2201_ = lean_unsigned_to_nat(0u);
v___x_2202_ = lean_nat_dec_eq(v_idx_2167_, v___x_2201_);
lean_dec(v_idx_2167_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_mkNot(v_c_2200_);
v___y_2175_ = v___x_2203_;
goto v___jp_2174_;
}
else
{
v___y_2175_ = v_c_2200_;
goto v___jp_2174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2208_, lean_object* v_e_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2208_, v_e_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
return v_res_2215_;
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
