// Lean compiler output
// Module: Lean.Elab.BuiltinDo.For
// Imports: public import Lean.Elab.BuiltinDo.Basic meta import Lean.Parser.Do import Init.Control.Do import Lean.Meta.ProdN
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
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkProdMkN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkPureApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_enterLoopBody___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_bindMutVarsFromTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Do_MutVar_getId(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkBindApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Std.toStream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toStream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(165, 78, 6, 120, 105, 250, 102, 183)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToStream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(131, 221, 81, 225, 58, 10, 156, 107)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(10, 224, 141, 229, 184, 244, 208, 180)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__s"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 33, 185, 180, 14, 135, 99, 223)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mut"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Std.Stream.next\?"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Stream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next\?"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(131, 33, 225, 197, 4, 77, 215, 237)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(223, 69, 181, 194, 149, 37, 29, 54)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "break"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s'"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(203, 110, 194, 112, 150, 40, 11, 92)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "The proof annotation here has not been implemented yet."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__7_value;
static const lean_array_object l_Lean_Elab_Do_expandDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__8 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__8_value;
static const lean_array_object l_Lean_Elab_Do_expandDoFor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__9 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__10 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__12 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__14 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expandDoFor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 157, 21, 52, 135, 185, 36, 254)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__3;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = " but the info said there is no early return"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__5;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Early returning "};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__7;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "yield"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ForInStep"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 23, 255, 201, 194, 179, 65, 111)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Break"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "runK"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "match_1"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 204, 143, 3, 84, 67, 92, 151)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 178, 64, 100, 79, 118, 122, 28)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 194, 234, 57, 172, 104, 157, 179)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mem"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 90, 126, 237, 128, 148, 153, 69)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ForIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "forIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 12, 142, 239, 44, 138, 10, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 234, 148, 175, 115, 149, 2, 231)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ForIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value),LEAN_SCALAR_PTR_LITERAL(10, 254, 232, 131, 195, 189, 138, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "ρ"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value),LEAN_SCALAR_PTR_LITERAL(148, 87, 172, 24, 54, 35, 28, 246)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value),LEAN_SCALAR_PTR_LITERAL(38, 26, 183, 93, 43, 136, 227, 87)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__16_value;
static const lean_array_object l_Lean_Elab_Do_elabDoFor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabDoFor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 135, 12, 29, 130, 81, 226, 183)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_macroScope_6_; lean_object* v_traceMsgs_7_; lean_object* v_expandedMacroDecls_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v_macroScope_6_ = lean_ctor_get(v___y_5_, 0);
v_traceMsgs_7_ = lean_ctor_get(v___y_5_, 1);
v_expandedMacroDecls_8_ = lean_ctor_get(v___y_5_, 2);
v_isSharedCheck_21_ = !lean_is_exclusive(v___y_5_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v___y_5_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_expandedMacroDecls_8_);
lean_inc(v_traceMsgs_7_);
lean_inc(v_macroScope_6_);
lean_dec(v___y_5_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v_quotContext_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v_quotContext_12_ = lean_ctor_get(v___y_4_, 1);
v___x_13_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1));
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_add(v_macroScope_6_, v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_traceMsgs_7_);
lean_ctor_set(v_reuseFailAlloc_20_, 2, v_expandedMacroDecls_8_);
v___x_17_ = v_reuseFailAlloc_20_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_inc(v_quotContext_12_);
v___x_18_ = l_Lean_addMacroScope(v_quotContext_12_, v___x_13_, v_macroScope_6_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___boxed(lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_22_, v___y_23_);
lean_dec_ref(v___y_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(lean_object* v_ref_25_, uint8_t v_canonical_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___x_29_; lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v___x_29_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_27_, v___y_28_);
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_29_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = l_Lean_mkIdentFrom(v_ref_25_, v_a_30_, v_canonical_26_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_a_31_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1___boxed(lean_object* v_ref_40_, lean_object* v_canonical_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
uint8_t v_canonical_boxed_44_; lean_object* v_res_45_; 
v_canonical_boxed_44_ = lean_unbox(v_canonical_41_);
v_res_45_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v_ref_40_, v_canonical_boxed_44_, v___y_42_, v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v_ref_40_);
return v_res_45_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3));
v___x_51_ = l_String_toRawSubstring_x27(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Array_mkArray0(lean_box(0));
return v___x_81_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32));
v___x_92_ = l_String_toRawSubstring_x27(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43));
v___x_111_ = l_String_toRawSubstring_x27(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53));
v___x_129_ = l_String_toRawSubstring_x27(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64));
v___x_149_ = l_String_toRawSubstring_x27(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69));
v___x_155_ = l_String_toRawSubstring_x27(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(lean_object* v___x_164_, lean_object* v___x_165_, lean_object* v___x_166_, uint8_t v___x_167_, lean_object* v___x_168_, lean_object* v___x_169_, lean_object* v___x_170_, lean_object* v___f_171_, lean_object* v_fst_172_, lean_object* v___x_173_, lean_object* v_snd_174_, lean_object* v_x_175_, lean_object* v_h_x3f_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___y_182_; 
v___x_179_ = l_Lean_Syntax_getArg(v___x_164_, v___x_165_);
v___x_180_ = l_Lean_Syntax_getArg(v___x_164_, v___x_166_);
if (lean_obj_tag(v_h_x3f_176_) == 1)
{
lean_object* v_val_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_val_400_ = lean_ctor_get(v_h_x3f_176_, 0);
v___x_401_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77));
v___x_402_ = l_Lean_Macro_throwErrorAt___redArg(v_val_400_, v___x_401_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 2);
v___y_182_ = v_a_403_;
goto v___jp_181_;
}
else
{
lean_object* v_a_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v___x_180_);
lean_dec(v___x_179_);
lean_dec(v_snd_174_);
lean_dec_ref(v___x_173_);
lean_dec(v_fst_172_);
lean_dec_ref(v___f_171_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
v_a_404_ = lean_ctor_get(v___x_402_, 0);
v_a_405_ = lean_ctor_get(v___x_402_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_402_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_inc(v_a_404_);
lean_dec(v___x_402_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_404_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
v___y_182_ = v___y_178_;
goto v___jp_181_;
}
v___jp_181_:
{
lean_object* v_quotContext_183_; lean_object* v_currMacroScope_184_; lean_object* v_ref_185_; lean_object* v_ref_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_macroScope_208_; lean_object* v_traceMsgs_209_; lean_object* v_expandedMacroDecls_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_399_; 
v_quotContext_183_ = lean_ctor_get(v___y_177_, 1);
v_currMacroScope_184_ = lean_ctor_get(v___y_177_, 2);
v_ref_185_ = lean_ctor_get(v___y_177_, 5);
v_ref_186_ = l_Lean_replaceRef(v___x_180_, v_ref_185_);
v___x_187_ = l_Lean_SourceInfo_fromRef(v_ref_186_, v___x_167_);
lean_dec(v_ref_186_);
v___x_188_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
lean_inc_ref_n(v___x_170_, 3);
lean_inc_ref_n(v___x_169_, 3);
lean_inc_ref_n(v___x_168_, 3);
v___x_189_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_188_);
v___x_190_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1));
v___x_191_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_190_);
v___x_192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2));
lean_inc_n(v___x_187_, 6);
v___x_193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_187_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
v___x_195_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_184_);
lean_inc(v_quotContext_183_);
v___x_196_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_195_, v_currMacroScope_184_);
v___x_197_ = lean_box(0);
v___x_198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11));
v___x_199_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_199_, 0, v___x_187_);
lean_ctor_set(v___x_199_, 1, v___x_194_);
lean_ctor_set(v___x_199_, 2, v___x_196_);
lean_ctor_set(v___x_199_, 3, v___x_198_);
lean_inc(v___x_191_);
v___x_200_ = l_Lean_Syntax_node2(v___x_187_, v___x_191_, v___x_193_, v___x_199_);
v___x_201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_202_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14));
v___x_203_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_202_);
v___x_204_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_187_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
lean_inc(v___x_203_);
v___x_206_ = l_Lean_Syntax_node1(v___x_187_, v___x_203_, v___x_205_);
lean_inc(v___x_180_);
lean_inc_n(v___x_206_, 2);
v___x_207_ = l_Lean_Syntax_node4(v___x_187_, v___x_201_, v___x_206_, v___x_206_, v___x_206_, v___x_180_);
v_macroScope_208_ = lean_ctor_get(v___y_182_, 0);
v_traceMsgs_209_ = lean_ctor_get(v___y_182_, 1);
v_expandedMacroDecls_210_ = lean_ctor_get(v___y_182_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v___y_182_);
if (v_isSharedCheck_399_ == 0)
{
v___x_212_ = v___y_182_;
v_isShared_213_ = v_isSharedCheck_399_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_expandedMacroDecls_210_);
lean_inc(v_traceMsgs_209_);
lean_inc(v_macroScope_208_);
lean_dec(v___y_182_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_399_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_nat_add(v_macroScope_208_, v___x_165_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_traceMsgs_209_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_expandedMacroDecls_210_);
v___x_216_ = v_reuseFailAlloc_398_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; 
lean_inc_ref(v___f_171_);
lean_inc_ref(v___y_177_);
lean_inc(v_ref_185_);
v___x_217_ = lean_apply_3(v___f_171_, v_ref_185_, v___y_177_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v_a_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_n(v_a_218_, 9);
v_a_219_ = lean_ctor_get(v___x_217_, 1);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_217_, 2);
lean_inc(v___x_189_);
v___x_220_ = l_Lean_Syntax_node2(v___x_187_, v___x_189_, v___x_200_, v___x_207_);
v___x_221_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
lean_inc(v_quotContext_183_);
v___x_222_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_221_, v_macroScope_208_);
v___x_223_ = l_Lean_mkIdentFrom(v___x_180_, v___x_222_, v___x_167_);
lean_dec(v___x_180_);
v___x_224_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18));
lean_inc_ref_n(v___x_170_, 6);
lean_inc_ref_n(v___x_169_, 6);
lean_inc_ref_n(v___x_168_, 6);
v___x_225_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_224_);
v___x_226_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19));
v___x_227_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_226_);
v___x_228_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20));
v___x_229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_229_, 0, v_a_218_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21));
v___x_231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_231_, 0, v_a_218_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_Lean_Syntax_node1(v_a_218_, v___x_201_, v___x_231_);
v___x_233_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22));
v___x_234_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_233_);
v___x_235_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_236_, 0, v_a_218_);
lean_ctor_set(v___x_236_, 1, v___x_201_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_inc_ref_n(v___x_236_, 3);
v___x_237_ = l_Lean_Syntax_node1(v_a_218_, v___x_234_, v___x_236_);
v___x_238_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24));
v___x_239_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_238_);
v___x_240_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25));
v___x_241_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_240_);
v___x_242_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26));
v___x_243_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_242_);
lean_inc(v___x_223_);
lean_inc(v___x_243_);
v___x_244_ = l_Lean_Syntax_node1(v_a_218_, v___x_243_, v___x_223_);
v___x_245_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27));
v___x_246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_246_, 0, v_a_218_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = l_Lean_Syntax_node5(v_a_218_, v___x_241_, v___x_244_, v___x_236_, v___x_236_, v___x_246_, v___x_220_);
lean_inc_ref(v___y_177_);
lean_inc(v_ref_185_);
v___x_248_ = lean_apply_3(v___f_171_, v_ref_185_, v___y_177_, v_a_219_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_379_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_a_250_ = lean_ctor_get(v___x_248_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_379_ == 0)
{
v___x_252_ = v___x_248_;
v_isShared_253_ = v_isSharedCheck_379_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_379_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
lean_inc_n(v_a_218_, 2);
v___x_254_ = l_Lean_Syntax_node1(v_a_218_, v___x_239_, v___x_247_);
v___x_255_ = l_Lean_Syntax_node4(v_a_218_, v___x_227_, v___x_229_, v___x_232_, v___x_237_, v___x_254_);
lean_inc_n(v___x_225_, 4);
v___x_256_ = l_Lean_Syntax_node2(v_a_218_, v___x_225_, v___x_255_, v___x_236_);
v___x_257_ = lean_array_push(v_fst_172_, v___x_256_);
v___x_258_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28));
lean_inc_ref_n(v___x_170_, 11);
lean_inc_ref_n(v___x_169_, 11);
lean_inc_ref_n(v___x_168_, 13);
v___x_259_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_258_);
v___x_260_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
v___x_261_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_260_);
v___x_262_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v_a_249_, 54);
v___x_263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_263_, 0, v_a_249_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_264_, 0, v_a_249_);
lean_ctor_set(v___x_264_, 1, v___x_201_);
lean_ctor_set(v___x_264_, 2, v___x_235_);
v___x_265_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31));
v___x_266_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_265_);
v___x_267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_267_, 0, v_a_249_);
lean_ctor_set(v___x_267_, 1, v___x_192_);
v___x_268_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33);
v___x_269_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36));
lean_inc_n(v_currMacroScope_184_, 5);
lean_inc_n(v_quotContext_183_, 5);
v___x_270_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_269_, v_currMacroScope_184_);
v___x_271_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_272_, 0, v_a_249_);
lean_ctor_set(v___x_272_, 1, v___x_268_);
lean_ctor_set(v___x_272_, 2, v___x_270_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
v___x_273_ = l_Lean_Syntax_node2(v_a_249_, v___x_191_, v___x_267_, v___x_272_);
v___x_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_274_, 0, v_a_249_);
lean_ctor_set(v___x_274_, 1, v___x_204_);
v___x_275_ = l_Lean_Syntax_node1(v_a_249_, v___x_203_, v___x_274_);
lean_inc(v___x_223_);
lean_inc_n(v___x_275_, 2);
v___x_276_ = l_Lean_Syntax_node4(v_a_249_, v___x_201_, v___x_275_, v___x_275_, v___x_275_, v___x_223_);
lean_inc(v___x_189_);
v___x_277_ = l_Lean_Syntax_node2(v_a_249_, v___x_189_, v___x_273_, v___x_276_);
lean_inc_ref_n(v___x_264_, 9);
v___x_278_ = l_Lean_Syntax_node2(v_a_249_, v___x_266_, v___x_264_, v___x_277_);
v___x_279_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_278_);
v___x_280_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_281_, 0, v_a_249_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40));
v___x_283_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_282_);
v___x_284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_285_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_284_);
v___x_286_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_287_, 0, v_a_249_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44);
v___x_289_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45));
v___x_290_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_289_, v_currMacroScope_184_);
v___x_291_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_292_, 0, v_a_249_);
lean_ctor_set(v___x_292_, 1, v___x_288_);
lean_ctor_set(v___x_292_, 2, v___x_290_);
lean_ctor_set(v___x_292_, 3, v___x_291_);
v___x_293_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_292_);
v___x_294_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_293_);
v___x_295_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_296_, 0, v_a_249_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51));
v___x_298_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_297_);
v___x_299_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52));
v___x_300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_300_, 0, v_a_249_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_Syntax_node1(v_a_249_, v___x_298_, v___x_300_);
v___x_302_ = l_Lean_Syntax_node2(v_a_249_, v___x_225_, v___x_301_, v___x_264_);
v___x_303_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_302_);
lean_inc_n(v___x_259_, 2);
v___x_304_ = l_Lean_Syntax_node1(v_a_249_, v___x_259_, v___x_303_);
lean_inc_ref(v___x_296_);
lean_inc_ref(v___x_287_);
lean_inc(v___x_285_);
v___x_305_ = l_Lean_Syntax_node4(v_a_249_, v___x_285_, v___x_287_, v___x_294_, v___x_296_, v___x_304_);
v___x_306_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54);
v___x_307_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55));
v___x_308_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_307_, v_currMacroScope_184_);
v___x_309_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58));
v___x_310_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_310_, 0, v_a_249_);
lean_ctor_set(v___x_310_, 1, v___x_306_);
lean_ctor_set(v___x_310_, 2, v___x_308_);
lean_ctor_set(v___x_310_, 3, v___x_309_);
v___x_311_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59));
v___x_312_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_311_);
v___x_313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60));
v___x_314_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_313_);
v___x_315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61));
v___x_316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_249_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
v___x_318_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65);
v___x_319_ = lean_box(0);
v___x_320_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_319_, v_currMacroScope_184_);
v___x_321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66));
v___x_322_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67));
v___x_323_ = l_Lean_Name_mkStr3(v___x_168_, v___x_321_, v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68));
v___x_326_ = l_Lean_Name_mkStr2(v___x_168_, v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = l_Lean_Name_mkStr3(v___x_168_, v___x_169_, v___x_170_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_197_);
v___x_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_327_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_324_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_333_, 0, v_a_249_);
lean_ctor_set(v___x_333_, 1, v___x_318_);
lean_ctor_set(v___x_333_, 2, v___x_320_);
lean_ctor_set(v___x_333_, 3, v___x_332_);
v___x_334_ = l_Lean_Syntax_node1(v_a_249_, v___x_317_, v___x_333_);
v___x_335_ = l_Lean_Syntax_node2(v_a_249_, v___x_314_, v___x_316_, v___x_334_);
v___x_336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_336_, 0, v_a_249_);
lean_ctor_set(v___x_336_, 1, v___x_173_);
v___x_337_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70);
v___x_338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71));
v___x_339_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_338_, v_currMacroScope_184_);
v___x_340_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_340_, 0, v_a_249_);
lean_ctor_set(v___x_340_, 1, v___x_337_);
lean_ctor_set(v___x_340_, 2, v___x_339_);
lean_ctor_set(v___x_340_, 3, v___x_197_);
lean_inc_ref(v___x_340_);
v___x_341_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_340_);
v___x_342_ = l_Lean_Syntax_node3(v_a_249_, v___x_201_, v___x_179_, v___x_336_, v___x_341_);
v___x_343_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v_a_249_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_Syntax_node3(v_a_249_, v___x_312_, v___x_335_, v___x_342_, v___x_344_);
v___x_346_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_345_);
v___x_347_ = l_Lean_Syntax_node2(v_a_249_, v___x_189_, v___x_310_, v___x_346_);
v___x_348_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_347_);
v___x_349_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_348_);
v___x_350_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73));
v___x_351_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_350_);
v___x_352_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74));
v___x_353_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_352_);
v___x_354_ = l_Lean_Syntax_node1(v_a_249_, v___x_243_, v___x_223_);
v___x_355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_355_, 0, v_a_249_);
lean_ctor_set(v___x_355_, 1, v___x_245_);
v___x_356_ = l_Lean_Syntax_node5(v_a_249_, v___x_353_, v___x_354_, v___x_264_, v___x_264_, v___x_355_, v___x_340_);
v___x_357_ = l_Lean_Syntax_node1(v_a_249_, v___x_351_, v___x_356_);
v___x_358_ = l_Lean_Syntax_node2(v_a_249_, v___x_225_, v___x_357_, v___x_264_);
v___x_359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_360_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_359_);
v___x_361_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v_a_249_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_Syntax_node2(v_a_249_, v___x_360_, v___x_362_, v_snd_174_);
v___x_364_ = l_Lean_Syntax_node2(v_a_249_, v___x_225_, v___x_363_, v___x_264_);
v___x_365_ = l_Lean_Syntax_node2(v_a_249_, v___x_201_, v___x_358_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node1(v_a_249_, v___x_259_, v___x_365_);
v___x_367_ = l_Lean_Syntax_node4(v_a_249_, v___x_285_, v___x_287_, v___x_349_, v___x_296_, v___x_366_);
v___x_368_ = l_Lean_Syntax_node2(v_a_249_, v___x_201_, v___x_305_, v___x_367_);
v___x_369_ = l_Lean_Syntax_node1(v_a_249_, v___x_283_, v___x_368_);
v___x_370_ = l_Lean_Syntax_node7(v_a_249_, v___x_261_, v___x_263_, v___x_264_, v___x_264_, v___x_264_, v___x_279_, v___x_281_, v___x_369_);
v___x_371_ = l_Lean_Syntax_node2(v_a_249_, v___x_225_, v___x_370_, v___x_264_);
v___x_372_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_371_);
v___x_373_ = l_Lean_Syntax_node1(v_a_249_, v___x_259_, v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_257_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_375_);
v___x_377_ = v___x_252_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_a_250_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v___x_247_);
lean_dec(v___x_243_);
lean_dec(v___x_239_);
lean_dec(v___x_237_);
lean_dec_ref_known(v___x_236_, 3);
lean_dec(v___x_232_);
lean_dec_ref_known(v___x_229_, 2);
lean_dec(v___x_227_);
lean_dec(v___x_225_);
lean_dec(v___x_223_);
lean_dec(v_a_218_);
lean_dec(v___x_203_);
lean_dec(v___x_191_);
lean_dec(v___x_189_);
lean_dec(v___x_179_);
lean_dec(v_snd_174_);
lean_dec_ref(v___x_173_);
lean_dec(v_fst_172_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
v_a_380_ = lean_ctor_get(v___x_248_, 0);
v_a_381_ = lean_ctor_get(v___x_248_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_248_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_inc(v_a_380_);
lean_dec(v___x_248_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_380_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_macroScope_208_);
lean_dec(v___x_207_);
lean_dec(v___x_203_);
lean_dec(v___x_200_);
lean_dec(v___x_191_);
lean_dec(v___x_189_);
lean_dec(v___x_187_);
lean_dec(v___x_180_);
lean_dec(v___x_179_);
lean_dec(v_snd_174_);
lean_dec_ref(v___x_173_);
lean_dec(v_fst_172_);
lean_dec_ref(v___f_171_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
v_a_389_ = lean_ctor_get(v___x_217_, 0);
v_a_390_ = lean_ctor_get(v___x_217_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_217_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_inc(v_a_389_);
lean_dec(v___x_217_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_389_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___boxed(lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v___x_416_, lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___f_420_, lean_object* v_fst_421_, lean_object* v___x_422_, lean_object* v_snd_423_, lean_object* v_x_424_, lean_object* v_h_x3f_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_146124__boxed_428_; lean_object* v_res_429_; 
v___x_146124__boxed_428_ = lean_unbox(v___x_416_);
v_res_429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_413_, v___x_414_, v___x_415_, v___x_146124__boxed_428_, v___x_417_, v___x_418_, v___x_419_, v___f_420_, v_fst_421_, v___x_422_, v_snd_423_, v_x_424_, v_h_x3f_425_, v___y_426_, v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v_h_x3f_425_);
lean_dec(v___x_415_);
lean_dec(v___x_414_);
lean_dec(v___x_413_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(uint8_t v___x_430_, lean_object* v_____do__lift_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = l_Lean_SourceInfo_fromRef(v_____do__lift_431_, v___x_430_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(lean_object* v___x_436_, lean_object* v_____do__lift_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
uint8_t v___x_146730__boxed_440_; lean_object* v_res_441_; 
v___x_146730__boxed_440_ = lean_unbox(v___x_436_);
v_res_441_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(v___x_146730__boxed_440_, v_____do__lift_437_, v___y_438_, v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_____do__lift_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(uint8_t v___x_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_array_457_; lean_object* v_start_458_; lean_object* v_stop_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_553_; 
v_array_457_ = lean_ctor_get(v_a_453_, 0);
v_start_458_ = lean_ctor_get(v_a_453_, 1);
v_stop_459_ = lean_ctor_get(v_a_453_, 2);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_453_);
if (v_isSharedCheck_553_ == 0)
{
v___x_461_ = v_a_453_;
v_isShared_462_ = v_isSharedCheck_553_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_stop_459_);
lean_inc(v_start_458_);
lean_inc(v_array_457_);
lean_dec(v_a_453_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_553_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; 
v___x_463_ = lean_nat_dec_lt(v_start_458_, v_stop_459_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_del_object(v___x_461_);
lean_dec(v_stop_459_);
lean_dec(v_start_458_);
lean_dec_ref(v_array_457_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_b_454_);
lean_ctor_set(v___x_464_, 1, v___y_456_);
return v___x_464_;
}
else
{
lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_552_; 
v_fst_465_ = lean_ctor_get(v_b_454_, 0);
v_snd_466_ = lean_ctor_get(v_b_454_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_b_454_);
if (v_isSharedCheck_552_ == 0)
{
v___x_468_ = v_b_454_;
v_isShared_469_ = v_isSharedCheck_552_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_inc(v_fst_465_);
lean_dec(v_b_454_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_552_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_472_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_473_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_474_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v___x_475_ = lean_nat_add(v_start_458_, v___x_470_);
lean_inc_ref(v_array_457_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_475_);
v___x_477_ = v___x_461_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_array_457_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_stop_459_);
v___x_477_ = v_reuseFailAlloc_551_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___y_479_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_array_fget(v_array_457_, v_start_458_);
lean_dec(v_start_458_);
lean_dec_ref(v_array_457_);
lean_inc(v___x_503_);
v___x_504_ = l_Lean_Syntax_isOfKind(v___x_503_, v___x_474_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v___x_503_);
v___x_505_ = l_Lean_Macro_throwUnsupported___redArg(v___y_456_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; 
v_a_506_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 2);
if (v_isShared_469_ == 0)
{
v___x_508_ = v___x_468_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_fst_465_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_snd_466_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
v_a_453_ = v___x_477_;
v_b_454_ = v___x_508_;
v___y_456_ = v_a_506_;
goto _start;
}
}
else
{
lean_object* v_a_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v___x_477_);
lean_del_object(v___x_468_);
lean_dec(v_snd_466_);
lean_dec(v_fst_465_);
v_a_511_ = lean_ctor_get(v___x_505_, 0);
v_a_512_ = lean_ctor_get(v___x_505_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_505_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_inc(v_a_511_);
lean_dec(v___x_505_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_520_ = lean_box(v___x_452_);
v___f_521_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_521_, 0, v___x_520_);
v___x_522_ = lean_unsigned_to_nat(3u);
v___x_523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_Lean_Syntax_getArg(v___x_503_, v___x_524_);
v___x_526_ = l_Lean_Syntax_isNone(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_525_);
v___x_528_ = l_Lean_Syntax_matchesNull(v___x_525_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_dec(v___x_525_);
lean_dec_ref(v___f_521_);
lean_dec(v___x_503_);
v___x_529_ = l_Lean_Macro_throwUnsupported___redArg(v___y_456_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v___x_529_, 1);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 2);
if (v_isShared_469_ == 0)
{
v___x_532_ = v___x_468_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_465_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_snd_466_);
v___x_532_ = v_reuseFailAlloc_534_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v_a_453_ = v___x_477_;
v_b_454_ = v___x_532_;
v___y_456_ = v_a_530_;
goto _start;
}
}
else
{
lean_object* v_a_535_; lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v___x_477_);
lean_del_object(v___x_468_);
lean_dec(v_snd_466_);
lean_dec(v_fst_465_);
v_a_535_ = lean_ctor_get(v___x_529_, 0);
v_a_536_ = lean_ctor_get(v___x_529_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_529_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_inc(v_a_535_);
lean_dec(v___x_529_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_535_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_del_object(v___x_468_);
v___x_544_ = l_Lean_Syntax_getArg(v___x_525_, v___x_524_);
lean_dec(v___x_525_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
v___x_547_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_503_, v___x_470_, v___x_522_, v___x_452_, v___x_471_, v___x_472_, v___x_473_, v___f_521_, v_fst_465_, v___x_523_, v_snd_466_, v___x_545_, v___x_546_, v___y_455_, v___y_456_);
lean_dec_ref_known(v___x_546_, 1);
lean_dec(v___x_503_);
v___y_479_ = v___x_547_;
goto v___jp_478_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v___x_525_);
lean_del_object(v___x_468_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_box(0);
v___x_550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_503_, v___x_470_, v___x_522_, v___x_452_, v___x_471_, v___x_472_, v___x_473_, v___f_521_, v_fst_465_, v___x_523_, v_snd_466_, v___x_548_, v___x_549_, v___y_455_, v___y_456_);
lean_dec(v___x_503_);
v___y_479_ = v___x_550_;
goto v___jp_478_;
}
}
v___jp_478_:
{
if (lean_obj_tag(v___y_479_) == 0)
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___y_479_, 0);
lean_inc(v_a_480_);
if (lean_obj_tag(v_a_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v___x_477_);
v_a_481_ = lean_ctor_get(v___y_479_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___y_479_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v___y_479_, 0);
lean_dec(v_unused_490_);
v___x_483_ = v___y_479_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___y_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_a_485_; lean_object* v___x_487_; 
v_a_485_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v_a_480_, 1);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v_a_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_a_481_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v_a_492_; 
v_a_491_ = lean_ctor_get(v___y_479_, 1);
lean_inc(v_a_491_);
lean_dec_ref_known(v___y_479_, 2);
v_a_492_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v_a_480_, 1);
v_a_453_ = v___x_477_;
v_b_454_ = v_a_492_;
v___y_456_ = v_a_491_;
goto _start;
}
}
else
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref(v___x_477_);
v_a_494_ = lean_ctor_get(v___y_479_, 0);
v_a_495_ = lean_ctor_get(v___y_479_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___y_479_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___y_479_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_inc(v_a_494_);
lean_dec(v___y_479_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___boxed(lean_object* v___x_554_, lean_object* v_a_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_146766__boxed_559_; lean_object* v_res_560_; 
v___x_146766__boxed_559_ = lean_unbox(v___x_554_);
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_146766__boxed_559_, v_a_555_, v_b_556_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object* v_stx_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_617_);
v___x_621_ = l_Lean_Syntax_isOfKind(v_stx_617_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec(v_stx_617_);
v___x_622_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v_tk_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v_tk_624_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_623_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_625_);
lean_inc(v___x_626_);
v___x_627_ = l_Lean_Syntax_matchesNull(v___x_626_, v___x_625_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v_decls_660_; lean_object* v_decls_661_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v_x_666_; lean_object* v_body_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_628_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v_decls_660_ = l_Lean_Syntax_getArgs(v___x_626_);
lean_dec(v___x_626_);
v_decls_661_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_660_);
lean_dec_ref(v_decls_660_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_array_get(v___x_706_, v_decls_661_, v___x_623_);
lean_inc(v___x_707_);
v___x_708_ = l_Lean_Syntax_isOfKind(v___x_707_, v___x_628_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
lean_dec(v___x_707_);
lean_dec_ref(v_decls_661_);
lean_dec(v_tk_624_);
lean_dec(v_stx_617_);
v___x_709_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v_body_711_; lean_object* v_h_x3f_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_710_ = lean_unsigned_to_nat(3u);
v_body_711_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_710_);
lean_dec(v_stx_617_);
v___x_776_ = l_Lean_Syntax_getArg(v___x_707_, v___x_623_);
v___x_777_ = l_Lean_Syntax_isNone(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_776_);
v___x_779_ = l_Lean_Syntax_matchesNull(v___x_776_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
lean_dec(v___x_776_);
lean_dec(v_body_711_);
lean_dec(v___x_707_);
lean_dec_ref(v_decls_661_);
lean_dec(v_tk_624_);
v___x_780_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_780_;
}
else
{
lean_object* v_h_x3f_781_; lean_object* v___x_782_; 
v_h_x3f_781_ = l_Lean_Syntax_getArg(v___x_776_, v___x_623_);
lean_dec(v___x_776_);
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v_h_x3f_781_);
v_h_x3f_713_ = v___x_782_;
v___y_714_ = v_a_618_;
v___y_715_ = v_a_619_;
goto v___jp_712_;
}
}
else
{
lean_object* v___x_783_; 
lean_dec(v___x_776_);
v___x_783_ = lean_box(0);
v_h_x3f_713_ = v___x_783_;
v___y_714_ = v_a_618_;
v___y_715_ = v_a_619_;
goto v___jp_712_;
}
v___jp_712_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_doElems_718_; uint8_t v___x_719_; 
v___x_716_ = l_Lean_Syntax_getArg(v___x_707_, v___x_625_);
v___x_717_ = l_Lean_Syntax_getArg(v___x_707_, v___x_710_);
lean_dec(v___x_707_);
v_doElems_718_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_719_ = l_Lean_Syntax_isIdent(v___x_716_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_716_);
v___x_721_ = l_Lean_Syntax_isOfKind(v___x_716_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_716_, v___x_721_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v_a_724_; lean_object* v_ref_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_n(v_a_723_, 2);
v_a_724_ = lean_ctor_get(v___x_722_, 1);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_722_, 2);
v_ref_725_ = lean_ctor_get(v___y_714_, 5);
v___x_726_ = l_Lean_SourceInfo_fromRef(v_ref_725_, v___x_721_);
v___x_727_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_728_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_729_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_730_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_731_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_726_, 15);
v___x_732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_726_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_734_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_734_, 0, v___x_726_);
lean_ctor_set(v___x_734_, 1, v___x_728_);
lean_ctor_set(v___x_734_, 2, v___x_733_);
v___x_735_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_734_, 4);
v___x_736_ = l_Lean_Syntax_node2(v___x_726_, v___x_735_, v___x_734_, v_a_723_);
v___x_737_ = l_Lean_Syntax_node1(v___x_726_, v___x_728_, v___x_736_);
v___x_738_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_726_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_741_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_742_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_726_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_Syntax_node1(v___x_726_, v___x_728_, v___x_716_);
v___x_745_ = l_Lean_Syntax_node1(v___x_726_, v___x_728_, v___x_744_);
v___x_746_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_726_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_Syntax_node4(v___x_726_, v___x_741_, v___x_743_, v___x_745_, v___x_747_, v_body_711_);
v___x_749_ = l_Lean_Syntax_node1(v___x_726_, v___x_728_, v___x_748_);
v___x_750_ = l_Lean_Syntax_node1(v___x_726_, v___x_740_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node7(v___x_726_, v___x_730_, v___x_732_, v___x_734_, v___x_734_, v___x_734_, v___x_737_, v___x_739_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node2(v___x_726_, v___x_729_, v___x_751_, v___x_734_);
v___x_753_ = l_Lean_Syntax_node1(v___x_726_, v___x_728_, v___x_752_);
v___x_754_ = l_Lean_Syntax_node1(v___x_726_, v___x_727_, v___x_753_);
v___y_663_ = v_doElems_718_;
v___y_664_ = v___x_717_;
v___y_665_ = v_h_x3f_713_;
v_x_666_ = v_a_723_;
v_body_667_ = v___x_754_;
v___y_668_ = v___y_714_;
v___y_669_ = v_a_724_;
goto v___jp_662_;
}
else
{
lean_object* v_a_755_; lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v___x_717_);
lean_dec(v___x_716_);
lean_dec(v_h_x3f_713_);
lean_dec(v_body_711_);
lean_dec_ref(v_decls_661_);
lean_dec(v_tk_624_);
v_a_755_ = lean_ctor_get(v___x_722_, 0);
v_a_756_ = lean_ctor_get(v___x_722_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_722_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_inc(v_a_755_);
lean_dec(v___x_722_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_755_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_716_, v___x_719_, v___y_714_, v___y_715_);
lean_dec(v___x_716_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v_a_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
v_a_766_ = lean_ctor_get(v___x_764_, 1);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_764_, 2);
v___y_663_ = v_doElems_718_;
v___y_664_ = v___x_717_;
v___y_665_ = v_h_x3f_713_;
v_x_666_ = v_a_765_;
v_body_667_ = v_body_711_;
v___y_668_ = v___y_714_;
v___y_669_ = v_a_766_;
goto v___jp_662_;
}
else
{
lean_object* v_a_767_; lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v___x_717_);
lean_dec(v_h_x3f_713_);
lean_dec(v_body_711_);
lean_dec_ref(v_decls_661_);
lean_dec(v_tk_624_);
v_a_767_ = lean_ctor_get(v___x_764_, 0);
v_a_768_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_764_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_inc(v_a_767_);
lean_dec(v___x_764_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_767_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
else
{
v___y_663_ = v_doElems_718_;
v___y_664_ = v___x_717_;
v___y_665_ = v_h_x3f_713_;
v_x_666_ = v___x_716_;
v_body_667_ = v_body_711_;
v___y_668_ = v___y_714_;
v___y_669_ = v___y_715_;
goto v___jp_662_;
}
}
}
v___jp_629_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_inc_ref_n(v___y_632_, 3);
v___x_641_ = l_Array_append___redArg(v___y_632_, v___y_640_);
lean_dec_ref(v___y_640_);
lean_inc_n(v___y_639_, 4);
lean_inc_n(v___y_631_, 10);
v___x_642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_642_, 0, v___y_631_);
lean_ctor_set(v___x_642_, 1, v___y_639_);
lean_ctor_set(v___x_642_, 2, v___x_641_);
v___x_643_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_644_, 0, v___y_631_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = l_Lean_Syntax_node4(v___y_631_, v___x_628_, v___x_642_, v___y_630_, v___x_644_, v___y_634_);
v___x_646_ = l_Lean_Syntax_node1(v___y_631_, v___y_639_, v___x_645_);
v___x_647_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_631_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
lean_inc_ref(v___x_648_);
v___x_649_ = l_Lean_Syntax_node4(v___y_631_, v___x_620_, v___y_637_, v___x_646_, v___x_648_, v___y_638_);
v___x_650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_650_, 0, v___y_631_);
lean_ctor_set(v___x_650_, 1, v___y_639_);
lean_ctor_set(v___x_650_, 2, v___y_632_);
lean_inc(v___y_636_);
v___x_651_ = l_Lean_Syntax_node2(v___y_631_, v___y_636_, v___x_649_, v___x_650_);
v___x_652_ = lean_array_push(v___y_633_, v___x_651_);
v___x_653_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_654_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_655_ = l_Array_append___redArg(v___y_632_, v___x_652_);
lean_dec_ref(v___x_652_);
v___x_656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_656_, 0, v___y_631_);
lean_ctor_set(v___x_656_, 1, v___y_639_);
lean_ctor_set(v___x_656_, 2, v___x_655_);
v___x_657_ = l_Lean_Syntax_node1(v___y_631_, v___x_654_, v___x_656_);
v___x_658_ = l_Lean_Syntax_node2(v___y_631_, v___x_653_, v___x_648_, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___y_635_);
return v___x_659_;
}
v___jp_662_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_array_get_size(v_decls_661_);
v___x_671_ = l_Array_toSubarray___redArg(v_decls_661_, v___x_625_, v___x_670_);
lean_inc_ref(v___y_663_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___y_663_);
lean_ctor_set(v___x_672_, 1, v_body_667_);
v___x_673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_627_, v___x_671_, v___x_672_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v_a_675_; lean_object* v_fst_676_; lean_object* v_snd_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_696_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
v_a_675_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_673_, 2);
v_fst_676_ = lean_ctor_get(v_a_674_, 0);
v_snd_677_ = lean_ctor_get(v_a_674_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_696_ == 0)
{
v___x_679_ = v_a_674_;
v_isShared_680_ = v_isSharedCheck_696_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snd_677_);
lean_inc(v_fst_676_);
lean_dec(v_a_674_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_696_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_ref_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v_ref_681_ = lean_ctor_get(v___y_668_, 5);
v___x_682_ = l_Lean_SourceInfo_fromRef(v_ref_681_, v___x_627_);
v___x_683_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_684_ = l_Lean_SourceInfo_fromRef(v_tk_624_, v___x_621_);
lean_dec(v_tk_624_);
v___x_685_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 2);
lean_ctor_set(v___x_679_, 1, v___x_685_);
lean_ctor_set(v___x_679_, 0, v___x_684_);
v___x_687_ = v___x_679_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_685_);
v___x_687_ = v_reuseFailAlloc_695_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_689_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_665_) == 1)
{
lean_object* v_val_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_val_690_ = lean_ctor_get(v___y_665_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___y_665_, 1);
v___x_691_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_682_);
v___x_692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_682_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Array_mkArray2___redArg(v_val_690_, v___x_692_);
v___y_630_ = v_x_666_;
v___y_631_ = v___x_682_;
v___y_632_ = v___x_689_;
v___y_633_ = v_fst_676_;
v___y_634_ = v___y_664_;
v___y_635_ = v_a_675_;
v___y_636_ = v___x_683_;
v___y_637_ = v___x_687_;
v___y_638_ = v_snd_677_;
v___y_639_ = v___x_688_;
v___y_640_ = v___x_693_;
goto v___jp_629_;
}
else
{
lean_object* v___x_694_; 
lean_dec(v___y_665_);
v___x_694_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_630_ = v_x_666_;
v___y_631_ = v___x_682_;
v___y_632_ = v___x_689_;
v___y_633_ = v_fst_676_;
v___y_634_ = v___y_664_;
v___y_635_ = v_a_675_;
v___y_636_ = v___x_683_;
v___y_637_ = v___x_687_;
v___y_638_ = v_snd_677_;
v___y_639_ = v___x_688_;
v___y_640_ = v___x_694_;
goto v___jp_629_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_x_666_);
lean_dec(v___y_665_);
lean_dec(v___y_664_);
lean_dec(v_tk_624_);
v_a_697_ = lean_ctor_get(v___x_673_, 0);
v_a_698_ = lean_ctor_get(v___x_673_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_673_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_inc(v_a_697_);
lean_dec(v___x_673_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_697_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; uint8_t v___y_853_; lean_object* v_x_854_; lean_object* v_body_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; uint8_t v___y_898_; lean_object* v___y_899_; lean_object* v_h_x3f_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; uint8_t v___x_1017_; 
v___x_784_ = l_Lean_Syntax_getArg(v___x_626_, v___x_623_);
v___x_785_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_784_);
v___x_1017_ = l_Lean_Syntax_isOfKind(v___x_784_, v___x_785_);
if (v___x_1017_ == 0)
{
lean_object* v_decls_1018_; lean_object* v_decls_1019_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v_x_1024_; lean_object* v_body_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
lean_dec(v___x_784_);
v_decls_1018_ = l_Lean_Syntax_getArgs(v___x_626_);
lean_dec(v___x_626_);
v_decls_1019_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1018_);
lean_dec_ref(v_decls_1018_);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_array_get(v___x_1064_, v_decls_1019_, v___x_623_);
lean_inc(v___x_1065_);
v___x_1066_ = l_Lean_Syntax_isOfKind(v___x_1065_, v___x_785_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_dec(v___x_1065_);
lean_dec_ref(v_decls_1019_);
lean_dec(v_tk_624_);
lean_dec(v_stx_617_);
v___x_1067_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; lean_object* v_body_1069_; lean_object* v_h_x3f_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1068_ = lean_unsigned_to_nat(3u);
v_body_1069_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_1068_);
lean_dec(v_stx_617_);
v___x_1134_ = l_Lean_Syntax_getArg(v___x_1065_, v___x_623_);
v___x_1135_ = l_Lean_Syntax_isNone(v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1134_);
v___x_1137_ = l_Lean_Syntax_matchesNull(v___x_1134_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec(v___x_1134_);
lean_dec(v_body_1069_);
lean_dec(v___x_1065_);
lean_dec_ref(v_decls_1019_);
lean_dec(v_tk_624_);
v___x_1138_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_1138_;
}
else
{
lean_object* v_h_x3f_1139_; lean_object* v___x_1140_; 
v_h_x3f_1139_ = l_Lean_Syntax_getArg(v___x_1134_, v___x_623_);
lean_dec(v___x_1134_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_h_x3f_1139_);
v_h_x3f_1071_ = v___x_1140_;
v___y_1072_ = v_a_618_;
v___y_1073_ = v_a_619_;
goto v___jp_1070_;
}
}
else
{
lean_object* v___x_1141_; 
lean_dec(v___x_1134_);
v___x_1141_ = lean_box(0);
v_h_x3f_1071_ = v___x_1141_;
v___y_1072_ = v_a_618_;
v___y_1073_ = v_a_619_;
goto v___jp_1070_;
}
v___jp_1070_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_doElems_1076_; uint8_t v___x_1077_; 
v___x_1074_ = l_Lean_Syntax_getArg(v___x_1065_, v___x_625_);
v___x_1075_ = l_Lean_Syntax_getArg(v___x_1065_, v___x_1068_);
lean_dec(v___x_1065_);
v_doElems_1076_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1077_ = l_Lean_Syntax_isIdent(v___x_1074_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1074_);
v___x_1079_ = l_Lean_Syntax_isOfKind(v___x_1074_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1074_, v___x_1079_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_a_1082_; lean_object* v_ref_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc_n(v_a_1081_, 2);
v_a_1082_ = lean_ctor_get(v___x_1080_, 1);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1080_, 2);
v_ref_1083_ = lean_ctor_get(v___y_1072_, 5);
v___x_1084_ = l_Lean_SourceInfo_fromRef(v_ref_1083_, v___x_1079_);
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1086_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1089_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1084_, 15);
v___x_1090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1084_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1084_);
lean_ctor_set(v___x_1092_, 1, v___x_1086_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1092_, 4);
v___x_1094_ = l_Lean_Syntax_node2(v___x_1084_, v___x_1093_, v___x_1092_, v_a_1081_);
v___x_1095_ = l_Lean_Syntax_node1(v___x_1084_, v___x_1086_, v___x_1094_);
v___x_1096_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1084_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1099_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1100_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1084_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = l_Lean_Syntax_node1(v___x_1084_, v___x_1086_, v___x_1074_);
v___x_1103_ = l_Lean_Syntax_node1(v___x_1084_, v___x_1086_, v___x_1102_);
v___x_1104_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1084_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = l_Lean_Syntax_node4(v___x_1084_, v___x_1099_, v___x_1101_, v___x_1103_, v___x_1105_, v_body_1069_);
v___x_1107_ = l_Lean_Syntax_node1(v___x_1084_, v___x_1086_, v___x_1106_);
v___x_1108_ = l_Lean_Syntax_node1(v___x_1084_, v___x_1098_, v___x_1107_);
v___x_1109_ = l_Lean_Syntax_node7(v___x_1084_, v___x_1088_, v___x_1090_, v___x_1092_, v___x_1092_, v___x_1092_, v___x_1095_, v___x_1097_, v___x_1108_);
v___x_1110_ = l_Lean_Syntax_node2(v___x_1084_, v___x_1087_, v___x_1109_, v___x_1092_);
v___x_1111_ = l_Lean_Syntax_node1(v___x_1084_, v___x_1086_, v___x_1110_);
v___x_1112_ = l_Lean_Syntax_node1(v___x_1084_, v___x_1085_, v___x_1111_);
v___y_1021_ = v_h_x3f_1071_;
v___y_1022_ = v___x_1075_;
v___y_1023_ = v_doElems_1076_;
v_x_1024_ = v_a_1081_;
v_body_1025_ = v___x_1112_;
v___y_1026_ = v___y_1072_;
v___y_1027_ = v_a_1082_;
goto v___jp_1020_;
}
else
{
lean_object* v_a_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v___x_1075_);
lean_dec(v___x_1074_);
lean_dec(v_h_x3f_1071_);
lean_dec(v_body_1069_);
lean_dec_ref(v_decls_1019_);
lean_dec(v_tk_624_);
v_a_1113_ = lean_ctor_get(v___x_1080_, 0);
v_a_1114_ = lean_ctor_get(v___x_1080_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1080_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_inc(v_a_1113_);
lean_dec(v___x_1080_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1113_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1074_, v___x_1077_, v___y_1072_, v___y_1073_);
lean_dec(v___x_1074_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v_a_1124_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
v_a_1124_ = lean_ctor_get(v___x_1122_, 1);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1122_, 2);
v___y_1021_ = v_h_x3f_1071_;
v___y_1022_ = v___x_1075_;
v___y_1023_ = v_doElems_1076_;
v_x_1024_ = v_a_1123_;
v_body_1025_ = v_body_1069_;
v___y_1026_ = v___y_1072_;
v___y_1027_ = v_a_1124_;
goto v___jp_1020_;
}
else
{
lean_object* v_a_1125_; lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v___x_1075_);
lean_dec(v_h_x3f_1071_);
lean_dec(v_body_1069_);
lean_dec_ref(v_decls_1019_);
lean_dec(v_tk_624_);
v_a_1125_ = lean_ctor_get(v___x_1122_, 0);
v_a_1126_ = lean_ctor_get(v___x_1122_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1122_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_inc(v_a_1125_);
lean_dec(v___x_1122_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1125_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
else
{
v___y_1021_ = v_h_x3f_1071_;
v___y_1022_ = v___x_1075_;
v___y_1023_ = v_doElems_1076_;
v_x_1024_ = v___x_1074_;
v_body_1025_ = v_body_1069_;
v___y_1026_ = v___y_1072_;
v___y_1027_ = v___y_1073_;
goto v___jp_1020_;
}
}
}
v___jp_1020_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = lean_array_get_size(v_decls_1019_);
v___x_1029_ = l_Array_toSubarray___redArg(v_decls_1019_, v___x_625_, v___x_1028_);
lean_inc_ref(v___y_1023_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___y_1023_);
lean_ctor_set(v___x_1030_, 1, v_body_1025_);
v___x_1031_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1017_, v___x_1029_, v___x_1030_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v_a_1033_; lean_object* v_fst_1034_; lean_object* v_snd_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1054_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
v_a_1033_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1031_, 2);
v_fst_1034_ = lean_ctor_get(v_a_1032_, 0);
v_snd_1035_ = lean_ctor_get(v_a_1032_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_a_1032_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1037_ = v_a_1032_;
v_isShared_1038_ = v_isSharedCheck_1054_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_snd_1035_);
lean_inc(v_fst_1034_);
lean_dec(v_a_1032_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1054_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_ref_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v_ref_1039_ = lean_ctor_get(v___y_1026_, 5);
v___x_1040_ = l_Lean_SourceInfo_fromRef(v_ref_1039_, v___x_1017_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1042_ = l_Lean_SourceInfo_fromRef(v_tk_624_, v___x_621_);
lean_dec(v_tk_624_);
v___x_1043_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 2);
lean_ctor_set(v___x_1037_, 1, v___x_1043_);
lean_ctor_set(v___x_1037_, 0, v___x_1042_);
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1047_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1021_) == 1)
{
lean_object* v_val_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_val_1048_ = lean_ctor_get(v___y_1021_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v___y_1021_, 1);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1040_);
v___x_1050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1040_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l_Array_mkArray2___redArg(v_val_1048_, v___x_1050_);
v___y_987_ = v___x_1046_;
v___y_988_ = v___x_1040_;
v___y_989_ = v_snd_1035_;
v___y_990_ = v___x_1047_;
v___y_991_ = v_fst_1034_;
v___y_992_ = v___x_1045_;
v___y_993_ = v___x_1041_;
v___y_994_ = v_x_1024_;
v___y_995_ = v___y_1022_;
v___y_996_ = v_a_1033_;
v___y_997_ = v___x_1051_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1052_; 
lean_dec(v___y_1021_);
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_987_ = v___x_1046_;
v___y_988_ = v___x_1040_;
v___y_989_ = v_snd_1035_;
v___y_990_ = v___x_1047_;
v___y_991_ = v_fst_1034_;
v___y_992_ = v___x_1045_;
v___y_993_ = v___x_1041_;
v___y_994_ = v_x_1024_;
v___y_995_ = v___y_1022_;
v___y_996_ = v_a_1033_;
v___y_997_ = v___x_1052_;
goto v___jp_986_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_x_1024_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec(v_tk_624_);
v_a_1055_ = lean_ctor_get(v___x_1031_, 0);
v_a_1056_ = lean_ctor_get(v___x_1031_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1031_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_inc(v_a_1055_);
lean_dec(v___x_1031_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1055_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1142_ = l_Lean_Syntax_getArg(v___x_784_, v___x_623_);
v___x_1143_ = l_Lean_Syntax_isNone(v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(2u);
v___x_1145_ = l_Lean_Syntax_matchesNull(v___x_1142_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v_decls_1146_; lean_object* v_decls_1147_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v_x_1152_; lean_object* v_body_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
lean_dec(v___x_784_);
v_decls_1146_ = l_Lean_Syntax_getArgs(v___x_626_);
lean_dec(v___x_626_);
v_decls_1147_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1146_);
lean_dec_ref(v_decls_1146_);
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_array_get(v___x_1192_, v_decls_1147_, v___x_623_);
lean_inc(v___x_1193_);
v___x_1194_ = l_Lean_Syntax_isOfKind(v___x_1193_, v___x_785_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; 
lean_dec(v___x_1193_);
lean_dec_ref(v_decls_1147_);
lean_dec(v_tk_624_);
lean_dec(v_stx_617_);
v___x_1195_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; lean_object* v_body_1197_; lean_object* v_h_x3f_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1196_ = lean_unsigned_to_nat(3u);
v_body_1197_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_1196_);
lean_dec(v_stx_617_);
v___x_1262_ = l_Lean_Syntax_getArg(v___x_1193_, v___x_623_);
v___x_1263_ = l_Lean_Syntax_isNone(v___x_1262_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
lean_inc(v___x_1262_);
v___x_1264_ = l_Lean_Syntax_matchesNull(v___x_1262_, v___x_1144_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec(v___x_1262_);
lean_dec(v_body_1197_);
lean_dec(v___x_1193_);
lean_dec_ref(v_decls_1147_);
lean_dec(v_tk_624_);
v___x_1265_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_1265_;
}
else
{
lean_object* v_h_x3f_1266_; lean_object* v___x_1267_; 
v_h_x3f_1266_ = l_Lean_Syntax_getArg(v___x_1262_, v___x_623_);
lean_dec(v___x_1262_);
v___x_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_h_x3f_1266_);
v_h_x3f_1199_ = v___x_1267_;
v___y_1200_ = v_a_618_;
v___y_1201_ = v_a_619_;
goto v___jp_1198_;
}
}
else
{
lean_object* v___x_1268_; 
lean_dec(v___x_1262_);
v___x_1268_ = lean_box(0);
v_h_x3f_1199_ = v___x_1268_;
v___y_1200_ = v_a_618_;
v___y_1201_ = v_a_619_;
goto v___jp_1198_;
}
v___jp_1198_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_doElems_1204_; uint8_t v___x_1205_; 
v___x_1202_ = l_Lean_Syntax_getArg(v___x_1193_, v___x_625_);
v___x_1203_ = l_Lean_Syntax_getArg(v___x_1193_, v___x_1196_);
lean_dec(v___x_1193_);
v_doElems_1204_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1205_ = l_Lean_Syntax_isIdent(v___x_1202_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1202_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v___x_1202_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1202_, v___x_1207_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v_a_1210_; lean_object* v_ref_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc_n(v_a_1209_, 2);
v_a_1210_ = lean_ctor_get(v___x_1208_, 1);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1208_, 2);
v_ref_1211_ = lean_ctor_get(v___y_1200_, 5);
v___x_1212_ = l_Lean_SourceInfo_fromRef(v_ref_1211_, v___x_1207_);
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1214_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1215_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1216_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1217_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1212_, 15);
v___x_1218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1212_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1212_);
lean_ctor_set(v___x_1220_, 1, v___x_1214_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1220_, 4);
v___x_1222_ = l_Lean_Syntax_node2(v___x_1212_, v___x_1221_, v___x_1220_, v_a_1209_);
v___x_1223_ = l_Lean_Syntax_node1(v___x_1212_, v___x_1214_, v___x_1222_);
v___x_1224_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1212_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1227_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1228_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1212_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_Syntax_node1(v___x_1212_, v___x_1214_, v___x_1202_);
v___x_1231_ = l_Lean_Syntax_node1(v___x_1212_, v___x_1214_, v___x_1230_);
v___x_1232_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1212_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_Syntax_node4(v___x_1212_, v___x_1227_, v___x_1229_, v___x_1231_, v___x_1233_, v_body_1197_);
v___x_1235_ = l_Lean_Syntax_node1(v___x_1212_, v___x_1214_, v___x_1234_);
v___x_1236_ = l_Lean_Syntax_node1(v___x_1212_, v___x_1226_, v___x_1235_);
v___x_1237_ = l_Lean_Syntax_node7(v___x_1212_, v___x_1216_, v___x_1218_, v___x_1220_, v___x_1220_, v___x_1220_, v___x_1223_, v___x_1225_, v___x_1236_);
v___x_1238_ = l_Lean_Syntax_node2(v___x_1212_, v___x_1215_, v___x_1237_, v___x_1220_);
v___x_1239_ = l_Lean_Syntax_node1(v___x_1212_, v___x_1214_, v___x_1238_);
v___x_1240_ = l_Lean_Syntax_node1(v___x_1212_, v___x_1213_, v___x_1239_);
v___y_1149_ = v___x_1203_;
v___y_1150_ = v_h_x3f_1199_;
v___y_1151_ = v_doElems_1204_;
v_x_1152_ = v_a_1209_;
v_body_1153_ = v___x_1240_;
v___y_1154_ = v___y_1200_;
v___y_1155_ = v_a_1210_;
goto v___jp_1148_;
}
else
{
lean_object* v_a_1241_; lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v___x_1203_);
lean_dec(v___x_1202_);
lean_dec(v_h_x3f_1199_);
lean_dec(v_body_1197_);
lean_dec_ref(v_decls_1147_);
lean_dec(v_tk_624_);
v_a_1241_ = lean_ctor_get(v___x_1208_, 0);
v_a_1242_ = lean_ctor_get(v___x_1208_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1208_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_inc(v_a_1241_);
lean_dec(v___x_1208_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1241_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1202_, v___x_1205_, v___y_1200_, v___y_1201_);
lean_dec(v___x_1202_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v_a_1252_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
v_a_1252_ = lean_ctor_get(v___x_1250_, 1);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1250_, 2);
v___y_1149_ = v___x_1203_;
v___y_1150_ = v_h_x3f_1199_;
v___y_1151_ = v_doElems_1204_;
v_x_1152_ = v_a_1251_;
v_body_1153_ = v_body_1197_;
v___y_1154_ = v___y_1200_;
v___y_1155_ = v_a_1252_;
goto v___jp_1148_;
}
else
{
lean_object* v_a_1253_; lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v___x_1203_);
lean_dec(v_h_x3f_1199_);
lean_dec(v_body_1197_);
lean_dec_ref(v_decls_1147_);
lean_dec(v_tk_624_);
v_a_1253_ = lean_ctor_get(v___x_1250_, 0);
v_a_1254_ = lean_ctor_get(v___x_1250_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1250_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_inc(v_a_1253_);
lean_dec(v___x_1250_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1253_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
else
{
v___y_1149_ = v___x_1203_;
v___y_1150_ = v_h_x3f_1199_;
v___y_1151_ = v_doElems_1204_;
v_x_1152_ = v___x_1202_;
v_body_1153_ = v_body_1197_;
v___y_1154_ = v___y_1200_;
v___y_1155_ = v___y_1201_;
goto v___jp_1148_;
}
}
}
v___jp_1148_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = lean_array_get_size(v_decls_1147_);
v___x_1157_ = l_Array_toSubarray___redArg(v_decls_1147_, v___x_625_, v___x_1156_);
lean_inc_ref(v___y_1151_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___y_1151_);
lean_ctor_set(v___x_1158_, 1, v_body_1153_);
v___x_1159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1145_, v___x_1157_, v___x_1158_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v_a_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1182_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
v_a_1161_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1159_, 2);
v_fst_1162_ = lean_ctor_get(v_a_1160_, 0);
v_snd_1163_ = lean_ctor_get(v_a_1160_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_a_1160_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1165_ = v_a_1160_;
v_isShared_1166_ = v_isSharedCheck_1182_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_snd_1163_);
lean_inc(v_fst_1162_);
lean_dec(v_a_1160_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1182_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_ref_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v_ref_1167_ = lean_ctor_get(v___y_1154_, 5);
v___x_1168_ = l_Lean_SourceInfo_fromRef(v_ref_1167_, v___x_1145_);
v___x_1169_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1170_ = l_Lean_SourceInfo_fromRef(v_tk_624_, v___x_621_);
lean_dec(v_tk_624_);
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 2);
lean_ctor_set(v___x_1165_, 1, v___x_1171_);
lean_ctor_set(v___x_1165_, 0, v___x_1170_);
v___x_1173_ = v___x_1165_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1175_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1150_) == 1)
{
lean_object* v_val_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_val_1176_ = lean_ctor_get(v___y_1150_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v___y_1150_, 1);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1168_);
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1168_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Array_mkArray2___redArg(v_val_1176_, v___x_1178_);
v___y_787_ = v___y_1149_;
v___y_788_ = v___x_1168_;
v___y_789_ = v_a_1161_;
v___y_790_ = v_snd_1163_;
v___y_791_ = v___x_1174_;
v___y_792_ = v___x_1169_;
v___y_793_ = v_fst_1162_;
v___y_794_ = v_x_1152_;
v___y_795_ = v___x_1175_;
v___y_796_ = v___x_1173_;
v___y_797_ = v___x_1179_;
goto v___jp_786_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v___y_1150_);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_787_ = v___y_1149_;
v___y_788_ = v___x_1168_;
v___y_789_ = v_a_1161_;
v___y_790_ = v_snd_1163_;
v___y_791_ = v___x_1174_;
v___y_792_ = v___x_1169_;
v___y_793_ = v_fst_1162_;
v___y_794_ = v_x_1152_;
v___y_795_ = v___x_1175_;
v___y_796_ = v___x_1173_;
v___y_797_ = v___x_1180_;
goto v___jp_786_;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_x_1152_);
lean_dec(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec(v_tk_624_);
v_a_1183_ = lean_ctor_get(v___x_1159_, 0);
v_a_1184_ = lean_ctor_get(v___x_1159_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1159_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_inc(v_a_1183_);
lean_dec(v___x_1159_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1183_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
else
{
v___y_964_ = v_a_618_;
v___y_965_ = v_a_619_;
goto v___jp_963_;
}
}
else
{
lean_dec(v___x_1142_);
v___y_964_ = v_a_618_;
v___y_965_ = v_a_619_;
goto v___jp_963_;
}
}
v___jp_786_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_inc_ref_n(v___y_795_, 3);
v___x_798_ = l_Array_append___redArg(v___y_795_, v___y_797_);
lean_dec_ref(v___y_797_);
lean_inc_n(v___y_791_, 4);
lean_inc_n(v___y_788_, 10);
v___x_799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_799_, 0, v___y_788_);
lean_ctor_set(v___x_799_, 1, v___y_791_);
lean_ctor_set(v___x_799_, 2, v___x_798_);
v___x_800_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_801_, 0, v___y_788_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_Syntax_node4(v___y_788_, v___x_785_, v___x_799_, v___y_794_, v___x_801_, v___y_787_);
v___x_803_ = l_Lean_Syntax_node1(v___y_788_, v___y_791_, v___x_802_);
v___x_804_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v___y_788_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
lean_inc_ref(v___x_805_);
v___x_806_ = l_Lean_Syntax_node4(v___y_788_, v___x_620_, v___y_796_, v___x_803_, v___x_805_, v___y_790_);
v___x_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_807_, 0, v___y_788_);
lean_ctor_set(v___x_807_, 1, v___y_791_);
lean_ctor_set(v___x_807_, 2, v___y_795_);
lean_inc(v___y_792_);
v___x_808_ = l_Lean_Syntax_node2(v___y_788_, v___y_792_, v___x_806_, v___x_807_);
v___x_809_ = lean_array_push(v___y_793_, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_811_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_812_ = l_Array_append___redArg(v___y_795_, v___x_809_);
lean_dec_ref(v___x_809_);
v___x_813_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_813_, 0, v___y_788_);
lean_ctor_set(v___x_813_, 1, v___y_791_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
v___x_814_ = l_Lean_Syntax_node1(v___y_788_, v___x_811_, v___x_813_);
v___x_815_ = l_Lean_Syntax_node2(v___y_788_, v___x_810_, v___x_805_, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___y_789_);
return v___x_816_;
}
v___jp_817_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_inc_ref_n(v___y_824_, 3);
v___x_829_ = l_Array_append___redArg(v___y_824_, v___y_828_);
lean_dec_ref(v___y_828_);
lean_inc_n(v___y_820_, 4);
lean_inc_n(v___y_825_, 10);
v___x_830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_830_, 0, v___y_825_);
lean_ctor_set(v___x_830_, 1, v___y_820_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
v___x_831_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_825_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_Syntax_node4(v___y_825_, v___x_785_, v___x_830_, v___y_818_, v___x_832_, v___y_819_);
v___x_834_ = l_Lean_Syntax_node1(v___y_825_, v___y_820_, v___x_833_);
v___x_835_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_825_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
lean_inc_ref(v___x_836_);
v___x_837_ = l_Lean_Syntax_node4(v___y_825_, v___x_620_, v___y_823_, v___x_834_, v___x_836_, v___y_821_);
v___x_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_838_, 0, v___y_825_);
lean_ctor_set(v___x_838_, 1, v___y_820_);
lean_ctor_set(v___x_838_, 2, v___y_824_);
lean_inc(v___y_822_);
v___x_839_ = l_Lean_Syntax_node2(v___y_825_, v___y_822_, v___x_837_, v___x_838_);
v___x_840_ = lean_array_push(v___y_826_, v___x_839_);
v___x_841_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_842_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_843_ = l_Array_append___redArg(v___y_824_, v___x_840_);
lean_dec_ref(v___x_840_);
v___x_844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_844_, 0, v___y_825_);
lean_ctor_set(v___x_844_, 1, v___y_820_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
v___x_845_ = l_Lean_Syntax_node1(v___y_825_, v___x_842_, v___x_844_);
v___x_846_ = l_Lean_Syntax_node2(v___y_825_, v___x_841_, v___x_836_, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___y_827_);
return v___x_847_;
}
v___jp_848_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = lean_array_get_size(v___y_851_);
v___x_859_ = l_Array_toSubarray___redArg(v___y_851_, v___x_625_, v___x_858_);
lean_inc_ref(v___y_852_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_852_);
lean_ctor_set(v___x_860_, 1, v_body_855_);
v___x_861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_853_, v___x_859_, v___x_860_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v_a_863_; lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_884_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
v_a_863_ = lean_ctor_get(v___x_861_, 1);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_861_, 2);
v_fst_864_ = lean_ctor_get(v_a_862_, 0);
v_snd_865_ = lean_ctor_get(v_a_862_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_884_ == 0)
{
v___x_867_ = v_a_862_;
v_isShared_868_ = v_isSharedCheck_884_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_snd_865_);
lean_inc(v_fst_864_);
lean_dec(v_a_862_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_884_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_ref_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v_ref_869_ = lean_ctor_get(v___y_856_, 5);
v___x_870_ = l_Lean_SourceInfo_fromRef(v_ref_869_, v___y_853_);
v___x_871_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_872_ = l_Lean_SourceInfo_fromRef(v_tk_624_, v___x_621_);
lean_dec(v_tk_624_);
v___x_873_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 2);
lean_ctor_set(v___x_867_, 1, v___x_873_);
lean_ctor_set(v___x_867_, 0, v___x_872_);
v___x_875_ = v___x_867_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_883_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_877_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_850_) == 1)
{
lean_object* v_val_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_val_878_ = lean_ctor_get(v___y_850_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v___y_850_, 1);
v___x_879_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_870_);
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_870_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Array_mkArray2___redArg(v_val_878_, v___x_880_);
v___y_818_ = v_x_854_;
v___y_819_ = v___y_849_;
v___y_820_ = v___x_876_;
v___y_821_ = v_snd_865_;
v___y_822_ = v___x_871_;
v___y_823_ = v___x_875_;
v___y_824_ = v___x_877_;
v___y_825_ = v___x_870_;
v___y_826_ = v_fst_864_;
v___y_827_ = v_a_863_;
v___y_828_ = v___x_881_;
goto v___jp_817_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v___y_850_);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_818_ = v_x_854_;
v___y_819_ = v___y_849_;
v___y_820_ = v___x_876_;
v___y_821_ = v_snd_865_;
v___y_822_ = v___x_871_;
v___y_823_ = v___x_875_;
v___y_824_ = v___x_877_;
v___y_825_ = v___x_870_;
v___y_826_ = v_fst_864_;
v___y_827_ = v_a_863_;
v___y_828_ = v___x_882_;
goto v___jp_817_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_x_854_);
lean_dec(v___y_850_);
lean_dec(v___y_849_);
lean_dec(v_tk_624_);
v_a_885_ = lean_ctor_get(v___x_861_, 0);
v_a_886_ = lean_ctor_get(v___x_861_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_861_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_inc(v_a_885_);
lean_dec(v___x_861_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_885_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
v___jp_894_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v_doElems_905_; uint8_t v___x_906_; 
v___x_903_ = l_Lean_Syntax_getArg(v___y_899_, v___x_625_);
v___x_904_ = l_Lean_Syntax_getArg(v___y_899_, v___y_895_);
lean_dec(v___y_899_);
v_doElems_905_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_906_ = l_Lean_Syntax_isIdent(v___x_903_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_903_);
v___x_908_ = l_Lean_Syntax_isOfKind(v___x_903_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_903_, v___y_898_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_a_911_; lean_object* v_ref_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc_n(v_a_910_, 2);
v_a_911_ = lean_ctor_get(v___x_909_, 1);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_909_, 2);
v_ref_912_ = lean_ctor_get(v___y_901_, 5);
v___x_913_ = l_Lean_SourceInfo_fromRef(v_ref_912_, v___y_898_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_916_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_917_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_918_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_913_, 15);
v___x_919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_913_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_921_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_921_, 0, v___x_913_);
lean_ctor_set(v___x_921_, 1, v___x_915_);
lean_ctor_set(v___x_921_, 2, v___x_920_);
v___x_922_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_921_, 4);
v___x_923_ = l_Lean_Syntax_node2(v___x_913_, v___x_922_, v___x_921_, v_a_910_);
v___x_924_ = l_Lean_Syntax_node1(v___x_913_, v___x_915_, v___x_923_);
v___x_925_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_913_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_928_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_929_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_913_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = l_Lean_Syntax_node1(v___x_913_, v___x_915_, v___x_903_);
v___x_932_ = l_Lean_Syntax_node1(v___x_913_, v___x_915_, v___x_931_);
v___x_933_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_913_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_Syntax_node4(v___x_913_, v___x_928_, v___x_930_, v___x_932_, v___x_934_, v___y_897_);
v___x_936_ = l_Lean_Syntax_node1(v___x_913_, v___x_915_, v___x_935_);
v___x_937_ = l_Lean_Syntax_node1(v___x_913_, v___x_927_, v___x_936_);
v___x_938_ = l_Lean_Syntax_node7(v___x_913_, v___x_917_, v___x_919_, v___x_921_, v___x_921_, v___x_921_, v___x_924_, v___x_926_, v___x_937_);
v___x_939_ = l_Lean_Syntax_node2(v___x_913_, v___x_916_, v___x_938_, v___x_921_);
v___x_940_ = l_Lean_Syntax_node1(v___x_913_, v___x_915_, v___x_939_);
v___x_941_ = l_Lean_Syntax_node1(v___x_913_, v___x_914_, v___x_940_);
v___y_849_ = v___x_904_;
v___y_850_ = v_h_x3f_900_;
v___y_851_ = v___y_896_;
v___y_852_ = v_doElems_905_;
v___y_853_ = v___y_898_;
v_x_854_ = v_a_910_;
v_body_855_ = v___x_941_;
v___y_856_ = v___y_901_;
v___y_857_ = v_a_911_;
goto v___jp_848_;
}
else
{
lean_object* v_a_942_; lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec(v_h_x3f_900_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v_tk_624_);
v_a_942_ = lean_ctor_get(v___x_909_, 0);
v_a_943_ = lean_ctor_get(v___x_909_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_909_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_inc(v_a_942_);
lean_dec(v___x_909_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_942_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_903_, v___y_898_, v___y_901_, v___y_902_);
lean_dec(v___x_903_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_a_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
v_a_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_951_, 2);
v___y_849_ = v___x_904_;
v___y_850_ = v_h_x3f_900_;
v___y_851_ = v___y_896_;
v___y_852_ = v_doElems_905_;
v___y_853_ = v___y_898_;
v_x_854_ = v_a_952_;
v_body_855_ = v___y_897_;
v___y_856_ = v___y_901_;
v___y_857_ = v_a_953_;
goto v___jp_848_;
}
else
{
lean_object* v_a_954_; lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v___x_904_);
lean_dec(v_h_x3f_900_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v_tk_624_);
v_a_954_ = lean_ctor_get(v___x_951_, 0);
v_a_955_ = lean_ctor_get(v___x_951_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_951_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_inc(v_a_954_);
lean_dec(v___x_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_954_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
else
{
v___y_849_ = v___x_904_;
v___y_850_ = v_h_x3f_900_;
v___y_851_ = v___y_896_;
v___y_852_ = v_doElems_905_;
v___y_853_ = v___y_898_;
v_x_854_ = v___x_903_;
v_body_855_ = v___y_897_;
v___y_856_ = v___y_901_;
v___y_857_ = v___y_902_;
goto v___jp_848_;
}
}
v___jp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_966_ = l_Lean_Syntax_getArg(v___x_784_, v___x_625_);
lean_dec(v___x_784_);
v___x_967_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
v___x_968_ = l_Lean_Syntax_isOfKind(v___x_966_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v_decls_969_; lean_object* v_decls_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_decls_969_ = l_Lean_Syntax_getArgs(v___x_626_);
lean_dec(v___x_626_);
v_decls_970_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_969_);
lean_dec_ref(v_decls_969_);
v___x_971_ = lean_box(0);
v___x_972_ = lean_array_get(v___x_971_, v_decls_970_, v___x_623_);
lean_inc(v___x_972_);
v___x_973_ = l_Lean_Syntax_isOfKind(v___x_972_, v___x_785_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec(v___x_972_);
lean_dec_ref(v_decls_970_);
lean_dec(v_tk_624_);
lean_dec(v_stx_617_);
v___x_974_ = l_Lean_Macro_throwUnsupported___redArg(v___y_965_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v_body_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_975_ = lean_unsigned_to_nat(3u);
v_body_976_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_975_);
lean_dec(v_stx_617_);
v___x_977_ = l_Lean_Syntax_getArg(v___x_972_, v___x_623_);
v___x_978_ = l_Lean_Syntax_isNone(v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_977_);
v___x_980_ = l_Lean_Syntax_matchesNull(v___x_977_, v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec(v___x_977_);
lean_dec(v_body_976_);
lean_dec(v___x_972_);
lean_dec_ref(v_decls_970_);
lean_dec(v_tk_624_);
v___x_981_ = l_Lean_Macro_throwUnsupported___redArg(v___y_965_);
return v___x_981_;
}
else
{
lean_object* v_h_x3f_982_; lean_object* v___x_983_; 
v_h_x3f_982_ = l_Lean_Syntax_getArg(v___x_977_, v___x_623_);
lean_dec(v___x_977_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_h_x3f_982_);
v___y_895_ = v___x_975_;
v___y_896_ = v_decls_970_;
v___y_897_ = v_body_976_;
v___y_898_ = v___x_968_;
v___y_899_ = v___x_972_;
v_h_x3f_900_ = v___x_983_;
v___y_901_ = v___y_964_;
v___y_902_ = v___y_965_;
goto v___jp_894_;
}
}
else
{
lean_object* v___x_984_; 
lean_dec(v___x_977_);
v___x_984_ = lean_box(0);
v___y_895_ = v___x_975_;
v___y_896_ = v_decls_970_;
v___y_897_ = v_body_976_;
v___y_898_ = v___x_968_;
v___y_899_ = v___x_972_;
v_h_x3f_900_ = v___x_984_;
v___y_901_ = v___y_964_;
v___y_902_ = v___y_965_;
goto v___jp_894_;
}
}
}
else
{
lean_object* v___x_985_; 
lean_dec(v___x_626_);
lean_dec(v_tk_624_);
lean_dec(v_stx_617_);
v___x_985_ = l_Lean_Macro_throwUnsupported___redArg(v___y_965_);
return v___x_985_;
}
}
v___jp_986_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_inc_ref_n(v___y_990_, 3);
v___x_998_ = l_Array_append___redArg(v___y_990_, v___y_997_);
lean_dec_ref(v___y_997_);
lean_inc_n(v___y_987_, 4);
lean_inc_n(v___y_988_, 10);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v___y_988_);
lean_ctor_set(v___x_999_, 1, v___y_987_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___y_988_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node4(v___y_988_, v___x_785_, v___x_999_, v___y_994_, v___x_1001_, v___y_995_);
v___x_1003_ = l_Lean_Syntax_node1(v___y_988_, v___y_987_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_988_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
lean_inc_ref(v___x_1005_);
v___x_1006_ = l_Lean_Syntax_node4(v___y_988_, v___x_620_, v___y_992_, v___x_1003_, v___x_1005_, v___y_989_);
v___x_1007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1007_, 0, v___y_988_);
lean_ctor_set(v___x_1007_, 1, v___y_987_);
lean_ctor_set(v___x_1007_, 2, v___y_990_);
lean_inc(v___y_993_);
v___x_1008_ = l_Lean_Syntax_node2(v___y_988_, v___y_993_, v___x_1006_, v___x_1007_);
v___x_1009_ = lean_array_push(v___y_991_, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1011_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1012_ = l_Array_append___redArg(v___y_990_, v___x_1009_);
lean_dec_ref(v___x_1009_);
v___x_1013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1013_, 0, v___y_988_);
lean_ctor_set(v___x_1013_, 1, v___y_987_);
lean_ctor_set(v___x_1013_, 2, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node1(v___y_988_, v___x_1011_, v___x_1013_);
v___x_1015_ = l_Lean_Syntax_node2(v___y_988_, v___x_1010_, v___x_1005_, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___y_996_);
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object* v_stx_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Elab_Do_expandDoFor(v_stx_1269_, v_a_1270_, v_a_1271_);
lean_dec_ref(v_a_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_1273_, lean_object* v_inst_1274_, lean_object* v_R_1275_, lean_object* v_a_1276_, lean_object* v_b_1277_, lean_object* v_c_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1273_, v_a_1276_, v_b_1277_, v___y_1279_, v___y_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_1282_, lean_object* v_inst_1283_, lean_object* v_R_1284_, lean_object* v_a_1285_, lean_object* v_b_1286_, lean_object* v_c_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v___x_148624__boxed_1290_; lean_object* v_res_1291_; 
v___x_148624__boxed_1290_ = lean_unbox(v___x_1282_);
v_res_1291_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_148624__boxed_1290_, v_inst_1283_, v_R_1284_, v_a_1285_, v_b_1286_, v_c_1287_, v___y_1288_, v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1299_ = l_Lean_Elab_macroAttribute;
v___x_1300_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_1301_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_1302_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor___boxed), 3, 0);
v___x_1303_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1299_, v___x_1300_, v___x_1301_, v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_1305_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v___x_1306_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg(){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0);
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v_00_u03b1_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v_00_u03b1_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(v_00_u03b1_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc_ref(v___y_1335_);
v___x_1344_ = lean_apply_9(v_k_1334_, v_b_1338_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, lean_box(0));
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v_b_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v_b_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_1356_, uint8_t v_bi_1357_, lean_object* v_type_1358_, lean_object* v_k_1359_, uint8_t v_kind_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___f_1369_; lean_object* v___x_1370_; 
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc_ref(v___y_1361_);
v___f_1369_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1369_, 0, v_k_1359_);
lean_closure_set(v___f_1369_, 1, v___y_1361_);
lean_closure_set(v___f_1369_, 2, v___y_1362_);
lean_closure_set(v___f_1369_, 3, v___y_1363_);
v___x_1370_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1356_, v_bi_1357_, v_type_1358_, v___f_1369_, v_kind_1360_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1370_) == 0)
{
return v___x_1370_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_1379_, lean_object* v_bi_1380_, lean_object* v_type_1381_, lean_object* v_k_1382_, lean_object* v_kind_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_bi_boxed_1392_; uint8_t v_kind_boxed_1393_; lean_object* v_res_1394_; 
v_bi_boxed_1392_ = lean_unbox(v_bi_1380_);
v_kind_boxed_1393_ = lean_unbox(v_kind_1383_);
v_res_1394_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1379_, v_bi_boxed_1392_, v_type_1381_, v_k_1382_, v_kind_boxed_1393_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_1395_, lean_object* v_name_1396_, uint8_t v_bi_1397_, lean_object* v_type_1398_, lean_object* v_k_1399_, uint8_t v_kind_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1396_, v_bi_1397_, v_type_1398_, v_k_1399_, v_kind_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_name_1411_, lean_object* v_bi_1412_, lean_object* v_type_1413_, lean_object* v_k_1414_, lean_object* v_kind_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v_bi_boxed_1424_; uint8_t v_kind_boxed_1425_; lean_object* v_res_1426_; 
v_bi_boxed_1424_ = lean_unbox(v_bi_1412_);
v_kind_boxed_1425_ = lean_unbox(v_kind_1415_);
v_res_1426_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_1410_, v_name_1411_, v_bi_boxed_1424_, v_type_1413_, v_k_1414_, v_kind_boxed_1425_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1427_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_1438_, lean_object* v_x_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_1438_, v_x_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec_ref(v_x_1439_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v_x_1449_, lean_object* v___f_1450_, lean_object* v___x_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = l_Lean_TSyntax_getId(v_x_1449_);
v___x_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
lean_ctor_set(v___x_1455_, 1, v___f_1450_);
v___x_1456_ = lean_mk_empty_array_with_capacity(v___x_1451_);
v___x_1457_ = lean_array_push(v___x_1456_, v___x_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v_x_1458_, lean_object* v___f_1459_, lean_object* v___x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Elab_Do_elabDoFor___lam__2(v_x_1458_, v___f_1459_, v___x_1460_, v_x_1461_, v_x_1462_);
lean_dec(v_x_1462_);
lean_dec(v_x_1461_);
lean_dec(v___x_1460_);
lean_dec(v_x_1458_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_a_1464_, lean_object* v___x_1465_, uint8_t v___x_1466_, lean_object* v_r_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_k_1476_; lean_object* v___x_1477_; 
v_k_1476_ = lean_ctor_get(v_a_1464_, 1);
lean_inc_ref(v_k_1476_);
lean_dec_ref(v_a_1464_);
lean_inc(v___y_1474_);
lean_inc_ref(v___y_1473_);
lean_inc(v___y_1472_);
lean_inc_ref(v___y_1471_);
lean_inc(v___y_1470_);
lean_inc_ref(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc_ref(v_r_1467_);
v___x_1477_ = lean_apply_9(v_k_1476_, v_r_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, lean_box(0));
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = lean_mk_empty_array_with_capacity(v___x_1465_);
v___x_1480_ = lean_array_push(v___x_1479_, v_r_1467_);
v___x_1481_ = 0;
v___x_1482_ = 1;
v___x_1483_ = l_Lean_Meta_mkLambdaFVars(v___x_1480_, v_a_1478_, v___x_1481_, v___x_1466_, v___x_1481_, v___x_1466_, v___x_1482_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec_ref(v___x_1480_);
return v___x_1483_;
}
else
{
lean_dec_ref(v_r_1467_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_a_1484_, lean_object* v___x_1485_, lean_object* v___x_1486_, lean_object* v_r_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v___x_71137__boxed_1496_; lean_object* v_res_1497_; 
v___x_71137__boxed_1496_ = lean_unbox(v___x_1486_);
v_res_1497_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_a_1484_, v___x_1485_, v___x_71137__boxed_1496_, v_r_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___x_1485_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v___x_1498_, lean_object* v_as_1499_, size_t v_sz_1500_, size_t v_i_1501_, lean_object* v_b_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v___x_1510_; 
v___x_1510_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_dec_ref(v___x_1498_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_b_1502_);
return v___x_1511_;
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_a_1512_ = lean_array_uget_borrowed(v_as_1499_, v_i_1501_);
v___x_1513_ = l_Lean_Elab_Do_MutVar_getId(v_a_1512_);
v___x_1514_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_1513_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v_ident_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc_n(v_a_1515_, 2);
lean_dec_ref_known(v___x_1514_, 1);
v_ident_1516_ = lean_ctor_get(v_a_1512_, 0);
v___x_1517_ = l_Lean_LocalDecl_toExpr(v_a_1515_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_box(0);
v___x_1520_ = 0;
lean_inc_ref(v___x_1517_);
lean_inc(v_ident_1516_);
v___x_1521_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_1516_, v___x_1517_, v___x_1518_, v___x_1518_, v___x_1519_, v___x_1520_, v___x_1520_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
lean_dec_ref_known(v___x_1521_, 1);
v___x_1522_ = l_Lean_LocalDecl_type(v_a_1515_);
lean_dec(v_a_1515_);
v___x_1523_ = l_Lean_Meta_getDecLevel(v___x_1522_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v_u_1525_; lean_object* v___x_1526_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v_u_1525_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_u_1525_);
v___x_1526_ = l_Lean_Meta_isLevelDefEq(v_a_1524_, v_u_1525_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v___x_1527_; size_t v___x_1528_; size_t v___x_1529_; 
lean_dec_ref_known(v___x_1526_, 1);
v___x_1527_ = lean_array_push(v_b_1502_, v___x_1517_);
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_add(v_i_1501_, v___x_1528_);
v_i_1501_ = v___x_1529_;
v_b_1502_ = v___x_1527_;
goto _start;
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_b_1502_);
lean_dec_ref(v___x_1498_);
v_a_1531_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1526_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1526_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_b_1502_);
lean_dec_ref(v___x_1498_);
v_a_1539_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1523_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1523_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v___x_1517_);
lean_dec(v_a_1515_);
lean_dec_ref(v_b_1502_);
lean_dec_ref(v___x_1498_);
v_a_1547_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1521_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1521_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_b_1502_);
lean_dec_ref(v___x_1498_);
v_a_1555_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1514_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1514_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v___x_1563_, lean_object* v_as_1564_, lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_b_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
size_t v_sz_boxed_1575_; size_t v_i_boxed_1576_; lean_object* v_res_1577_; 
v_sz_boxed_1575_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1576_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_1563_, v_as_1564_, v_sz_boxed_1575_, v_i_boxed_1576_, v_b_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec_ref(v_as_1564_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(lean_object* v_msgData_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v___x_1584_; lean_object* v_env_1585_; lean_object* v___x_1586_; lean_object* v_mctx_1587_; lean_object* v_lctx_1588_; lean_object* v_options_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1584_ = lean_st_ref_get(v___y_1582_);
v_env_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_ref(v_env_1585_);
lean_dec(v___x_1584_);
v___x_1586_ = lean_st_ref_get(v___y_1580_);
v_mctx_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc_ref(v_mctx_1587_);
lean_dec(v___x_1586_);
v_lctx_1588_ = lean_ctor_get(v___y_1579_, 2);
v_options_1589_ = lean_ctor_get(v___y_1581_, 2);
lean_inc_ref(v_options_1589_);
lean_inc_ref(v_lctx_1588_);
v___x_1590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1590_, 0, v_env_1585_);
lean_ctor_set(v___x_1590_, 1, v_mctx_1587_);
lean_ctor_set(v___x_1590_, 2, v_lctx_1588_);
lean_ctor_set(v___x_1590_, 3, v_options_1589_);
v___x_1591_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
lean_ctor_set(v___x_1591_, 1, v_msgData_1578_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(lean_object* v_msgData_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1599_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = lean_box(1);
v___x_1601_ = l_Lean_MessageData_ofFormat(v___x_1600_);
return v___x_1601_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2));
v___x_1606_ = l_Lean_MessageData_ofFormat(v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
return v_x_1607_;
}
else
{
lean_object* v_head_1609_; lean_object* v_tail_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1632_; 
v_head_1609_ = lean_ctor_get(v_x_1608_, 0);
v_tail_1610_ = lean_ctor_get(v_x_1608_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1612_ = v_x_1608_;
v_isShared_1613_ = v_isSharedCheck_1632_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_tail_1610_);
lean_inc(v_head_1609_);
lean_dec(v_x_1608_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1632_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_before_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1630_; 
v_before_1614_ = lean_ctor_get(v_head_1609_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_head_1609_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v_head_1609_, 1);
lean_dec(v_unused_1631_);
v___x_1616_ = v_head_1609_;
v_isShared_1617_ = v_isSharedCheck_1630_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_before_1614_);
lean_dec(v_head_1609_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1630_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 7);
lean_ctor_set(v___x_1616_, 1, v___x_1618_);
lean_ctor_set(v___x_1616_, 0, v_x_1607_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_x_1607_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 7);
lean_ctor_set(v___x_1612_, 1, v___x_1621_);
lean_ctor_set(v___x_1612_, 0, v___x_1620_);
v___x_1623_ = v___x_1612_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = l_Lean_MessageData_ofSyntax(v_before_1614_);
v___x_1625_ = l_Lean_indentD(v___x_1624_);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1623_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v_x_1607_ = v___x_1626_;
v_x_1608_ = v_tail_1610_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(lean_object* v_opts_1633_, lean_object* v_opt_1634_){
_start:
{
lean_object* v_name_1635_; lean_object* v_defValue_1636_; lean_object* v_map_1637_; lean_object* v___x_1638_; 
v_name_1635_ = lean_ctor_get(v_opt_1634_, 0);
v_defValue_1636_ = lean_ctor_get(v_opt_1634_, 1);
v_map_1637_ = lean_ctor_get(v_opts_1633_, 0);
v___x_1638_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1637_, v_name_1635_);
if (lean_obj_tag(v___x_1638_) == 0)
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_unbox(v_defValue_1636_);
return v___x_1639_;
}
else
{
lean_object* v_val_1640_; 
v_val_1640_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v___x_1638_, 1);
if (lean_obj_tag(v_val_1640_) == 1)
{
uint8_t v_v_1641_; 
v_v_1641_ = lean_ctor_get_uint8(v_val_1640_, 0);
lean_dec_ref_known(v_val_1640_, 0);
return v_v_1641_;
}
else
{
uint8_t v___x_1642_; 
lean_dec(v_val_1640_);
v___x_1642_ = lean_unbox(v_defValue_1636_);
return v___x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_1643_, lean_object* v_opt_1644_){
_start:
{
uint8_t v_res_1645_; lean_object* v_r_1646_; 
v_res_1645_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_1643_, v_opt_1644_);
lean_dec_ref(v_opt_1644_);
lean_dec_ref(v_opts_1643_);
v_r_1646_ = lean_box(v_res_1645_);
return v_r_1646_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1));
v___x_1651_ = l_Lean_MessageData_ofFormat(v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(lean_object* v_msgData_1652_, lean_object* v_macroStack_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_options_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_options_1656_ = lean_ctor_get(v___y_1654_, 2);
v___x_1657_ = l_Lean_Elab_pp_macroStack;
v___x_1658_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; 
lean_dec(v_macroStack_1653_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_msgData_1652_);
return v___x_1659_;
}
else
{
if (lean_obj_tag(v_macroStack_1653_) == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1660_, 0, v_msgData_1652_);
return v___x_1660_;
}
else
{
lean_object* v_head_1661_; lean_object* v_after_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1677_; 
v_head_1661_ = lean_ctor_get(v_macroStack_1653_, 0);
lean_inc(v_head_1661_);
v_after_1662_ = lean_ctor_get(v_head_1661_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_head_1661_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v_head_1661_, 0);
lean_dec(v_unused_1678_);
v___x_1664_ = v_head_1661_;
v_isShared_1665_ = v_isSharedCheck_1677_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_after_1662_);
lean_dec(v_head_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1677_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 7);
lean_ctor_set(v___x_1664_, 1, v___x_1666_);
lean_ctor_set(v___x_1664_, 0, v_msgData_1652_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_msgData_1652_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_msgData_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1669_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = l_Lean_MessageData_ofSyntax(v_after_1662_);
v___x_1672_ = l_Lean_indentD(v___x_1671_);
v_msgData_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1673_, 0, v___x_1670_);
lean_ctor_set(v_msgData_1673_, 1, v___x_1672_);
v___x_1674_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_1673_, v_macroStack_1653_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_1679_, lean_object* v_macroStack_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_1679_, v_macroStack_1680_, v___y_1681_);
lean_dec_ref(v___y_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_msg_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_ref_1692_; lean_object* v___x_1693_; lean_object* v_a_1694_; lean_object* v_macroStack_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_ref_1692_ = lean_ctor_get(v___y_1689_, 5);
v___x_1693_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_1684_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v_macroStack_1695_ = lean_ctor_get(v___y_1685_, 1);
v___x_1696_ = l_Lean_Elab_getBetterRef(v_ref_1692_, v_macroStack_1695_);
lean_inc(v_macroStack_1695_);
v___x_1697_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_1694_, v_macroStack_1695_, v___y_1689_);
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1696_);
lean_ctor_set(v___x_1702_, 1, v_a_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 1);
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_msg_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1715_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_box(0);
v___x_1722_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2));
v___x_1723_ = l_Lean_mkConst(v___x_1722_, v___x_1721_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6));
v___x_1729_ = l_Lean_stringToMessageData(v___x_1728_);
return v___x_1729_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9));
v___x_1734_ = l_Lean_MessageData_ofFormat(v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v___y_1735_, lean_object* v_monadInfo_1736_, uint8_t v_returnsEarly_1737_, lean_object* v___x_1738_, lean_object* v_a_1739_, uint8_t v___x_1740_, lean_object* v_e_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_defs_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___x_1773_; lean_object* v_returnVar_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1808_; lean_object* v___y_1809_; 
v___x_1773_ = lean_mk_empty_array_with_capacity(v___x_1738_);
if (lean_obj_tag(v_e_1741_) == 0)
{
if (v___x_1740_ == 0)
{
goto v___jp_1822_;
}
else
{
goto v___jp_1783_;
}
}
else
{
goto v___jp_1822_;
}
v___jp_1749_:
{
size_t v_sz_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v_sz_1757_ = lean_array_size(v___y_1735_);
v___x_1758_ = ((size_t)0ULL);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v_monadInfo_1736_, v___y_1735_, v_sz_1757_, v___x_1758_, v_defs_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1759_) == 0)
{
if (v_returnsEarly_1737_ == 0)
{
return v___x_1759_;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
v___x_1761_ = lean_array_get_size(v___y_1735_);
v___x_1762_ = lean_nat_dec_eq(v___x_1761_, v___x_1738_);
if (v___x_1762_ == 0)
{
lean_dec(v_a_1760_);
return v___x_1759_;
}
else
{
lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1771_; 
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v___x_1759_, 0);
lean_dec(v_unused_1772_);
v___x_1764_ = v___x_1759_;
v_isShared_1765_ = v_isSharedCheck_1771_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v___x_1759_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1771_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1766_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3);
v___x_1767_ = lean_array_push(v_a_1760_, v___x_1766_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1767_);
v___x_1769_ = v___x_1764_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
else
{
return v___x_1759_;
}
}
v___jp_1774_:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_array_push(v___x_1773_, v_returnVar_1775_);
v_defs_1750_ = v___x_1782_;
v___y_1751_ = v___y_1776_;
v___y_1752_ = v___y_1777_;
v___y_1753_ = v___y_1778_;
v___y_1754_ = v___y_1779_;
v___y_1755_ = v___y_1780_;
v___y_1756_ = v___y_1781_;
goto v___jp_1749_;
}
v___jp_1783_:
{
if (v_returnsEarly_1737_ == 0)
{
lean_dec(v_e_1741_);
lean_dec_ref(v_a_1739_);
v_defs_1750_ = v___x_1773_;
v___y_1751_ = v___y_1742_;
v___y_1752_ = v___y_1743_;
v___y_1753_ = v___y_1744_;
v___y_1754_ = v___y_1745_;
v___y_1755_ = v___y_1746_;
v___y_1756_ = v___y_1747_;
goto v___jp_1749_;
}
else
{
if (lean_obj_tag(v_e_1741_) == 0)
{
lean_object* v_resultType_1784_; lean_object* v___x_1785_; 
v_resultType_1784_ = lean_ctor_get(v_a_1739_, 0);
lean_inc_ref(v_resultType_1784_);
lean_dec_ref(v_a_1739_);
v___x_1785_ = l_Lean_Meta_mkNone(v_resultType_1784_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v_returnVar_1775_ = v_a_1786_;
v___y_1776_ = v___y_1742_;
v___y_1777_ = v___y_1743_;
v___y_1778_ = v___y_1744_;
v___y_1779_ = v___y_1745_;
v___y_1780_ = v___y_1746_;
v___y_1781_ = v___y_1747_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_monadInfo_1736_);
v_a_1787_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1785_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1785_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_val_1795_; lean_object* v_resultType_1796_; lean_object* v___x_1797_; 
v_val_1795_ = lean_ctor_get(v_e_1741_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v_e_1741_, 1);
v_resultType_1796_ = lean_ctor_get(v_a_1739_, 0);
lean_inc_ref(v_resultType_1796_);
lean_dec_ref(v_a_1739_);
v___x_1797_ = l_Lean_Meta_mkSome(v_resultType_1796_, v_val_1795_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1797_, 1);
v_returnVar_1775_ = v_a_1798_;
v___y_1776_ = v___y_1742_;
v___y_1777_ = v___y_1743_;
v___y_1778_ = v___y_1744_;
v___y_1779_ = v___y_1745_;
v___y_1780_ = v___y_1746_;
v___y_1781_ = v___y_1747_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_monadInfo_1736_);
v_a_1799_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1797_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
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
}
}
v___jp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_inc_ref(v___y_1808_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___y_1808_);
lean_ctor_set(v___x_1810_, 1, v___y_1809_);
v___x_1811_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___x_1812_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
v___jp_1822_:
{
if (v_returnsEarly_1737_ == 0)
{
lean_object* v___x_1823_; 
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_a_1739_);
lean_dec_ref(v_monadInfo_1736_);
v___x_1823_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7);
if (lean_obj_tag(v_e_1741_) == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10);
v___y_1808_ = v___x_1823_;
v___y_1809_ = v___x_1824_;
goto v___jp_1807_;
}
else
{
lean_object* v_val_1825_; lean_object* v___x_1826_; 
v_val_1825_ = lean_ctor_get(v_e_1741_, 0);
lean_inc(v_val_1825_);
lean_dec_ref_known(v_e_1741_, 1);
v___x_1826_ = l_Lean_MessageData_ofExpr(v_val_1825_);
v___y_1808_ = v___x_1823_;
v___y_1809_ = v___x_1826_;
goto v___jp_1807_;
}
}
else
{
goto v___jp_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v___y_1827_, lean_object* v_monadInfo_1828_, lean_object* v_returnsEarly_1829_, lean_object* v___x_1830_, lean_object* v_a_1831_, lean_object* v___x_1832_, lean_object* v_e_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_returnsEarly_boxed_1841_; uint8_t v___x_71568__boxed_1842_; lean_object* v_res_1843_; 
v_returnsEarly_boxed_1841_ = lean_unbox(v_returnsEarly_1829_);
v___x_71568__boxed_1842_ = lean_unbox(v___x_1832_);
v_res_1843_ = l_Lean_Elab_Do_elabDoFor___lam__3(v___y_1827_, v_monadInfo_1828_, v_returnsEarly_boxed_1841_, v___x_1830_, v_a_1831_, v___x_71568__boxed_1842_, v_e_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___x_1830_);
lean_dec_ref(v___y_1827_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object* v___f_1845_, lean_object* v_u_1846_, lean_object* v___x_1847_, lean_object* v___x_1848_, lean_object* v_snd_1849_, lean_object* v___x_1850_, lean_object* v_e_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_e_1851_);
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
lean_inc(v___y_1856_);
lean_inc_ref(v___y_1855_);
lean_inc(v___y_1854_);
lean_inc_ref(v___y_1853_);
v___x_1861_ = lean_apply_8(v___f_1845_, v___x_1860_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, lean_box(0));
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v___x_1863_ = l_Lean_Meta_mkProdMkN(v_a_1862_, v_u_1846_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v_fst_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v_fst_1865_ = lean_ctor_get(v_a_1864_, 0);
lean_inc(v_fst_1865_);
lean_dec(v_a_1864_);
v___x_1866_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1867_ = l_Lean_Name_mkStr2(v___x_1847_, v___x_1866_);
v___x_1868_ = l_Lean_mkConst(v___x_1867_, v___x_1848_);
v___x_1869_ = l_Lean_mkAppB(v___x_1868_, v_snd_1849_, v_fst_1865_);
v___x_1870_ = l_Lean_Elab_Do_mkPureApp(v___x_1850_, v___x_1869_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
return v___x_1870_;
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_snd_1849_);
lean_dec(v___x_1848_);
lean_dec_ref(v___x_1847_);
v_a_1871_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1863_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1863_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_snd_1849_);
lean_dec(v___x_1848_);
lean_dec_ref(v___x_1847_);
lean_dec(v_u_1846_);
v_a_1879_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1861_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1861_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object* v___f_1887_, lean_object* v_u_1888_, lean_object* v___x_1889_, lean_object* v___x_1890_, lean_object* v_snd_1891_, lean_object* v___x_1892_, lean_object* v_e_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Elab_Do_elabDoFor___lam__4(v___f_1887_, v_u_1888_, v___x_1889_, v___x_1890_, v_snd_1891_, v___x_1892_, v_e_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___f_1904_, lean_object* v___x_1905_, lean_object* v_u_1906_, lean_object* v___x_1907_, lean_object* v___x_1908_, lean_object* v_snd_1909_, lean_object* v___x_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; 
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
v___x_1919_ = lean_apply_8(v___f_1904_, v___x_1905_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, lean_box(0));
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l_Lean_Meta_mkProdMkN(v_a_1920_, v_u_1906_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v_fst_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v_fst_1923_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_fst_1923_);
lean_dec(v_a_1922_);
v___x_1924_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0));
v___x_1925_ = l_Lean_Name_mkStr2(v___x_1907_, v___x_1924_);
v___x_1926_ = l_Lean_mkConst(v___x_1925_, v___x_1908_);
v___x_1927_ = l_Lean_mkAppB(v___x_1926_, v_snd_1909_, v_fst_1923_);
v___x_1928_ = l_Lean_Elab_Do_mkPureApp(v___x_1910_, v___x_1927_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
return v___x_1928_;
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_snd_1909_);
lean_dec(v___x_1908_);
lean_dec_ref(v___x_1907_);
v_a_1929_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1921_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1921_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
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
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v___x_1910_);
lean_dec_ref(v_snd_1909_);
lean_dec(v___x_1908_);
lean_dec_ref(v___x_1907_);
lean_dec(v_u_1906_);
v_a_1937_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1919_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1919_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___f_1945_, lean_object* v___x_1946_, lean_object* v_u_1947_, lean_object* v___x_1948_, lean_object* v___x_1949_, lean_object* v_snd_1950_, lean_object* v___x_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___f_1945_, v___x_1946_, v_u_1947_, v___x_1948_, v___x_1949_, v_snd_1950_, v___x_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_1961_, lean_object* v___x_1962_, lean_object* v_u_1963_, lean_object* v___x_1964_, lean_object* v___x_1965_, lean_object* v_snd_1966_, lean_object* v___x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
lean_inc(v___y_1974_);
lean_inc_ref(v___y_1973_);
lean_inc(v___y_1972_);
lean_inc_ref(v___y_1971_);
lean_inc(v___y_1970_);
lean_inc_ref(v___y_1969_);
v___x_1976_ = lean_apply_8(v___f_1961_, v___x_1962_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, lean_box(0));
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1978_ = l_Lean_Meta_mkProdMkN(v_a_1977_, v_u_1963_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v_fst_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v_fst_1980_ = lean_ctor_get(v_a_1979_, 0);
lean_inc(v_fst_1980_);
lean_dec(v_a_1979_);
v___x_1981_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1982_ = l_Lean_Name_mkStr2(v___x_1964_, v___x_1981_);
v___x_1983_ = l_Lean_mkConst(v___x_1982_, v___x_1965_);
v___x_1984_ = l_Lean_mkAppB(v___x_1983_, v_snd_1966_, v_fst_1980_);
v___x_1985_ = l_Lean_Elab_Do_mkPureApp(v___x_1967_, v___x_1984_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_1985_;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v___x_1967_);
lean_dec_ref(v_snd_1966_);
lean_dec(v___x_1965_);
lean_dec_ref(v___x_1964_);
v_a_1986_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1978_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1978_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v___x_1967_);
lean_dec_ref(v_snd_1966_);
lean_dec(v___x_1965_);
lean_dec_ref(v___x_1964_);
lean_dec(v_u_1963_);
v_a_1994_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1976_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1976_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_2002_, lean_object* v___x_2003_, lean_object* v_u_2004_, lean_object* v___x_2005_, lean_object* v___x_2006_, lean_object* v_snd_2007_, lean_object* v___x_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_2002_, v___x_2003_, v_u_2004_, v___x_2005_, v___x_2006_, v_snd_2007_, v___x_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___x_2018_, lean_object* v___f_2019_, lean_object* v___f_2020_, lean_object* v___x_2021_, lean_object* v___x_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_monadInfo_2031_; lean_object* v_mutVars_2032_; lean_object* v_mutVarDefs_2033_; lean_object* v_contInfo_2034_; uint8_t v_deadCode_2035_; lean_object* v_ops_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
v_monadInfo_2031_ = lean_ctor_get(v___y_2023_, 0);
v_mutVars_2032_ = lean_ctor_get(v___y_2023_, 1);
v_mutVarDefs_2033_ = lean_ctor_get(v___y_2023_, 2);
v_contInfo_2034_ = lean_ctor_get(v___y_2023_, 4);
v_deadCode_2035_ = lean_ctor_get_uint8(v___y_2023_, sizeof(void*)*6);
v_ops_2036_ = lean_ctor_get(v___y_2023_, 5);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___y_2023_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v___y_2023_, 3);
lean_dec(v_unused_2045_);
v___x_2038_ = v___y_2023_;
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_ops_2036_);
lean_inc(v_contInfo_2034_);
lean_inc(v_mutVarDefs_2033_);
lean_inc(v_mutVars_2032_);
lean_inc(v_monadInfo_2031_);
lean_dec(v___y_2023_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 3, v___x_2018_);
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_monadInfo_2031_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_mutVars_2032_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_mutVarDefs_2033_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v_contInfo_2034_);
lean_ctor_set(v_reuseFailAlloc_2043_, 5, v_ops_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2043_, sizeof(void*)*6, v_deadCode_2035_);
v___x_2041_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_2019_, v___f_2020_, v___x_2021_, v___x_2022_, v___x_2041_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec_ref(v___x_2041_);
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___x_2046_, lean_object* v___f_2047_, lean_object* v___f_2048_, lean_object* v___x_2049_, lean_object* v___x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___x_2046_, v___f_2047_, v___f_2048_, v___x_2049_, v___x_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_u_2065_, lean_object* v_snd_2066_, lean_object* v___f_2067_, lean_object* v___x_2068_, lean_object* v_body_2069_, uint8_t v___x_2070_, lean_object* v___y_2071_, lean_object* v_xh_2072_, lean_object* v_loopS_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_resultType_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2119_; 
v_resultType_2082_ = lean_ctor_get(v_a_2063_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_a_2063_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v_a_2063_, 1);
lean_dec(v_unused_2120_);
v___x_2084_ = v_a_2063_;
v_isShared_2085_ = v_isSharedCheck_2119_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_resultType_2082_);
lean_dec(v_a_2063_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2119_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_resultName_2086_; lean_object* v_resultType_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2117_; 
v_resultName_2086_ = lean_ctor_get(v_a_2064_, 0);
v_resultType_2087_ = lean_ctor_get(v_a_2064_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2064_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v_a_2064_, 2);
lean_dec(v_unused_2118_);
v___x_2089_ = v_a_2064_;
v_isShared_2090_ = v_isSharedCheck_2117_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_resultType_2087_);
lean_inc(v_resultName_2086_);
lean_dec(v_a_2064_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2117_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___f_2098_; lean_object* v___f_2099_; lean_object* v___f_2100_; lean_object* v___x_2102_; 
v___x_2091_ = l_Lean_Expr_fvarId_x21(v_loopS_2073_);
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0));
v___x_2093_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1));
v___x_2094_ = lean_box(0);
lean_inc_n(v_u_2065_, 3);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_u_2065_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
lean_inc_ref_n(v___x_2095_, 3);
v___x_2096_ = l_Lean_mkConst(v___x_2093_, v___x_2095_);
lean_inc_ref_n(v_snd_2066_, 3);
v___x_2097_ = l_Lean_Expr_app___override(v___x_2096_, v_snd_2066_);
lean_inc_ref_n(v___x_2097_, 3);
lean_inc_ref_n(v___f_2067_, 2);
v___f_2098_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 15, 6);
lean_closure_set(v___f_2098_, 0, v___f_2067_);
lean_closure_set(v___f_2098_, 1, v_u_2065_);
lean_closure_set(v___f_2098_, 2, v___x_2092_);
lean_closure_set(v___f_2098_, 3, v___x_2095_);
lean_closure_set(v___f_2098_, 4, v_snd_2066_);
lean_closure_set(v___f_2098_, 5, v___x_2097_);
lean_inc(v___x_2068_);
v___f_2099_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 15, 7);
lean_closure_set(v___f_2099_, 0, v___f_2067_);
lean_closure_set(v___f_2099_, 1, v___x_2068_);
lean_closure_set(v___f_2099_, 2, v_u_2065_);
lean_closure_set(v___f_2099_, 3, v___x_2092_);
lean_closure_set(v___f_2099_, 4, v___x_2095_);
lean_closure_set(v___f_2099_, 5, v_snd_2066_);
lean_closure_set(v___f_2099_, 6, v___x_2097_);
v___f_2100_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 7);
lean_closure_set(v___f_2100_, 0, v___f_2067_);
lean_closure_set(v___f_2100_, 1, v___x_2068_);
lean_closure_set(v___f_2100_, 2, v_u_2065_);
lean_closure_set(v___f_2100_, 3, v___x_2092_);
lean_closure_set(v___f_2100_, 4, v___x_2095_);
lean_closure_set(v___f_2100_, 5, v_snd_2066_);
lean_closure_set(v___f_2100_, 6, v___x_2097_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v___f_2098_);
v___x_2102_ = v___x_2084_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_resultType_2082_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v___f_2098_);
v___x_2102_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
uint8_t v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = 1;
lean_inc_ref(v___f_2099_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 2, v___f_2099_);
v___x_2105_ = v___x_2089_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_resultName_2086_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_resultType_2087_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v___f_2099_);
v___x_2105_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; 
lean_ctor_set_uint8(v___x_2105_, sizeof(void*)*3, v___x_2103_);
v___x_2106_ = lean_box(v___x_2070_);
v___x_2107_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_2107_, 0, v_body_2069_);
lean_closure_set(v___x_2107_, 1, v___x_2105_);
lean_closure_set(v___x_2107_, 2, v___x_2106_);
v___f_2108_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 13, 5);
lean_closure_set(v___f_2108_, 0, v___x_2097_);
lean_closure_set(v___f_2108_, 1, v___f_2100_);
lean_closure_set(v___f_2108_, 2, v___f_2099_);
lean_closure_set(v___f_2108_, 3, v___x_2102_);
lean_closure_set(v___f_2108_, 4, v___x_2107_);
v___x_2109_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2071_, v___x_2091_, v___f_2108_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = lean_array_push(v_xh_2072_, v_loopS_2073_);
v___x_2112_ = 0;
v___x_2113_ = 1;
v___x_2114_ = l_Lean_Meta_mkLambdaFVars(v___x_2111_, v_a_2110_, v___x_2112_, v___x_2070_, v___x_2112_, v___x_2070_, v___x_2113_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec_ref(v___x_2111_);
return v___x_2114_;
}
else
{
lean_dec_ref(v_loopS_2073_);
lean_dec_ref(v_xh_2072_);
return v___x_2109_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object** _args){
lean_object* v_a_2121_ = _args[0];
lean_object* v_a_2122_ = _args[1];
lean_object* v_u_2123_ = _args[2];
lean_object* v_snd_2124_ = _args[3];
lean_object* v___f_2125_ = _args[4];
lean_object* v___x_2126_ = _args[5];
lean_object* v_body_2127_ = _args[6];
lean_object* v___x_2128_ = _args[7];
lean_object* v___y_2129_ = _args[8];
lean_object* v_xh_2130_ = _args[9];
lean_object* v_loopS_2131_ = _args[10];
lean_object* v___y_2132_ = _args[11];
lean_object* v___y_2133_ = _args[12];
lean_object* v___y_2134_ = _args[13];
lean_object* v___y_2135_ = _args[14];
lean_object* v___y_2136_ = _args[15];
lean_object* v___y_2137_ = _args[16];
lean_object* v___y_2138_ = _args[17];
lean_object* v___y_2139_ = _args[18];
_start:
{
uint8_t v___x_72125__boxed_2140_; lean_object* v_res_2141_; 
v___x_72125__boxed_2140_ = lean_unbox(v___x_2128_);
v_res_2141_ = l_Lean_Elab_Do_elabDoFor___lam__8(v_a_2121_, v_a_2122_, v_u_2123_, v_snd_2124_, v___f_2125_, v___x_2126_, v_body_2127_, v___x_72125__boxed_2140_, v___y_2129_, v_xh_2130_, v_loopS_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v___y_2132_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v_x_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_u_2147_, lean_object* v_snd_2148_, lean_object* v___f_2149_, lean_object* v___x_2150_, lean_object* v_body_2151_, uint8_t v___x_2152_, lean_object* v___y_2153_, lean_object* v_a_2154_, lean_object* v_h_x3f_2155_, lean_object* v___x_2156_, lean_object* v_xh_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_array_get_borrowed(v___x_2142_, v_xh_2157_, v___x_2143_);
lean_inc(v___x_2166_);
v___x_2167_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_2144_, v___x_2166_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v___x_2168_; lean_object* v___f_2169_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; 
lean_dec_ref_known(v___x_2167_, 1);
v___x_2168_ = lean_box(v___x_2152_);
lean_inc_ref(v_xh_2157_);
lean_inc_ref(v_snd_2148_);
v___f_2169_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 19, 10);
lean_closure_set(v___f_2169_, 0, v_a_2145_);
lean_closure_set(v___f_2169_, 1, v_a_2146_);
lean_closure_set(v___f_2169_, 2, v_u_2147_);
lean_closure_set(v___f_2169_, 3, v_snd_2148_);
lean_closure_set(v___f_2169_, 4, v___f_2149_);
lean_closure_set(v___f_2169_, 5, v___x_2150_);
lean_closure_set(v___f_2169_, 6, v_body_2151_);
lean_closure_set(v___f_2169_, 7, v___x_2168_);
lean_closure_set(v___f_2169_, 8, v___y_2153_);
lean_closure_set(v___f_2169_, 9, v_xh_2157_);
if (lean_obj_tag(v_h_x3f_2155_) == 1)
{
lean_object* v_val_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_val_2181_ = lean_ctor_get(v_h_x3f_2155_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v_h_x3f_2155_, 1);
v___x_2182_ = lean_array_get(v___x_2142_, v_xh_2157_, v___x_2156_);
lean_dec_ref(v_xh_2157_);
v___x_2183_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_2181_, v___x_2182_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_dec_ref_known(v___x_2183_, 1);
v___y_2171_ = v___y_2158_;
v___y_2172_ = v___y_2159_;
v___y_2173_ = v___y_2160_;
v___y_2174_ = v___y_2161_;
v___y_2175_ = v___y_2162_;
v___y_2176_ = v___y_2163_;
v___y_2177_ = v___y_2164_;
goto v___jp_2170_;
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v___f_2169_);
lean_dec(v_a_2154_);
lean_dec_ref(v_snd_2148_);
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2183_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2183_);
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
else
{
lean_dec_ref(v_xh_2157_);
lean_dec(v_h_x3f_2155_);
v___y_2171_ = v___y_2158_;
v___y_2172_ = v___y_2159_;
v___y_2173_ = v___y_2160_;
v___y_2174_ = v___y_2161_;
v___y_2175_ = v___y_2162_;
v___y_2176_ = v___y_2163_;
v___y_2177_ = v___y_2164_;
goto v___jp_2170_;
}
v___jp_2170_:
{
uint8_t v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = 0;
v___x_2179_ = 1;
v___x_2180_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_2154_, v___x_2178_, v_snd_2148_, v___f_2169_, v___x_2179_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
return v___x_2180_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref(v_xh_2157_);
lean_dec(v_h_x3f_2155_);
lean_dec(v_a_2154_);
lean_dec(v___y_2153_);
lean_dec(v_body_2151_);
lean_dec(v___x_2150_);
lean_dec_ref(v___f_2149_);
lean_dec_ref(v_snd_2148_);
lean_dec(v_u_2147_);
lean_dec_ref(v_a_2146_);
lean_dec_ref(v_a_2145_);
v_a_2192_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2167_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2167_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object** _args){
lean_object* v___x_2200_ = _args[0];
lean_object* v___x_2201_ = _args[1];
lean_object* v_x_2202_ = _args[2];
lean_object* v_a_2203_ = _args[3];
lean_object* v_a_2204_ = _args[4];
lean_object* v_u_2205_ = _args[5];
lean_object* v_snd_2206_ = _args[6];
lean_object* v___f_2207_ = _args[7];
lean_object* v___x_2208_ = _args[8];
lean_object* v_body_2209_ = _args[9];
lean_object* v___x_2210_ = _args[10];
lean_object* v___y_2211_ = _args[11];
lean_object* v_a_2212_ = _args[12];
lean_object* v_h_x3f_2213_ = _args[13];
lean_object* v___x_2214_ = _args[14];
lean_object* v_xh_2215_ = _args[15];
lean_object* v___y_2216_ = _args[16];
lean_object* v___y_2217_ = _args[17];
lean_object* v___y_2218_ = _args[18];
lean_object* v___y_2219_ = _args[19];
lean_object* v___y_2220_ = _args[20];
lean_object* v___y_2221_ = _args[21];
lean_object* v___y_2222_ = _args[22];
lean_object* v___y_2223_ = _args[23];
_start:
{
uint8_t v___x_72248__boxed_2224_; lean_object* v_res_2225_; 
v___x_72248__boxed_2224_ = lean_unbox(v___x_2210_);
v_res_2225_ = l_Lean_Elab_Do_elabDoFor___lam__9(v___x_2200_, v___x_2201_, v_x_2202_, v_a_2203_, v_a_2204_, v_u_2205_, v_snd_2206_, v___f_2207_, v___x_2208_, v_body_2209_, v___x_72248__boxed_2224_, v___y_2211_, v_a_2212_, v_h_x3f_2213_, v___x_2214_, v_xh_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___x_2214_);
lean_dec(v___x_2201_);
lean_dec_ref(v___x_2200_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(lean_object* v_name_2226_, lean_object* v_type_2227_, lean_object* v_k_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
uint8_t v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = 0;
v___x_2238_ = 0;
v___x_2239_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2226_, v___x_2237_, v_type_2227_, v_k_2228_, v___x_2238_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(lean_object* v_name_2240_, lean_object* v_type_2241_, lean_object* v_k_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_2240_, v_type_2241_, v_k_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(uint8_t v_returnsEarly_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_doBlockResultType_2272_, lean_object* v_a_2273_, lean_object* v_v_2274_, lean_object* v_u_2275_, lean_object* v___f_2276_, lean_object* v___y_2277_, lean_object* v___x_2278_, lean_object* v___x_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_ret_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; 
if (v_returnsEarly_2269_ == 0)
{
lean_object* v___x_2343_; 
lean_dec_ref(v___f_2276_);
lean_dec(v_u_2275_);
lean_dec(v_v_2274_);
lean_dec_ref(v_a_2273_);
lean_dec_ref(v_doBlockResultType_2272_);
lean_dec(v_a_2271_);
v___x_2343_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_2270_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
return v___x_2343_;
}
else
{
lean_object* v___x_2344_; 
v___x_2344_ = l_Lean_Meta_getFVarFromUserName(v_a_2271_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = lean_array_get_size(v___y_2277_);
v___x_2347_ = lean_nat_dec_eq(v___x_2346_, v___x_2278_);
if (v___x_2347_ == 0)
{
v_ret_2289_ = v_a_2345_;
v___y_2290_ = v___y_2280_;
v___y_2291_ = v___y_2281_;
v___y_2292_ = v___y_2282_;
v___y_2293_ = v___y_2283_;
v___y_2294_ = v___y_2284_;
v___y_2295_ = v___y_2285_;
v___y_2296_ = v___y_2286_;
goto v___jp_2288_;
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2348_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9));
v___x_2349_ = lean_mk_empty_array_with_capacity(v___x_2279_);
v___x_2350_ = lean_array_push(v___x_2349_, v_a_2345_);
v___x_2351_ = l_Lean_Meta_mkAppM(v___x_2348_, v___x_2350_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v_ret_2289_ = v_a_2352_;
v___y_2290_ = v___y_2280_;
v___y_2291_ = v___y_2281_;
v___y_2292_ = v___y_2282_;
v___y_2293_ = v___y_2283_;
v___y_2294_ = v___y_2284_;
v___y_2295_ = v___y_2285_;
v___y_2296_ = v___y_2286_;
goto v___jp_2288_;
}
else
{
lean_dec_ref(v___f_2276_);
lean_dec(v_u_2275_);
lean_dec(v_v_2274_);
lean_dec_ref(v_a_2273_);
lean_dec_ref(v_doBlockResultType_2272_);
lean_dec_ref(v_a_2270_);
return v___x_2351_;
}
}
}
else
{
lean_dec_ref(v___f_2276_);
lean_dec(v_u_2275_);
lean_dec(v_v_2274_);
lean_dec_ref(v_a_2273_);
lean_dec_ref(v_doBlockResultType_2272_);
lean_dec_ref(v_a_2270_);
return v___x_2344_;
}
}
v___jp_2288_:
{
lean_object* v___x_2297_; 
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
lean_inc_ref(v_ret_2289_);
v___x_2297_ = lean_infer_type(v_ret_2289_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
v___x_2299_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2272_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_2270_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_2304_ = l_Lean_Core_mkFreshUserName(v___x_2303_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v_resultType_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2333_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v_resultType_2306_ = lean_ctor_get(v_a_2273_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_a_2273_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_a_2273_, 1);
lean_dec(v_unused_2334_);
v___x_2308_ = v_a_2273_;
v_isShared_2309_ = v_isSharedCheck_2333_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_resultType_2306_);
lean_dec(v_a_2273_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2333_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2310_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2));
v___x_2311_ = 0;
v___x_2312_ = l_Lean_mkLambda(v___x_2310_, v___x_2311_, v_a_2298_, v_a_2300_);
v___x_2313_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6));
v___x_2314_ = l_Lean_Level_succ___override(v_v_2274_);
v___x_2315_ = lean_box(0);
if (v_isShared_2309_ == 0)
{
lean_ctor_set_tag(v___x_2308_, 1);
lean_ctor_set(v___x_2308_, 1, v___x_2315_);
lean_ctor_set(v___x_2308_, 0, v___x_2314_);
v___x_2317_ = v___x_2308_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2318_, 0, v_u_2275_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_mkConst(v___x_2313_, v___x_2318_);
lean_inc_ref(v_resultType_2306_);
v___x_2320_ = l_Lean_mkApp3(v___x_2319_, v_resultType_2306_, v___x_2312_, v_ret_2289_);
v___x_2321_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_a_2305_, v_resultType_2306_, v___f_2276_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2331_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2331_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2331_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2326_ = l_Lean_mkSimpleThunk(v_a_2302_);
v___x_2327_ = l_Lean_mkAppB(v___x_2320_, v_a_2322_, v___x_2326_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2327_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
else
{
lean_dec_ref(v___x_2320_);
lean_dec(v_a_2302_);
return v___x_2321_;
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_a_2302_);
lean_dec(v_a_2300_);
lean_dec(v_a_2298_);
lean_dec_ref(v_ret_2289_);
lean_dec_ref(v___f_2276_);
lean_dec(v_u_2275_);
lean_dec(v_v_2274_);
lean_dec_ref(v_a_2273_);
v_a_2335_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2304_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2304_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
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
lean_dec(v_a_2300_);
lean_dec(v_a_2298_);
lean_dec_ref(v_ret_2289_);
lean_dec_ref(v___f_2276_);
lean_dec(v_u_2275_);
lean_dec(v_v_2274_);
lean_dec_ref(v_a_2273_);
return v___x_2301_;
}
}
else
{
lean_dec(v_a_2298_);
lean_dec_ref(v_ret_2289_);
lean_dec_ref(v___f_2276_);
lean_dec(v_u_2275_);
lean_dec(v_v_2274_);
lean_dec_ref(v_a_2273_);
lean_dec_ref(v_a_2270_);
return v___x_2299_;
}
}
else
{
lean_dec_ref(v_ret_2289_);
lean_dec_ref(v___f_2276_);
lean_dec(v_u_2275_);
lean_dec(v_v_2274_);
lean_dec_ref(v_a_2273_);
lean_dec_ref(v_doBlockResultType_2272_);
lean_dec_ref(v_a_2270_);
return v___x_2297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_returnsEarly_2353_ = _args[0];
lean_object* v_a_2354_ = _args[1];
lean_object* v_a_2355_ = _args[2];
lean_object* v_doBlockResultType_2356_ = _args[3];
lean_object* v_a_2357_ = _args[4];
lean_object* v_v_2358_ = _args[5];
lean_object* v_u_2359_ = _args[6];
lean_object* v___f_2360_ = _args[7];
lean_object* v___y_2361_ = _args[8];
lean_object* v___x_2362_ = _args[9];
lean_object* v___x_2363_ = _args[10];
lean_object* v___y_2364_ = _args[11];
lean_object* v___y_2365_ = _args[12];
lean_object* v___y_2366_ = _args[13];
lean_object* v___y_2367_ = _args[14];
lean_object* v___y_2368_ = _args[15];
lean_object* v___y_2369_ = _args[16];
lean_object* v___y_2370_ = _args[17];
lean_object* v___y_2371_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_2372_; lean_object* v_res_2373_; 
v_returnsEarly_boxed_2372_ = lean_unbox(v_returnsEarly_2353_);
v_res_2373_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_returnsEarly_boxed_2372_, v_a_2354_, v_a_2355_, v_doBlockResultType_2356_, v_a_2357_, v_v_2358_, v_u_2359_, v___f_2360_, v___y_2361_, v___x_2362_, v___x_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___x_2363_);
lean_dec(v___x_2362_);
lean_dec_ref(v___y_2361_);
return v_res_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___x_2376_, uint8_t v___x_2377_, lean_object* v_postS_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = l_Lean_Expr_fvarId_x21(v_postS_2378_);
v___x_2388_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2374_, v___x_2387_, v___y_2375_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = lean_mk_empty_array_with_capacity(v___x_2376_);
v___x_2391_ = lean_array_push(v___x_2390_, v_postS_2378_);
v___x_2392_ = 0;
v___x_2393_ = 1;
v___x_2394_ = l_Lean_Meta_mkLambdaFVars(v___x_2391_, v_a_2389_, v___x_2392_, v___x_2377_, v___x_2392_, v___x_2377_, v___x_2393_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec_ref(v___x_2391_);
return v___x_2394_;
}
else
{
lean_dec_ref(v_postS_2378_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___x_2397_, lean_object* v___x_2398_, lean_object* v_postS_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
uint8_t v___x_72630__boxed_2408_; lean_object* v_res_2409_; 
v___x_72630__boxed_2408_ = lean_unbox(v___x_2398_);
v_res_2409_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___y_2395_, v___y_2396_, v___x_2397_, v___x_72630__boxed_2408_, v_postS_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___x_2397_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v___x_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_val_2420_, lean_object* v_a_2421_, lean_object* v_x_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2431_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_2432_ = lean_box(0);
v___x_2433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2415_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_a_2416_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = l_Lean_mkConst(v___x_2431_, v___x_2434_);
v___x_2436_ = l_Lean_instInhabitedExpr;
v___x_2437_ = lean_array_get_borrowed(v___x_2436_, v_x_2422_, v___x_2417_);
lean_inc(v___x_2437_);
v___x_2438_ = l_Lean_mkApp5(v___x_2435_, v_a_2418_, v_a_2419_, v_val_2420_, v_a_2421_, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v___x_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_val_2445_, lean_object* v_a_2446_, lean_object* v_x_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_2440_, v_a_2441_, v___x_2442_, v_a_2443_, v_a_2444_, v_val_2445_, v_a_2446_, v_x_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec_ref(v_x_2447_);
lean_dec(v___x_2442_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(lean_object* v_a_2457_, lean_object* v_as_2458_, size_t v_i_2459_, size_t v_stop_2460_, lean_object* v_b_2461_){
_start:
{
lean_object* v___y_2463_; uint8_t v___x_2467_; 
v___x_2467_ = lean_usize_dec_eq(v_i_2459_, v_stop_2460_);
if (v___x_2467_ == 0)
{
lean_object* v_reassigns_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v_reassigns_2468_ = lean_ctor_get(v_a_2457_, 1);
v___x_2469_ = lean_array_uget_borrowed(v_as_2458_, v_i_2459_);
v___x_2470_ = l_Lean_Elab_Do_MutVar_getId(v___x_2469_);
v___x_2471_ = l_Lean_NameSet_contains(v_reassigns_2468_, v___x_2470_);
lean_dec(v___x_2470_);
if (v___x_2471_ == 0)
{
v___y_2463_ = v_b_2461_;
goto v___jp_2462_;
}
else
{
lean_object* v___x_2472_; 
lean_inc(v___x_2469_);
v___x_2472_ = lean_array_push(v_b_2461_, v___x_2469_);
v___y_2463_ = v___x_2472_;
goto v___jp_2462_;
}
}
else
{
return v_b_2461_;
}
v___jp_2462_:
{
size_t v___x_2464_; size_t v___x_2465_; 
v___x_2464_ = ((size_t)1ULL);
v___x_2465_ = lean_usize_add(v_i_2459_, v___x_2464_);
v_i_2459_ = v___x_2465_;
v_b_2461_ = v___y_2463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object* v_a_2473_, lean_object* v_as_2474_, lean_object* v_i_2475_, lean_object* v_stop_2476_, lean_object* v_b_2477_){
_start:
{
size_t v_i_boxed_2478_; size_t v_stop_boxed_2479_; lean_object* v_res_2480_; 
v_i_boxed_2478_ = lean_unbox_usize(v_i_2475_);
lean_dec(v_i_2475_);
v_stop_boxed_2479_ = lean_unbox_usize(v_stop_2476_);
lean_dec(v_stop_2476_);
v_res_2480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_2473_, v_as_2474_, v_i_boxed_2478_, v_stop_boxed_2479_, v_b_2477_);
lean_dec_ref(v_as_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(size_t v_sz_2481_, size_t v_i_2482_, lean_object* v_bs_2483_){
_start:
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_usize_dec_lt(v_i_2482_, v_sz_2481_);
if (v___x_2484_ == 0)
{
return v_bs_2483_;
}
else
{
lean_object* v_v_2485_; lean_object* v___x_2486_; lean_object* v_bs_x27_2487_; lean_object* v___x_2488_; size_t v___x_2489_; size_t v___x_2490_; lean_object* v___x_2491_; 
v_v_2485_ = lean_array_uget(v_bs_2483_, v_i_2482_);
v___x_2486_ = lean_unsigned_to_nat(0u);
v_bs_x27_2487_ = lean_array_uset(v_bs_2483_, v_i_2482_, v___x_2486_);
v___x_2488_ = l_Lean_Elab_Do_MutVar_getId(v_v_2485_);
lean_dec(v_v_2485_);
v___x_2489_ = ((size_t)1ULL);
v___x_2490_ = lean_usize_add(v_i_2482_, v___x_2489_);
v___x_2491_ = lean_array_uset(v_bs_x27_2487_, v_i_2482_, v___x_2488_);
v_i_2482_ = v___x_2490_;
v_bs_2483_ = v___x_2491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_sz_2493_, lean_object* v_i_2494_, lean_object* v_bs_2495_){
_start:
{
size_t v_sz_boxed_2496_; size_t v_i_boxed_2497_; lean_object* v_res_2498_; 
v_sz_boxed_2496_ = lean_unbox_usize(v_sz_2493_);
lean_dec(v_sz_2493_);
v_i_boxed_2497_ = lean_unbox_usize(v_i_2494_);
lean_dec(v_i_2494_);
v_res_2498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_boxed_2496_, v_i_boxed_2497_, v_bs_2495_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(lean_object* v___x_2499_, lean_object* v_a_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_70933__overap_2510_; lean_object* v___x_2511_; 
v___x_2509_ = l_Lean_instInhabitedExpr;
v___x_70933__overap_2510_ = l_instInhabitedOfMonad___redArg(v___x_2499_, v___x_2509_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc_ref(v___y_2501_);
v___x_2511_ = lean_apply_8(v___x_70933__overap_2510_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, lean_box(0));
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(lean_object* v___x_2512_, lean_object* v_a_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(v___x_2512_, v_a_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_a_2513_);
return v_res_2522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_instMonadEIO(lean_box(0));
return v___x_2523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0);
v___x_2525_ = l_StateRefT_x27_instMonad___redArg(v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(lean_object* v_acc_2532_, lean_object* v_declInfos_2533_, lean_object* v_k_2534_, lean_object* v_kind_2535_, lean_object* v_x_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v_kind_boxed_2545_; lean_object* v_res_2546_; 
v_kind_boxed_2545_ = lean_unbox(v_kind_2535_);
v_res_2546_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(v_acc_2532_, v_declInfos_2533_, v_k_2534_, v_kind_boxed_2545_, v_x_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object* v_declInfos_2547_, lean_object* v_k_2548_, uint8_t v_kind_2549_, lean_object* v_acc_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v_toApplicative_2560_; lean_object* v_toFunctor_2561_; lean_object* v_toSeq_2562_; lean_object* v_toSeqLeft_2563_; lean_object* v_toSeqRight_2564_; lean_object* v___f_2565_; lean_object* v___f_2566_; lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___x_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v_toApplicative_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2656_; 
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1);
v_toApplicative_2560_ = lean_ctor_get(v___x_2559_, 0);
v_toFunctor_2561_ = lean_ctor_get(v_toApplicative_2560_, 0);
v_toSeq_2562_ = lean_ctor_get(v_toApplicative_2560_, 2);
v_toSeqLeft_2563_ = lean_ctor_get(v_toApplicative_2560_, 3);
v_toSeqRight_2564_ = lean_ctor_get(v_toApplicative_2560_, 4);
v___f_2565_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2));
v___f_2566_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3));
lean_inc_ref_n(v_toFunctor_2561_, 2);
v___f_2567_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2567_, 0, v_toFunctor_2561_);
v___f_2568_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2568_, 0, v_toFunctor_2561_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___f_2567_);
lean_ctor_set(v___x_2569_, 1, v___f_2568_);
lean_inc(v_toSeqRight_2564_);
v___f_2570_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2570_, 0, v_toSeqRight_2564_);
lean_inc(v_toSeqLeft_2563_);
v___f_2571_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2571_, 0, v_toSeqLeft_2563_);
lean_inc(v_toSeq_2562_);
v___f_2572_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2572_, 0, v_toSeq_2562_);
v___x_2573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2569_);
lean_ctor_set(v___x_2573_, 1, v___f_2565_);
lean_ctor_set(v___x_2573_, 2, v___f_2572_);
lean_ctor_set(v___x_2573_, 3, v___f_2571_);
lean_ctor_set(v___x_2573_, 4, v___f_2570_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v___f_2566_);
v___x_2575_ = l_StateRefT_x27_instMonad___redArg(v___x_2574_);
v_toApplicative_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v___x_2575_, 1);
lean_dec(v_unused_2657_);
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2656_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_toApplicative_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2656_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v_toFunctor_2580_; lean_object* v_toSeq_2581_; lean_object* v_toSeqLeft_2582_; lean_object* v_toSeqRight_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2654_; 
v_toFunctor_2580_ = lean_ctor_get(v_toApplicative_2576_, 0);
v_toSeq_2581_ = lean_ctor_get(v_toApplicative_2576_, 2);
v_toSeqLeft_2582_ = lean_ctor_get(v_toApplicative_2576_, 3);
v_toSeqRight_2583_ = lean_ctor_get(v_toApplicative_2576_, 4);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_toApplicative_2576_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_toApplicative_2576_, 1);
lean_dec(v_unused_2655_);
v___x_2585_ = v_toApplicative_2576_;
v_isShared_2586_ = v_isSharedCheck_2654_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_toSeqRight_2583_);
lean_inc(v_toSeqLeft_2582_);
lean_inc(v_toSeq_2581_);
lean_inc(v_toFunctor_2580_);
lean_dec(v_toApplicative_2576_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2654_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___f_2587_; lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; lean_object* v___f_2592_; lean_object* v___f_2593_; lean_object* v___f_2594_; lean_object* v___x_2596_; 
v___f_2587_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4));
v___f_2588_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5));
lean_inc_ref(v_toFunctor_2580_);
v___f_2589_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2589_, 0, v_toFunctor_2580_);
v___f_2590_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2590_, 0, v_toFunctor_2580_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___f_2589_);
lean_ctor_set(v___x_2591_, 1, v___f_2590_);
v___f_2592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2592_, 0, v_toSeqRight_2583_);
v___f_2593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2593_, 0, v_toSeqLeft_2582_);
v___f_2594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2594_, 0, v_toSeq_2581_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 4, v___f_2592_);
lean_ctor_set(v___x_2585_, 3, v___f_2593_);
lean_ctor_set(v___x_2585_, 2, v___f_2594_);
lean_ctor_set(v___x_2585_, 1, v___f_2587_);
lean_ctor_set(v___x_2585_, 0, v___x_2591_);
v___x_2596_ = v___x_2585_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___f_2587_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v___f_2594_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v___f_2593_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v___f_2592_);
v___x_2596_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2598_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 1, v___f_2588_);
lean_ctor_set(v___x_2578_, 0, v___x_2596_);
v___x_2598_ = v___x_2578_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___f_2588_);
v___x_2598_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; lean_object* v_toApplicative_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2650_; 
v___x_2599_ = l_StateRefT_x27_instMonad___redArg(v___x_2598_);
v_toApplicative_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v___x_2599_, 1);
lean_dec(v_unused_2651_);
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2650_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_toApplicative_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2650_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_toFunctor_2604_; lean_object* v_toSeq_2605_; lean_object* v_toSeqLeft_2606_; lean_object* v_toSeqRight_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2648_; 
v_toFunctor_2604_ = lean_ctor_get(v_toApplicative_2600_, 0);
v_toSeq_2605_ = lean_ctor_get(v_toApplicative_2600_, 2);
v_toSeqLeft_2606_ = lean_ctor_get(v_toApplicative_2600_, 3);
v_toSeqRight_2607_ = lean_ctor_get(v_toApplicative_2600_, 4);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_toApplicative_2600_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v_toApplicative_2600_, 1);
lean_dec(v_unused_2649_);
v___x_2609_ = v_toApplicative_2600_;
v_isShared_2610_ = v_isSharedCheck_2648_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_toSeqRight_2607_);
lean_inc(v_toSeqLeft_2606_);
lean_inc(v_toSeq_2605_);
lean_inc(v_toFunctor_2604_);
lean_dec(v_toApplicative_2600_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2648_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___f_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v___f_2614_; lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___f_2618_; lean_object* v___x_2620_; 
v___f_2611_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6));
v___f_2612_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7));
lean_inc_ref(v_toFunctor_2604_);
v___f_2613_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2613_, 0, v_toFunctor_2604_);
v___f_2614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2614_, 0, v_toFunctor_2604_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___f_2613_);
lean_ctor_set(v___x_2615_, 1, v___f_2614_);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toSeqRight_2607_);
v___f_2617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2617_, 0, v_toSeqLeft_2606_);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toSeq_2605_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 4, v___f_2616_);
lean_ctor_set(v___x_2609_, 3, v___f_2617_);
lean_ctor_set(v___x_2609_, 2, v___f_2618_);
lean_ctor_set(v___x_2609_, 1, v___f_2611_);
lean_ctor_set(v___x_2609_, 0, v___x_2615_);
v___x_2620_ = v___x_2609_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v___f_2611_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v___f_2618_);
lean_ctor_set(v_reuseFailAlloc_2647_, 3, v___f_2617_);
lean_ctor_set(v_reuseFailAlloc_2647_, 4, v___f_2616_);
v___x_2620_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 1, v___f_2612_);
lean_ctor_set(v___x_2602_, 0, v___x_2620_);
v___x_2622_ = v___x_2602_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___f_2612_);
v___x_2622_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2623_ = l_ReaderT_instMonad___redArg(v___x_2622_);
v___x_2624_ = lean_array_get_size(v_acc_2550_);
v___x_2625_ = lean_array_get_size(v_declInfos_2547_);
v___x_2626_ = lean_nat_dec_lt(v___x_2624_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref(v___x_2623_);
lean_dec_ref(v_declInfos_2547_);
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
lean_inc_ref(v___y_2551_);
v___x_2627_ = lean_apply_9(v_k_2548_, v_acc_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, lean_box(0));
return v___x_2627_;
}
else
{
lean_object* v___f_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_snd_2636_; lean_object* v_fst_2637_; lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v___x_2640_; 
v___f_2628_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2628_, 0, v___x_2623_);
v___x_2629_ = lean_box(0);
v___x_2630_ = 0;
v___f_2631_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2631_, 0, v___f_2628_);
v___x_2632_ = lean_box(v___x_2630_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___f_2631_);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2629_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = lean_array_get(v___x_2634_, v_declInfos_2547_, v___x_2624_);
lean_dec_ref_known(v___x_2634_, 2);
v_snd_2636_ = lean_ctor_get(v___x_2635_, 1);
lean_inc(v_snd_2636_);
v_fst_2637_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_fst_2637_);
lean_dec(v___x_2635_);
v_fst_2638_ = lean_ctor_get(v_snd_2636_, 0);
lean_inc(v_fst_2638_);
v_snd_2639_ = lean_ctor_get(v_snd_2636_, 1);
lean_inc(v_snd_2639_);
lean_dec(v_snd_2636_);
lean_inc(v___y_2557_);
lean_inc_ref(v___y_2556_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
lean_inc_ref(v___y_2551_);
lean_inc_ref(v_acc_2550_);
v___x_2640_ = lean_apply_9(v_snd_2639_, v_acc_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, lean_box(0));
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___f_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = lean_box(v_kind_2549_);
v___f_2643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2643_, 0, v_acc_2550_);
lean_closure_set(v___f_2643_, 1, v_declInfos_2547_);
lean_closure_set(v___f_2643_, 2, v_k_2548_);
lean_closure_set(v___f_2643_, 3, v___x_2642_);
v___x_2644_ = lean_unbox(v_fst_2638_);
lean_dec(v_fst_2638_);
v___x_2645_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_2637_, v___x_2644_, v_a_2641_, v___f_2643_, v_kind_2549_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2645_;
}
else
{
lean_dec(v_fst_2638_);
lean_dec(v_fst_2637_);
lean_dec_ref(v_acc_2550_);
lean_dec_ref(v_k_2548_);
lean_dec_ref(v_declInfos_2547_);
return v___x_2640_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(lean_object* v_acc_2658_, lean_object* v_declInfos_2659_, lean_object* v_k_2660_, uint8_t v_kind_2661_, lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_array_push(v_acc_2658_, v_x_2662_);
v___x_2672_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2659_, v_k_2660_, v_kind_2661_, v___x_2671_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object* v_declInfos_2673_, lean_object* v_k_2674_, lean_object* v_kind_2675_, lean_object* v_acc_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v_kind_boxed_2685_; lean_object* v_res_2686_; 
v_kind_boxed_2685_ = lean_unbox(v_kind_2675_);
v_res_2686_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2673_, v_k_2674_, v_kind_boxed_2685_, v_acc_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v___y_2677_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object* v_declInfos_2689_, lean_object* v_k_2690_, uint8_t v_kind_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0));
v___x_2701_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2689_, v_k_2690_, v_kind_2691_, v___x_2700_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object* v_declInfos_2702_, lean_object* v_k_2703_, lean_object* v_kind_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
uint8_t v_kind_boxed_2713_; lean_object* v_res_2714_; 
v_kind_boxed_2713_ = lean_unbox(v_kind_2704_);
v_res_2714_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_declInfos_2702_, v_k_2703_, v_kind_boxed_2713_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec_ref(v___y_2705_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t v_sz_2715_, size_t v_i_2716_, lean_object* v_bs_2717_){
_start:
{
uint8_t v___x_2718_; 
v___x_2718_ = lean_usize_dec_lt(v_i_2716_, v_sz_2715_);
if (v___x_2718_ == 0)
{
return v_bs_2717_;
}
else
{
lean_object* v_v_2719_; lean_object* v_fst_2720_; lean_object* v_snd_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2737_; 
v_v_2719_ = lean_array_uget(v_bs_2717_, v_i_2716_);
v_fst_2720_ = lean_ctor_get(v_v_2719_, 0);
v_snd_2721_ = lean_ctor_get(v_v_2719_, 1);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_v_2719_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2723_ = v_v_2719_;
v_isShared_2724_ = v_isSharedCheck_2737_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_snd_2721_);
lean_inc(v_fst_2720_);
lean_dec(v_v_2719_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2737_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v_bs_x27_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2725_ = lean_unsigned_to_nat(0u);
v_bs_x27_2726_ = lean_array_uset(v_bs_2717_, v_i_2716_, v___x_2725_);
v___x_2727_ = 0;
v___x_2728_ = lean_box(v___x_2727_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2728_);
v___x_2730_ = v___x_2723_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_snd_2721_);
v___x_2730_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v_fst_2720_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2716_, v___x_2732_);
v___x_2734_ = lean_array_uset(v_bs_x27_2726_, v_i_2716_, v___x_2731_);
v_i_2716_ = v___x_2733_;
v_bs_2717_ = v___x_2734_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_sz_2738_, lean_object* v_i_2739_, lean_object* v_bs_2740_){
_start:
{
size_t v_sz_boxed_2741_; size_t v_i_boxed_2742_; lean_object* v_res_2743_; 
v_sz_boxed_2741_ = lean_unbox_usize(v_sz_2738_);
lean_dec(v_sz_2738_);
v_i_boxed_2742_ = lean_unbox_usize(v_i_2739_);
lean_dec(v_i_2739_);
v_res_2743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_2741_, v_i_boxed_2742_, v_bs_2740_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_2744_, lean_object* v_k_2745_, uint8_t v_kind_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
size_t v_sz_2755_; size_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_sz_2755_ = lean_array_size(v_declInfos_2744_);
v___x_2756_ = ((size_t)0ULL);
v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_2755_, v___x_2756_, v_declInfos_2744_);
v___x_2758_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v___x_2757_, v_k_2745_, v_kind_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_2759_, lean_object* v_k_2760_, lean_object* v_kind_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
uint8_t v_kind_boxed_2770_; lean_object* v_res_2771_; 
v_kind_boxed_2770_ = lean_unbox(v_kind_2761_);
v_res_2771_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_2759_, v_k_2760_, v_kind_boxed_2770_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec_ref(v___y_2762_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_2802_, lean_object* v_dec_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2812_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_2802_);
v___x_2813_ = l_Lean_Syntax_isOfKind(v_stx_2802_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
lean_dec_ref(v_dec_2803_);
lean_dec(v_stx_2802_);
v___x_2814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2815_ = lean_unsigned_to_nat(1u);
v___x_2816_ = l_Lean_Syntax_getArg(v_stx_2802_, v___x_2815_);
lean_inc(v___x_2816_);
v___x_2817_ = l_Lean_Syntax_matchesNull(v___x_2816_, v___x_2815_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec(v___x_2816_);
lean_dec_ref(v_dec_2803_);
lean_dec(v_stx_2802_);
v___x_2818_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___y_2824_; lean_object* v___y_2825_; uint8_t v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; uint8_t v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v_fst_2890_; lean_object* v_snd_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; uint8_t v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; uint8_t v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; uint8_t v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; uint8_t v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; 
v___x_2819_ = lean_unsigned_to_nat(0u);
v___x_2820_ = l_Lean_Syntax_getArg(v___x_2816_, v___x_2819_);
lean_dec(v___x_2816_);
v___x_2821_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_2820_);
v___x_2822_ = l_Lean_Syntax_isOfKind(v___x_2820_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_3090_; 
lean_dec(v___x_2820_);
lean_dec_ref(v_dec_2803_);
lean_dec(v_stx_2802_);
v___x_3090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3090_;
}
else
{
lean_object* v_tk_3091_; lean_object* v_h_x3f_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v_tk_3091_ = l_Lean_Syntax_getArg(v_stx_2802_, v___x_2819_);
v___x_3225_ = l_Lean_Syntax_getArg(v___x_2820_, v___x_2819_);
v___x_3226_ = l_Lean_Syntax_isNone(v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3227_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3225_);
v___x_3228_ = l_Lean_Syntax_matchesNull(v___x_3225_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; 
lean_dec(v___x_3225_);
lean_dec(v_tk_3091_);
lean_dec(v___x_2820_);
lean_dec_ref(v_dec_2803_);
lean_dec(v_stx_2802_);
v___x_3229_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3229_;
}
else
{
lean_object* v_h_x3f_3230_; lean_object* v___x_3231_; 
v_h_x3f_3230_ = l_Lean_Syntax_getArg(v___x_3225_, v___x_2819_);
lean_dec(v___x_3225_);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_h_x3f_3230_);
v_h_x3f_3093_ = v___x_3231_;
v___y_3094_ = v_a_2804_;
v___y_3095_ = v_a_2805_;
v___y_3096_ = v_a_2806_;
v___y_3097_ = v_a_2807_;
v___y_3098_ = v_a_2808_;
v___y_3099_ = v_a_2809_;
v___y_3100_ = v_a_2810_;
goto v___jp_3092_;
}
}
else
{
lean_object* v___x_3232_; 
lean_dec(v___x_3225_);
v___x_3232_ = lean_box(0);
v_h_x3f_3093_ = v___x_3232_;
v___y_3094_ = v_a_2804_;
v___y_3095_ = v_a_2805_;
v___y_3096_ = v_a_2806_;
v___y_3097_ = v_a_2807_;
v___y_3098_ = v_a_2808_;
v___y_3099_ = v_a_2809_;
v___y_3100_ = v_a_2810_;
goto v___jp_3092_;
}
v___jp_3092_:
{
lean_object* v_x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; 
v_x_3101_ = l_Lean_Syntax_getArg(v___x_2820_, v___x_2815_);
v___x_3102_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
lean_inc(v_x_3101_);
v___x_3103_ = l_Lean_Syntax_isOfKind(v_x_3101_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; 
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
lean_dec(v_tk_3091_);
lean_dec(v___x_2820_);
lean_dec_ref(v_dec_2803_);
lean_dec(v_stx_2802_);
v___x_3104_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3104_;
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_2803_, v_tk_3091_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v_tk_3091_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3107_ = lean_mk_empty_array_with_capacity(v___x_2815_);
lean_inc(v_x_3101_);
v___x_3108_ = lean_array_push(v___x_3107_, v_x_3101_);
v___x_3109_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_3108_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec_ref(v___x_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3110_; 
lean_dec_ref_known(v___x_3109_, 1);
v___x_3110_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3112_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3112_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; uint8_t v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
lean_inc(v_a_3111_);
v___x_3114_ = l_Lean_Level_succ___override(v_a_3111_);
v___x_3115_ = l_Lean_mkSort(v___x_3114_);
v___x_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
v___x_3117_ = 0;
v___x_3118_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__12));
v___x_3119_ = l_Lean_Meta_mkFreshExprMVar(v___x_3116_, v___x_3117_, v___x_3118_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3192_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3122_ = v___x_3119_;
v_isShared_3123_ = v_isSharedCheck_3192_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3119_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3192_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3127_; 
lean_inc(v_a_3113_);
v___x_3124_ = l_Lean_Level_succ___override(v_a_3113_);
v___x_3125_ = l_Lean_mkSort(v___x_3124_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 1);
lean_ctor_set(v___x_3122_, 0, v___x_3125_);
v___x_3127_ = v___x_3122_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__14));
v___x_3129_ = l_Lean_Meta_mkFreshExprMVar(v___x_3127_, v___x_3117_, v___x_3128_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3190_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3190_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3190_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3134_ = lean_unsigned_to_nat(3u);
v___x_3135_ = l_Lean_Syntax_getArg(v___x_2820_, v___x_3134_);
lean_dec(v___x_2820_);
lean_inc(v_a_3130_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set_tag(v___x_3132_, 1);
v___x_3137_ = v___x_3132_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3130_);
v___x_3137_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_box(0);
v___x_3139_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_3135_, v___x_3137_, v___x_2822_, v___x_2822_, v___x_3138_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v_body_3141_; lean_object* v___x_3142_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v_body_3141_ = l_Lean_Syntax_getArg(v_stx_2802_, v___x_3134_);
lean_dec(v_stx_2802_);
lean_inc(v_body_3141_);
v___x_3142_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_3141_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_3094_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__16));
v___x_3147_ = l_Lean_Core_mkFreshUserName(v___x_3146_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v_monadInfo_3149_; lean_object* v_mutVars_3150_; lean_object* v___f_3151_; lean_object* v___f_3152_; lean_object* v___x_3153_; lean_object* v___f_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
v_monadInfo_3149_ = lean_ctor_get(v___y_3094_, 0);
v_mutVars_3150_ = lean_ctor_get(v___y_3094_, 1);
lean_inc(v_a_3120_);
v___f_3151_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3151_, 0, v_a_3120_);
lean_inc_ref(v___f_3151_);
lean_inc(v_x_3101_);
v___f_3152_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 5, 3);
lean_closure_set(v___f_3152_, 0, v_x_3101_);
lean_closure_set(v___f_3152_, 1, v___f_3151_);
lean_closure_set(v___f_3152_, 2, v___x_2815_);
v___x_3153_ = lean_box(v___x_2822_);
lean_inc(v_a_3145_);
v___f_3154_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 12, 3);
lean_closure_set(v___f_3154_, 0, v_a_3145_);
lean_closure_set(v___f_3154_, 1, v___x_2815_);
lean_closure_set(v___f_3154_, 2, v___x_3153_);
v___x_3155_ = lean_array_get_size(v_mutVars_3150_);
v___x_3156_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__17));
v___x_3157_ = lean_nat_dec_lt(v___x_2819_, v___x_3155_);
if (v___x_3157_ == 0)
{
lean_inc(v_h_x3f_3093_);
lean_inc(v_a_3120_);
lean_inc(v_a_3113_);
lean_inc(v_a_3130_);
lean_inc(v_x_3101_);
lean_inc(v_a_3140_);
lean_inc(v_a_3148_);
lean_inc(v_a_3111_);
v___y_3043_ = v_a_3111_;
v___y_3044_ = v_a_3148_;
v___y_3045_ = v_a_3140_;
v___y_3046_ = v___f_3154_;
v___y_3047_ = v_a_3106_;
v___y_3048_ = v___f_3151_;
v___y_3049_ = v___f_3152_;
v___y_3050_ = v_monadInfo_3149_;
v___y_3051_ = v_a_3145_;
v___y_3052_ = v_x_3101_;
v___y_3053_ = v_a_3130_;
v___y_3054_ = v_a_3113_;
v___y_3055_ = v_body_3141_;
v___y_3056_ = v___x_3103_;
v___y_3057_ = v_a_3120_;
v___y_3058_ = v_h_x3f_3093_;
v___y_3059_ = v_a_3148_;
v___y_3060_ = v_a_3111_;
v___y_3061_ = v_a_3140_;
v___y_3062_ = v___y_3099_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v_a_3143_;
v___y_3065_ = v___y_3098_;
v___y_3066_ = v___y_3096_;
v___y_3067_ = v_x_3101_;
v___y_3068_ = v___y_3094_;
v___y_3069_ = v_a_3130_;
v___y_3070_ = v___y_3095_;
v___y_3071_ = v___x_3117_;
v___y_3072_ = v_a_3113_;
v___y_3073_ = v___y_3100_;
v___y_3074_ = v_a_3120_;
v___y_3075_ = v_h_x3f_3093_;
v___y_3076_ = v___x_3156_;
goto v___jp_3042_;
}
else
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_nat_dec_le(v___x_3155_, v___x_3155_);
if (v___x_3158_ == 0)
{
if (v___x_3157_ == 0)
{
lean_inc(v_h_x3f_3093_);
lean_inc(v_a_3120_);
lean_inc(v_a_3113_);
lean_inc(v_a_3130_);
lean_inc(v_x_3101_);
lean_inc(v_a_3140_);
lean_inc(v_a_3148_);
lean_inc(v_a_3111_);
v___y_3043_ = v_a_3111_;
v___y_3044_ = v_a_3148_;
v___y_3045_ = v_a_3140_;
v___y_3046_ = v___f_3154_;
v___y_3047_ = v_a_3106_;
v___y_3048_ = v___f_3151_;
v___y_3049_ = v___f_3152_;
v___y_3050_ = v_monadInfo_3149_;
v___y_3051_ = v_a_3145_;
v___y_3052_ = v_x_3101_;
v___y_3053_ = v_a_3130_;
v___y_3054_ = v_a_3113_;
v___y_3055_ = v_body_3141_;
v___y_3056_ = v___x_3103_;
v___y_3057_ = v_a_3120_;
v___y_3058_ = v_h_x3f_3093_;
v___y_3059_ = v_a_3148_;
v___y_3060_ = v_a_3111_;
v___y_3061_ = v_a_3140_;
v___y_3062_ = v___y_3099_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v_a_3143_;
v___y_3065_ = v___y_3098_;
v___y_3066_ = v___y_3096_;
v___y_3067_ = v_x_3101_;
v___y_3068_ = v___y_3094_;
v___y_3069_ = v_a_3130_;
v___y_3070_ = v___y_3095_;
v___y_3071_ = v___x_3117_;
v___y_3072_ = v_a_3113_;
v___y_3073_ = v___y_3100_;
v___y_3074_ = v_a_3120_;
v___y_3075_ = v_h_x3f_3093_;
v___y_3076_ = v___x_3156_;
goto v___jp_3042_;
}
else
{
size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = lean_usize_of_nat(v___x_3155_);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_3143_, v_mutVars_3150_, v___x_3159_, v___x_3160_, v___x_3156_);
lean_inc(v_h_x3f_3093_);
lean_inc(v_a_3120_);
lean_inc(v_a_3113_);
lean_inc(v_a_3130_);
lean_inc(v_x_3101_);
lean_inc(v_a_3140_);
lean_inc(v_a_3148_);
lean_inc(v_a_3111_);
v___y_3043_ = v_a_3111_;
v___y_3044_ = v_a_3148_;
v___y_3045_ = v_a_3140_;
v___y_3046_ = v___f_3154_;
v___y_3047_ = v_a_3106_;
v___y_3048_ = v___f_3151_;
v___y_3049_ = v___f_3152_;
v___y_3050_ = v_monadInfo_3149_;
v___y_3051_ = v_a_3145_;
v___y_3052_ = v_x_3101_;
v___y_3053_ = v_a_3130_;
v___y_3054_ = v_a_3113_;
v___y_3055_ = v_body_3141_;
v___y_3056_ = v___x_3103_;
v___y_3057_ = v_a_3120_;
v___y_3058_ = v_h_x3f_3093_;
v___y_3059_ = v_a_3148_;
v___y_3060_ = v_a_3111_;
v___y_3061_ = v_a_3140_;
v___y_3062_ = v___y_3099_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v_a_3143_;
v___y_3065_ = v___y_3098_;
v___y_3066_ = v___y_3096_;
v___y_3067_ = v_x_3101_;
v___y_3068_ = v___y_3094_;
v___y_3069_ = v_a_3130_;
v___y_3070_ = v___y_3095_;
v___y_3071_ = v___x_3117_;
v___y_3072_ = v_a_3113_;
v___y_3073_ = v___y_3100_;
v___y_3074_ = v_a_3120_;
v___y_3075_ = v_h_x3f_3093_;
v___y_3076_ = v___x_3161_;
goto v___jp_3042_;
}
}
else
{
size_t v___x_3162_; size_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3162_ = ((size_t)0ULL);
v___x_3163_ = lean_usize_of_nat(v___x_3155_);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_3143_, v_mutVars_3150_, v___x_3162_, v___x_3163_, v___x_3156_);
lean_inc(v_h_x3f_3093_);
lean_inc(v_a_3120_);
lean_inc(v_a_3113_);
lean_inc(v_a_3130_);
lean_inc(v_x_3101_);
lean_inc(v_a_3140_);
lean_inc(v_a_3148_);
lean_inc(v_a_3111_);
v___y_3043_ = v_a_3111_;
v___y_3044_ = v_a_3148_;
v___y_3045_ = v_a_3140_;
v___y_3046_ = v___f_3154_;
v___y_3047_ = v_a_3106_;
v___y_3048_ = v___f_3151_;
v___y_3049_ = v___f_3152_;
v___y_3050_ = v_monadInfo_3149_;
v___y_3051_ = v_a_3145_;
v___y_3052_ = v_x_3101_;
v___y_3053_ = v_a_3130_;
v___y_3054_ = v_a_3113_;
v___y_3055_ = v_body_3141_;
v___y_3056_ = v___x_3103_;
v___y_3057_ = v_a_3120_;
v___y_3058_ = v_h_x3f_3093_;
v___y_3059_ = v_a_3148_;
v___y_3060_ = v_a_3111_;
v___y_3061_ = v_a_3140_;
v___y_3062_ = v___y_3099_;
v___y_3063_ = v___y_3097_;
v___y_3064_ = v_a_3143_;
v___y_3065_ = v___y_3098_;
v___y_3066_ = v___y_3096_;
v___y_3067_ = v_x_3101_;
v___y_3068_ = v___y_3094_;
v___y_3069_ = v_a_3130_;
v___y_3070_ = v___y_3095_;
v___y_3071_ = v___x_3117_;
v___y_3072_ = v_a_3113_;
v___y_3073_ = v___y_3100_;
v___y_3074_ = v_a_3120_;
v___y_3075_ = v_h_x3f_3093_;
v___y_3076_ = v___x_3164_;
goto v___jp_3042_;
}
}
}
else
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3172_; 
lean_dec(v_a_3145_);
lean_dec(v_a_3143_);
lean_dec(v_body_3141_);
lean_dec(v_a_3140_);
lean_dec(v_a_3130_);
lean_dec(v_a_3120_);
lean_dec(v_a_3113_);
lean_dec(v_a_3111_);
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
v_a_3165_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3167_ = v___x_3147_;
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3147_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3172_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3170_; 
if (v_isShared_3168_ == 0)
{
v___x_3170_ = v___x_3167_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_a_3165_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec(v_a_3143_);
lean_dec(v_body_3141_);
lean_dec(v_a_3140_);
lean_dec(v_a_3130_);
lean_dec(v_a_3120_);
lean_dec(v_a_3113_);
lean_dec(v_a_3111_);
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
v_a_3173_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3144_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3144_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_body_3141_);
lean_dec(v_a_3140_);
lean_dec(v_a_3130_);
lean_dec(v_a_3120_);
lean_dec(v_a_3113_);
lean_dec(v_a_3111_);
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
v_a_3181_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3142_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3142_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_dec(v_a_3130_);
lean_dec(v_a_3120_);
lean_dec(v_a_3113_);
lean_dec(v_a_3111_);
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
lean_dec(v_stx_2802_);
return v___x_3139_;
}
}
}
}
else
{
lean_dec(v_a_3120_);
lean_dec(v_a_3113_);
lean_dec(v_a_3111_);
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
lean_dec(v___x_2820_);
lean_dec(v_stx_2802_);
return v___x_3129_;
}
}
}
}
else
{
lean_dec(v_a_3113_);
lean_dec(v_a_3111_);
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
lean_dec(v___x_2820_);
lean_dec(v_stx_2802_);
return v___x_3119_;
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3111_);
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
lean_dec(v___x_2820_);
lean_dec(v_stx_2802_);
v_a_3193_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3112_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3112_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
lean_dec(v___x_2820_);
lean_dec(v_stx_2802_);
v_a_3201_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3110_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3110_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec(v_a_3106_);
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
lean_dec(v___x_2820_);
lean_dec(v_stx_2802_);
v_a_3209_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3109_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3109_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v_x_3101_);
lean_dec(v_h_x3f_3093_);
lean_dec(v___x_2820_);
lean_dec(v_stx_2802_);
v_a_3217_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3105_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3105_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
}
}
v___jp_2823_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___f_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; 
v___x_2850_ = l_Lean_instInhabitedExpr;
v___x_2851_ = lean_box(v___x_2822_);
lean_inc(v___y_2828_);
lean_inc(v___y_2835_);
lean_inc(v___y_2829_);
lean_inc_ref(v___y_2827_);
lean_inc_ref(v___y_2832_);
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 24, 15);
lean_closure_set(v___f_2852_, 0, v___x_2850_);
lean_closure_set(v___f_2852_, 1, v___x_2819_);
lean_closure_set(v___f_2852_, 2, v___y_2831_);
lean_closure_set(v___f_2852_, 3, v___y_2832_);
lean_closure_set(v___f_2852_, 4, v___y_2827_);
lean_closure_set(v___f_2852_, 5, v___y_2829_);
lean_closure_set(v___f_2852_, 6, v___y_2833_);
lean_closure_set(v___f_2852_, 7, v___y_2834_);
lean_closure_set(v___f_2852_, 8, v___y_2838_);
lean_closure_set(v___f_2852_, 9, v___y_2837_);
lean_closure_set(v___f_2852_, 10, v___x_2851_);
lean_closure_set(v___f_2852_, 11, v___y_2835_);
lean_closure_set(v___f_2852_, 12, v___y_2828_);
lean_closure_set(v___f_2852_, 13, v___y_2839_);
lean_closure_set(v___f_2852_, 14, v___x_2815_);
v___x_2853_ = 0;
v___x_2854_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_2849_, v___f_2852_, v___x_2853_, v___y_2840_, v___y_2846_, v___y_2844_, v___y_2847_, v___y_2848_, v___y_2843_, v___y_2841_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v_doBlockResultType_2856_; lean_object* v___x_2857_; lean_object* v___y_2858_; lean_object* v___x_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v_doBlockResultType_2856_ = lean_ctor_get(v___y_2840_, 3);
v___x_2857_ = lean_box(v___y_2826_);
lean_inc(v___y_2836_);
lean_inc_ref(v_doBlockResultType_2856_);
v___y_2858_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 11);
lean_closure_set(v___y_2858_, 0, v___x_2857_);
lean_closure_set(v___y_2858_, 1, v___y_2827_);
lean_closure_set(v___y_2858_, 2, v___y_2824_);
lean_closure_set(v___y_2858_, 3, v_doBlockResultType_2856_);
lean_closure_set(v___y_2858_, 4, v___y_2832_);
lean_closure_set(v___y_2858_, 5, v___y_2836_);
lean_closure_set(v___y_2858_, 6, v___y_2829_);
lean_closure_set(v___y_2858_, 7, v___y_2825_);
lean_closure_set(v___y_2858_, 8, v___y_2830_);
lean_closure_set(v___y_2858_, 9, v___x_2819_);
lean_closure_set(v___y_2858_, 10, v___x_2815_);
v___x_2859_ = lean_box(v___x_2822_);
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 13, 4);
lean_closure_set(v___f_2860_, 0, v___y_2835_);
lean_closure_set(v___f_2860_, 1, v___y_2858_);
lean_closure_set(v___f_2860_, 2, v___x_2815_);
lean_closure_set(v___f_2860_, 3, v___x_2859_);
lean_inc_ref(v___y_2842_);
v___x_2861_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v___y_2828_, v___y_2842_, v___f_2860_, v___y_2840_, v___y_2846_, v___y_2844_, v___y_2847_, v___y_2848_, v___y_2843_, v___y_2841_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = l_Lean_Expr_app___override(v___y_2845_, v_a_2855_);
lean_inc_ref(v_doBlockResultType_2856_);
v___x_2864_ = l_Lean_Elab_Do_mkBindApp(v___y_2842_, v_doBlockResultType_2856_, v___x_2863_, v_a_2862_, v___y_2840_, v___y_2846_, v___y_2844_, v___y_2847_, v___y_2848_, v___y_2843_, v___y_2841_);
return v___x_2864_;
}
else
{
lean_dec(v_a_2855_);
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2842_);
return v___x_2861_;
}
}
else
{
lean_dec_ref(v___y_2845_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2832_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
return v___x_2854_;
}
}
v___jp_2865_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_2900_ = l_Lean_Core_mkFreshUserName(v___x_2899_, v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2900_) == 0)
{
if (lean_obj_tag(v___y_2889_) == 1)
{
if (lean_obj_tag(v_snd_2891_) == 1)
{
lean_object* v_a_2901_; lean_object* v_val_2902_; lean_object* v_val_2903_; lean_object* v___f_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
lean_dec_ref(v___y_2887_);
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v_val_2902_ = lean_ctor_get(v___y_2889_, 0);
lean_inc(v_val_2902_);
lean_dec_ref_known(v___y_2889_, 1);
v_val_2903_ = lean_ctor_get(v_snd_2891_, 0);
lean_inc(v_val_2903_);
lean_dec_ref_known(v_snd_2891_, 1);
v___f_2904_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_2904_, 0, v___y_2880_);
lean_closure_set(v___f_2904_, 1, v___y_2866_);
lean_closure_set(v___f_2904_, 2, v___x_2819_);
lean_closure_set(v___f_2904_, 3, v___y_2883_);
lean_closure_set(v___f_2904_, 4, v___y_2876_);
lean_closure_set(v___f_2904_, 5, v_val_2903_);
lean_closure_set(v___f_2904_, 6, v___y_2868_);
v___x_2905_ = l_Lean_TSyntax_getId(v___y_2888_);
lean_dec(v___y_2888_);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v___y_2886_);
v___x_2907_ = l_Lean_TSyntax_getId(v_val_2902_);
lean_dec(v_val_2902_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v___f_2904_);
v___x_2909_ = lean_unsigned_to_nat(2u);
v___x_2910_ = lean_mk_empty_array_with_capacity(v___x_2909_);
v___x_2911_ = lean_array_push(v___x_2910_, v___x_2906_);
v___x_2912_ = lean_array_push(v___x_2911_, v___x_2908_);
lean_inc_ref(v___y_2877_);
v___y_2824_ = v___y_2867_;
v___y_2825_ = v___y_2869_;
v___y_2826_ = v___y_2870_;
v___y_2827_ = v___y_2871_;
v___y_2828_ = v_a_2901_;
v___y_2829_ = v___y_2872_;
v___y_2830_ = v___y_2873_;
v___y_2831_ = v___y_2874_;
v___y_2832_ = v___y_2875_;
v___y_2833_ = v___y_2877_;
v___y_2834_ = v___y_2878_;
v___y_2835_ = v___y_2879_;
v___y_2836_ = v___y_2881_;
v___y_2837_ = v___y_2882_;
v___y_2838_ = v___y_2884_;
v___y_2839_ = v___y_2885_;
v___y_2840_ = v___y_2892_;
v___y_2841_ = v___y_2898_;
v___y_2842_ = v___y_2877_;
v___y_2843_ = v___y_2897_;
v___y_2844_ = v___y_2894_;
v___y_2845_ = v_fst_2890_;
v___y_2846_ = v___y_2893_;
v___y_2847_ = v___y_2895_;
v___y_2848_ = v___y_2896_;
v___y_2849_ = v___x_2912_;
goto v___jp_2823_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2914_; 
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2866_);
v_a_2913_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2914_ = lean_apply_2(v___y_2887_, v___y_2889_, v_snd_2891_);
lean_inc_ref(v___y_2877_);
v___y_2824_ = v___y_2867_;
v___y_2825_ = v___y_2869_;
v___y_2826_ = v___y_2870_;
v___y_2827_ = v___y_2871_;
v___y_2828_ = v_a_2913_;
v___y_2829_ = v___y_2872_;
v___y_2830_ = v___y_2873_;
v___y_2831_ = v___y_2874_;
v___y_2832_ = v___y_2875_;
v___y_2833_ = v___y_2877_;
v___y_2834_ = v___y_2878_;
v___y_2835_ = v___y_2879_;
v___y_2836_ = v___y_2881_;
v___y_2837_ = v___y_2882_;
v___y_2838_ = v___y_2884_;
v___y_2839_ = v___y_2885_;
v___y_2840_ = v___y_2892_;
v___y_2841_ = v___y_2898_;
v___y_2842_ = v___y_2877_;
v___y_2843_ = v___y_2897_;
v___y_2844_ = v___y_2894_;
v___y_2845_ = v_fst_2890_;
v___y_2846_ = v___y_2893_;
v___y_2847_ = v___y_2895_;
v___y_2848_ = v___y_2896_;
v___y_2849_ = v___x_2914_;
goto v___jp_2823_;
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2916_; 
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2866_);
v_a_2915_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2916_ = lean_apply_2(v___y_2887_, v___y_2889_, v_snd_2891_);
lean_inc_ref(v___y_2877_);
v___y_2824_ = v___y_2867_;
v___y_2825_ = v___y_2869_;
v___y_2826_ = v___y_2870_;
v___y_2827_ = v___y_2871_;
v___y_2828_ = v_a_2915_;
v___y_2829_ = v___y_2872_;
v___y_2830_ = v___y_2873_;
v___y_2831_ = v___y_2874_;
v___y_2832_ = v___y_2875_;
v___y_2833_ = v___y_2877_;
v___y_2834_ = v___y_2878_;
v___y_2835_ = v___y_2879_;
v___y_2836_ = v___y_2881_;
v___y_2837_ = v___y_2882_;
v___y_2838_ = v___y_2884_;
v___y_2839_ = v___y_2885_;
v___y_2840_ = v___y_2892_;
v___y_2841_ = v___y_2898_;
v___y_2842_ = v___y_2877_;
v___y_2843_ = v___y_2897_;
v___y_2844_ = v___y_2894_;
v___y_2845_ = v_fst_2890_;
v___y_2846_ = v___y_2893_;
v___y_2847_ = v___y_2895_;
v___y_2848_ = v___y_2896_;
v___y_2849_ = v___x_2916_;
goto v___jp_2823_;
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v_snd_2891_);
lean_dec_ref(v_fst_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v___y_2866_);
v_a_2917_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2900_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2900_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
v___jp_2925_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_box(0);
lean_inc_ref(v___y_2936_);
lean_inc(v___y_2956_);
lean_inc_ref(v___y_2944_);
lean_inc(v___y_2946_);
lean_inc_ref(v___y_2945_);
lean_inc(v___y_2947_);
lean_inc_ref(v___y_2953_);
v___x_2961_ = lean_apply_8(v___y_2936_, v___x_2960_, v___y_2953_, v___y_2947_, v___y_2945_, v___y_2946_, v___y_2944_, v___y_2956_, lean_box(0));
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v_m_2963_; lean_object* v_u_2964_; lean_object* v_v_2965_; lean_object* v___x_2966_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v_m_2963_ = lean_ctor_get(v___y_2948_, 0);
v_u_2964_ = lean_ctor_get(v___y_2948_, 1);
v_v_2965_ = lean_ctor_get(v___y_2948_, 2);
lean_inc(v_u_2964_);
v___x_2966_ = l_Lean_Meta_mkProdMkN(v_a_2962_, v_u_2964_, v___y_2945_, v___y_2946_, v___y_2944_, v___y_2956_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
if (lean_obj_tag(v___y_2958_) == 0)
{
lean_object* v_fst_2968_; lean_object* v_snd_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2988_; 
v_fst_2968_ = lean_ctor_get(v_a_2967_, 0);
v_snd_2969_ = lean_ctor_get(v_a_2967_, 1);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_a_2967_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2971_ = v_a_2967_;
v_isShared_2972_ = v_isSharedCheck_2988_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_snd_2969_);
lean_inc(v_fst_2968_);
lean_dec(v_a_2967_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2988_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2973_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__1));
v___x_2974_ = lean_box(0);
lean_inc(v_v_2965_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set_tag(v___x_2971_, 1);
lean_ctor_set(v___x_2971_, 1, v___x_2974_);
lean_ctor_set(v___x_2971_, 0, v_v_2965_);
v___x_2976_ = v___x_2971_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_v_2965_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_inc(v_u_2964_);
v___x_2977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2977_, 0, v_u_2964_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___y_2941_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___y_2955_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
lean_inc_ref(v___x_2979_);
v___x_2980_ = l_Lean_mkConst(v___x_2973_, v___x_2979_);
lean_inc_ref(v___y_2957_);
lean_inc_ref(v___y_2952_);
lean_inc_ref(v_m_2963_);
v___x_2981_ = l_Lean_mkApp3(v___x_2980_, v_m_2963_, v___y_2952_, v___y_2957_);
v___x_2982_ = l_Lean_Elab_Term_mkInstMVar(v___x_2981_, v___x_2960_, v___y_2953_, v___y_2947_, v___y_2945_, v___y_2946_, v___y_2944_, v___y_2956_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_2985_ = l_Lean_mkConst(v___x_2984_, v___x_2979_);
lean_inc(v_snd_2969_);
lean_inc_ref(v_m_2963_);
v___x_2986_ = l_Lean_mkApp7(v___x_2985_, v_m_2963_, v___y_2952_, v___y_2957_, v_a_2983_, v_snd_2969_, v___y_2942_, v_fst_2968_);
lean_inc(v_u_2964_);
v___y_2866_ = v___y_2926_;
v___y_2867_ = v___y_2927_;
v___y_2868_ = v___y_2928_;
v___y_2869_ = v___y_2929_;
v___y_2870_ = v___y_2930_;
v___y_2871_ = v___y_2931_;
v___y_2872_ = v_u_2964_;
v___y_2873_ = v___y_2932_;
v___y_2874_ = v___y_2933_;
v___y_2875_ = v___y_2934_;
v___y_2876_ = v___y_2935_;
v___y_2877_ = v_snd_2969_;
v___y_2878_ = v___y_2936_;
v___y_2879_ = v___y_2959_;
v___y_2880_ = v___y_2937_;
v___y_2881_ = v_v_2965_;
v___y_2882_ = v___y_2938_;
v___y_2883_ = v___y_2939_;
v___y_2884_ = v___x_2960_;
v___y_2885_ = v___y_2940_;
v___y_2886_ = v___y_2943_;
v___y_2887_ = v___y_2949_;
v___y_2888_ = v___y_2950_;
v___y_2889_ = v___y_2958_;
v_fst_2890_ = v___x_2986_;
v_snd_2891_ = v___x_2960_;
v___y_2892_ = v___y_2951_;
v___y_2893_ = v___y_2953_;
v___y_2894_ = v___y_2947_;
v___y_2895_ = v___y_2945_;
v___y_2896_ = v___y_2946_;
v___y_2897_ = v___y_2944_;
v___y_2898_ = v___y_2956_;
goto v___jp_2865_;
}
else
{
lean_dec_ref_known(v___x_2979_, 2);
lean_dec(v_snd_2969_);
lean_dec(v_fst_2968_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
return v___x_2982_;
}
}
}
}
else
{
lean_object* v_fst_2989_; lean_object* v_snd_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3025_; 
v_fst_2989_ = lean_ctor_get(v_a_2967_, 0);
v_snd_2990_ = lean_ctor_get(v_a_2967_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_a_2967_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_2992_ = v_a_2967_;
v_isShared_2993_ = v_isSharedCheck_3025_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_snd_2990_);
lean_inc(v_fst_2989_);
lean_dec(v_a_2967_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3025_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2994_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__4));
v___x_2995_ = lean_box(0);
lean_inc(v___y_2955_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set_tag(v___x_2992_, 1);
lean_ctor_set(v___x_2992_, 1, v___x_2995_);
lean_ctor_set(v___x_2992_, 0, v___y_2955_);
v___x_2997_ = v___x_2992_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___y_2955_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_3024_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_inc(v___y_2941_);
v___x_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___y_2941_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = l_Lean_mkConst(v___x_2994_, v___x_2998_);
lean_inc_ref(v___y_2952_);
lean_inc_ref(v___y_2957_);
v___x_3000_ = l_Lean_mkAppB(v___x_2999_, v___y_2957_, v___y_2952_);
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
v___x_3002_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
v___x_3003_ = l_Lean_Meta_mkFreshExprMVar(v___x_3001_, v___y_2954_, v___x_3002_, v___y_2945_, v___y_2946_, v___y_2944_, v___y_2956_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc_n(v_a_3004_, 2);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
lean_inc(v_v_2965_);
v___x_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_v_2965_);
lean_ctor_set(v___x_3006_, 1, v___x_2995_);
lean_inc(v_u_2964_);
v___x_3007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3007_, 0, v_u_2964_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___y_2941_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___y_2955_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
lean_inc_ref(v___x_3009_);
v___x_3010_ = l_Lean_mkConst(v___x_3005_, v___x_3009_);
lean_inc_ref(v___y_2957_);
lean_inc_ref(v___y_2952_);
lean_inc_ref(v_m_2963_);
v___x_3011_ = l_Lean_mkApp4(v___x_3010_, v_m_2963_, v___y_2952_, v___y_2957_, v_a_3004_);
v___x_3012_ = l_Lean_Elab_Term_mkInstMVar(v___x_3011_, v___x_2960_, v___y_2953_, v___y_2947_, v___y_2945_, v___y_2946_, v___y_2944_, v___y_2956_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3023_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3023_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3023_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3017_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_3018_ = l_Lean_mkConst(v___x_3017_, v___x_3009_);
lean_inc(v_snd_2990_);
lean_inc(v_a_3004_);
lean_inc_ref(v_m_2963_);
v___x_3019_ = l_Lean_mkApp8(v___x_3018_, v_m_2963_, v___y_2952_, v___y_2957_, v_a_3004_, v_a_3013_, v_snd_2990_, v___y_2942_, v_fst_2989_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set_tag(v___x_3015_, 1);
lean_ctor_set(v___x_3015_, 0, v_a_3004_);
v___x_3021_ = v___x_3015_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3004_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_inc(v_u_2964_);
v___y_2866_ = v___y_2926_;
v___y_2867_ = v___y_2927_;
v___y_2868_ = v___y_2928_;
v___y_2869_ = v___y_2929_;
v___y_2870_ = v___y_2930_;
v___y_2871_ = v___y_2931_;
v___y_2872_ = v_u_2964_;
v___y_2873_ = v___y_2932_;
v___y_2874_ = v___y_2933_;
v___y_2875_ = v___y_2934_;
v___y_2876_ = v___y_2935_;
v___y_2877_ = v_snd_2990_;
v___y_2878_ = v___y_2936_;
v___y_2879_ = v___y_2959_;
v___y_2880_ = v___y_2937_;
v___y_2881_ = v_v_2965_;
v___y_2882_ = v___y_2938_;
v___y_2883_ = v___y_2939_;
v___y_2884_ = v___x_2960_;
v___y_2885_ = v___y_2940_;
v___y_2886_ = v___y_2943_;
v___y_2887_ = v___y_2949_;
v___y_2888_ = v___y_2950_;
v___y_2889_ = v___y_2958_;
v_fst_2890_ = v___x_3019_;
v_snd_2891_ = v___x_3021_;
v___y_2892_ = v___y_2951_;
v___y_2893_ = v___y_2953_;
v___y_2894_ = v___y_2947_;
v___y_2895_ = v___y_2945_;
v___y_2896_ = v___y_2946_;
v___y_2897_ = v___y_2944_;
v___y_2898_ = v___y_2956_;
goto v___jp_2865_;
}
}
}
else
{
lean_dec_ref_known(v___x_3009_, 2);
lean_dec(v_a_3004_);
lean_dec(v_snd_2990_);
lean_dec(v_fst_2989_);
lean_dec_ref_known(v___y_2958_, 1);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
return v___x_3012_;
}
}
else
{
lean_dec(v_snd_2990_);
lean_dec_ref_known(v___y_2958_, 1);
lean_dec(v_fst_2989_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
return v___x_3003_;
}
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
v_a_3026_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2966_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2966_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
v_a_3034_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_2961_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_2961_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
v___jp_3042_:
{
uint8_t v_returnsEarly_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___f_3080_; 
v_returnsEarly_3077_ = lean_ctor_get_uint8(v___y_3064_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_3064_);
v___x_3078_ = lean_box(v_returnsEarly_3077_);
v___x_3079_ = lean_box(v___y_3056_);
lean_inc_ref(v___y_3051_);
lean_inc_ref(v___y_3050_);
lean_inc_ref(v___y_3076_);
v___f_3080_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 14, 6);
lean_closure_set(v___f_3080_, 0, v___y_3076_);
lean_closure_set(v___f_3080_, 1, v___y_3050_);
lean_closure_set(v___f_3080_, 2, v___x_3078_);
lean_closure_set(v___f_3080_, 3, v___x_2819_);
lean_closure_set(v___f_3080_, 4, v___y_3051_);
lean_closure_set(v___f_3080_, 5, v___x_3079_);
if (v_returnsEarly_3077_ == 0)
{
size_t v_sz_3081_; size_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
lean_dec(v___y_3059_);
v_sz_3081_ = lean_array_size(v___y_3076_);
v___x_3082_ = ((size_t)0ULL);
lean_inc_ref(v___y_3076_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_3081_, v___x_3082_, v___y_3076_);
v___x_3084_ = lean_array_to_list(v___x_3083_);
v___y_2926_ = v___y_3043_;
v___y_2927_ = v___y_3044_;
v___y_2928_ = v___y_3045_;
v___y_2929_ = v___y_3046_;
v___y_2930_ = v_returnsEarly_3077_;
v___y_2931_ = v___y_3047_;
v___y_2932_ = v___y_3076_;
v___y_2933_ = v___y_3052_;
v___y_2934_ = v___y_3051_;
v___y_2935_ = v___y_3053_;
v___y_2936_ = v___f_3080_;
v___y_2937_ = v___y_3054_;
v___y_2938_ = v___y_3055_;
v___y_2939_ = v___y_3057_;
v___y_2940_ = v___y_3058_;
v___y_2941_ = v___y_3060_;
v___y_2942_ = v___y_3061_;
v___y_2943_ = v___y_3048_;
v___y_2944_ = v___y_3062_;
v___y_2945_ = v___y_3063_;
v___y_2946_ = v___y_3065_;
v___y_2947_ = v___y_3066_;
v___y_2948_ = v___y_3050_;
v___y_2949_ = v___y_3049_;
v___y_2950_ = v___y_3067_;
v___y_2951_ = v___y_3068_;
v___y_2952_ = v___y_3069_;
v___y_2953_ = v___y_3070_;
v___y_2954_ = v___y_3071_;
v___y_2955_ = v___y_3072_;
v___y_2956_ = v___y_3073_;
v___y_2957_ = v___y_3074_;
v___y_2958_ = v___y_3075_;
v___y_2959_ = v___x_3084_;
goto v___jp_2925_;
}
else
{
size_t v_sz_3085_; size_t v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v_sz_3085_ = lean_array_size(v___y_3076_);
v___x_3086_ = ((size_t)0ULL);
lean_inc_ref(v___y_3076_);
v___x_3087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_3085_, v___x_3086_, v___y_3076_);
v___x_3088_ = lean_array_to_list(v___x_3087_);
v___x_3089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___y_3059_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___y_2926_ = v___y_3043_;
v___y_2927_ = v___y_3044_;
v___y_2928_ = v___y_3045_;
v___y_2929_ = v___y_3046_;
v___y_2930_ = v_returnsEarly_3077_;
v___y_2931_ = v___y_3047_;
v___y_2932_ = v___y_3076_;
v___y_2933_ = v___y_3052_;
v___y_2934_ = v___y_3051_;
v___y_2935_ = v___y_3053_;
v___y_2936_ = v___f_3080_;
v___y_2937_ = v___y_3054_;
v___y_2938_ = v___y_3055_;
v___y_2939_ = v___y_3057_;
v___y_2940_ = v___y_3058_;
v___y_2941_ = v___y_3060_;
v___y_2942_ = v___y_3061_;
v___y_2943_ = v___y_3048_;
v___y_2944_ = v___y_3062_;
v___y_2945_ = v___y_3063_;
v___y_2946_ = v___y_3065_;
v___y_2947_ = v___y_3066_;
v___y_2948_ = v___y_3050_;
v___y_2949_ = v___y_3049_;
v___y_2950_ = v___y_3067_;
v___y_2951_ = v___y_3068_;
v___y_2952_ = v___y_3069_;
v___y_2953_ = v___y_3070_;
v___y_2954_ = v___y_3071_;
v___y_2955_ = v___y_3072_;
v___y_2956_ = v___y_3073_;
v___y_2957_ = v___y_3074_;
v___y_2958_ = v___y_3075_;
v___y_2959_ = v___x_3089_;
goto v___jp_2925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_3233_, lean_object* v_dec_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_Elab_Do_elabDoFor(v_stx_3233_, v_dec_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
lean_dec(v_a_3241_);
lean_dec_ref(v_a_3240_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec_ref(v_a_3235_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_3244_, lean_object* v_msg_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_3254_, lean_object* v_msg_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_3254_, v_msg_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object* v_00_u03b1_3264_, lean_object* v_name_3265_, lean_object* v_type_3266_, lean_object* v_k_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_3265_, v_type_3266_, v_k_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_00_u03b1_3277_, lean_object* v_name_3278_, lean_object* v_type_3279_, lean_object* v_k_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(v_00_u03b1_3277_, v_name_3278_, v_type_3279_, v_k_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec_ref(v___y_3281_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object* v_msgData_3290_, lean_object* v_macroStack_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_3290_, v_macroStack_3291_, v___y_3296_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object* v_msgData_3300_, lean_object* v_macroStack_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_3300_, v_macroStack_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3317_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_3318_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_3320_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_3321_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3317_, v___x_3318_, v___x_3319_, v___x_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_3323_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ProdN(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Lean_Meta_ProdN(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_For(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_For(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_For(builtin);
}
#ifdef __cplusplus
}
#endif
