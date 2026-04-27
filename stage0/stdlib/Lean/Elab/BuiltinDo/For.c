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
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
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
lean_dec_ref(v___x_402_);
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
lean_dec_ref(v___x_217_);
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
lean_dec_ref(v___x_236_);
lean_dec(v___x_232_);
lean_dec_ref(v___x_229_);
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
lean_dec_ref(v___x_505_);
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
lean_dec_ref(v___x_529_);
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
lean_dec_ref(v___x_546_);
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
lean_dec_ref(v_a_480_);
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
lean_dec_ref(v___y_479_);
v_a_492_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v_a_480_);
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
lean_dec_ref(v___x_722_);
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
v___y_664_ = v_h_x3f_713_;
v___y_665_ = v___x_717_;
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
lean_dec_ref(v___x_764_);
v___y_663_ = v_doElems_718_;
v___y_664_ = v_h_x3f_713_;
v___y_665_ = v___x_717_;
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
v___y_664_ = v_h_x3f_713_;
v___y_665_ = v___x_717_;
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
lean_inc_ref_n(v___y_639_, 3);
v___x_641_ = l_Array_append___redArg(v___y_639_, v___y_640_);
lean_dec_ref(v___y_640_);
lean_inc_n(v___y_638_, 4);
lean_inc_n(v___y_634_, 10);
v___x_642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_642_, 0, v___y_634_);
lean_ctor_set(v___x_642_, 1, v___y_638_);
lean_ctor_set(v___x_642_, 2, v___x_641_);
v___x_643_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_644_, 0, v___y_634_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = l_Lean_Syntax_node4(v___y_634_, v___x_628_, v___x_642_, v___y_633_, v___x_644_, v___y_637_);
v___x_646_ = l_Lean_Syntax_node1(v___y_634_, v___y_638_, v___x_645_);
v___x_647_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_648_, 0, v___y_634_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
lean_inc_ref(v___x_648_);
v___x_649_ = l_Lean_Syntax_node4(v___y_634_, v___x_620_, v___y_630_, v___x_646_, v___x_648_, v___y_636_);
v___x_650_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_650_, 0, v___y_634_);
lean_ctor_set(v___x_650_, 1, v___y_638_);
lean_ctor_set(v___x_650_, 2, v___y_639_);
lean_inc(v___y_635_);
v___x_651_ = l_Lean_Syntax_node2(v___y_634_, v___y_635_, v___x_649_, v___x_650_);
v___x_652_ = lean_array_push(v___y_631_, v___x_651_);
v___x_653_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_654_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_655_ = l_Array_append___redArg(v___y_639_, v___x_652_);
lean_dec_ref(v___x_652_);
v___x_656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_656_, 0, v___y_634_);
lean_ctor_set(v___x_656_, 1, v___y_638_);
lean_ctor_set(v___x_656_, 2, v___x_655_);
v___x_657_ = l_Lean_Syntax_node1(v___y_634_, v___x_654_, v___x_656_);
v___x_658_ = l_Lean_Syntax_node2(v___y_634_, v___x_653_, v___x_648_, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___y_632_);
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
lean_dec_ref(v___x_673_);
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
if (lean_obj_tag(v___y_664_) == 1)
{
lean_object* v_val_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_val_690_ = lean_ctor_get(v___y_664_, 0);
lean_inc(v_val_690_);
lean_dec_ref(v___y_664_);
v___x_691_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_682_);
v___x_692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_682_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Array_mkArray2___redArg(v_val_690_, v___x_692_);
v___y_630_ = v___x_687_;
v___y_631_ = v_fst_676_;
v___y_632_ = v_a_675_;
v___y_633_ = v_x_666_;
v___y_634_ = v___x_682_;
v___y_635_ = v___x_683_;
v___y_636_ = v_snd_677_;
v___y_637_ = v___y_665_;
v___y_638_ = v___x_688_;
v___y_639_ = v___x_689_;
v___y_640_ = v___x_693_;
goto v___jp_629_;
}
else
{
lean_object* v___x_694_; 
lean_dec(v___y_664_);
v___x_694_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_630_ = v___x_687_;
v___y_631_ = v_fst_676_;
v___y_632_ = v_a_675_;
v___y_633_ = v_x_666_;
v___y_634_ = v___x_682_;
v___y_635_ = v___x_683_;
v___y_636_ = v_snd_677_;
v___y_637_ = v___y_665_;
v___y_638_ = v___x_688_;
v___y_639_ = v___x_689_;
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
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_849_; lean_object* v___y_850_; uint8_t v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v_x_854_; lean_object* v_body_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_895_; uint8_t v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v_h_x3f_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; uint8_t v___x_1017_; 
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
lean_dec_ref(v___x_1080_);
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
v___y_1021_ = v___x_1075_;
v___y_1022_ = v_h_x3f_1071_;
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
lean_dec_ref(v___x_1122_);
v___y_1021_ = v___x_1075_;
v___y_1022_ = v_h_x3f_1071_;
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
v___y_1021_ = v___x_1075_;
v___y_1022_ = v_h_x3f_1071_;
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
lean_dec_ref(v___x_1031_);
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
if (lean_obj_tag(v___y_1022_) == 1)
{
lean_object* v_val_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_val_1048_ = lean_ctor_get(v___y_1022_, 0);
lean_inc(v_val_1048_);
lean_dec_ref(v___y_1022_);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1040_);
v___x_1050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1040_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l_Array_mkArray2___redArg(v_val_1048_, v___x_1050_);
v___y_987_ = v_fst_1034_;
v___y_988_ = v___x_1047_;
v___y_989_ = v___x_1040_;
v___y_990_ = v_a_1033_;
v___y_991_ = v___x_1045_;
v___y_992_ = v___x_1041_;
v___y_993_ = v_snd_1035_;
v___y_994_ = v___y_1021_;
v___y_995_ = v___x_1046_;
v___y_996_ = v_x_1024_;
v___y_997_ = v___x_1051_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1052_; 
lean_dec(v___y_1022_);
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_987_ = v_fst_1034_;
v___y_988_ = v___x_1047_;
v___y_989_ = v___x_1040_;
v___y_990_ = v_a_1033_;
v___y_991_ = v___x_1045_;
v___y_992_ = v___x_1041_;
v___y_993_ = v_snd_1035_;
v___y_994_ = v___y_1021_;
v___y_995_ = v___x_1046_;
v___y_996_ = v_x_1024_;
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
lean_dec_ref(v___x_1208_);
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
v___y_1149_ = v_doElems_1204_;
v___y_1150_ = v_h_x3f_1199_;
v___y_1151_ = v___x_1203_;
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
lean_dec_ref(v___x_1250_);
v___y_1149_ = v_doElems_1204_;
v___y_1150_ = v_h_x3f_1199_;
v___y_1151_ = v___x_1203_;
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
v___y_1149_ = v_doElems_1204_;
v___y_1150_ = v_h_x3f_1199_;
v___y_1151_ = v___x_1203_;
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
lean_inc_ref(v___y_1149_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___y_1149_);
lean_ctor_set(v___x_1158_, 1, v_body_1153_);
v___x_1159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1145_, v___x_1157_, v___x_1158_, v___y_1154_, v___y_1155_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v_a_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1182_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
v_a_1161_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_a_1161_);
lean_dec_ref(v___x_1159_);
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
lean_dec_ref(v___y_1150_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1168_);
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1168_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Array_mkArray2___redArg(v_val_1176_, v___x_1178_);
v___y_787_ = v_fst_1162_;
v___y_788_ = v___x_1169_;
v___y_789_ = v_snd_1163_;
v___y_790_ = v_x_1152_;
v___y_791_ = v___x_1168_;
v___y_792_ = v___x_1174_;
v___y_793_ = v___y_1151_;
v___y_794_ = v___x_1173_;
v___y_795_ = v_a_1161_;
v___y_796_ = v___x_1175_;
v___y_797_ = v___x_1179_;
goto v___jp_786_;
}
else
{
lean_object* v___x_1180_; 
lean_dec(v___y_1150_);
v___x_1180_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_787_ = v_fst_1162_;
v___y_788_ = v___x_1169_;
v___y_789_ = v_snd_1163_;
v___y_790_ = v_x_1152_;
v___y_791_ = v___x_1168_;
v___y_792_ = v___x_1174_;
v___y_793_ = v___y_1151_;
v___y_794_ = v___x_1173_;
v___y_795_ = v_a_1161_;
v___y_796_ = v___x_1175_;
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
lean_dec(v___y_1151_);
lean_dec(v___y_1150_);
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
lean_inc_ref_n(v___y_796_, 3);
v___x_798_ = l_Array_append___redArg(v___y_796_, v___y_797_);
lean_dec_ref(v___y_797_);
lean_inc_n(v___y_792_, 4);
lean_inc_n(v___y_791_, 10);
v___x_799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_799_, 0, v___y_791_);
lean_ctor_set(v___x_799_, 1, v___y_792_);
lean_ctor_set(v___x_799_, 2, v___x_798_);
v___x_800_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_801_, 0, v___y_791_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = l_Lean_Syntax_node4(v___y_791_, v___x_785_, v___x_799_, v___y_790_, v___x_801_, v___y_793_);
v___x_803_ = l_Lean_Syntax_node1(v___y_791_, v___y_792_, v___x_802_);
v___x_804_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v___y_791_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
lean_inc_ref(v___x_805_);
v___x_806_ = l_Lean_Syntax_node4(v___y_791_, v___x_620_, v___y_794_, v___x_803_, v___x_805_, v___y_789_);
v___x_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_807_, 0, v___y_791_);
lean_ctor_set(v___x_807_, 1, v___y_792_);
lean_ctor_set(v___x_807_, 2, v___y_796_);
lean_inc(v___y_788_);
v___x_808_ = l_Lean_Syntax_node2(v___y_791_, v___y_788_, v___x_806_, v___x_807_);
v___x_809_ = lean_array_push(v___y_787_, v___x_808_);
v___x_810_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_811_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_812_ = l_Array_append___redArg(v___y_796_, v___x_809_);
lean_dec_ref(v___x_809_);
v___x_813_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_813_, 0, v___y_791_);
lean_ctor_set(v___x_813_, 1, v___y_792_);
lean_ctor_set(v___x_813_, 2, v___x_812_);
v___x_814_ = l_Lean_Syntax_node1(v___y_791_, v___x_811_, v___x_813_);
v___x_815_ = l_Lean_Syntax_node2(v___y_791_, v___x_810_, v___x_805_, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___y_795_);
return v___x_816_;
}
v___jp_817_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_inc_ref_n(v___y_822_, 3);
v___x_829_ = l_Array_append___redArg(v___y_822_, v___y_828_);
lean_dec_ref(v___y_828_);
lean_inc_n(v___y_827_, 4);
lean_inc_n(v___y_819_, 10);
v___x_830_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_830_, 0, v___y_819_);
lean_ctor_set(v___x_830_, 1, v___y_827_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
v___x_831_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_832_, 0, v___y_819_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_Syntax_node4(v___y_819_, v___x_785_, v___x_830_, v___y_824_, v___x_832_, v___y_821_);
v___x_834_ = l_Lean_Syntax_node1(v___y_819_, v___y_827_, v___x_833_);
v___x_835_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_819_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
lean_inc_ref(v___x_836_);
v___x_837_ = l_Lean_Syntax_node4(v___y_819_, v___x_620_, v___y_820_, v___x_834_, v___x_836_, v___y_825_);
v___x_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_838_, 0, v___y_819_);
lean_ctor_set(v___x_838_, 1, v___y_827_);
lean_ctor_set(v___x_838_, 2, v___y_822_);
lean_inc(v___y_818_);
v___x_839_ = l_Lean_Syntax_node2(v___y_819_, v___y_818_, v___x_837_, v___x_838_);
v___x_840_ = lean_array_push(v___y_823_, v___x_839_);
v___x_841_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_842_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_843_ = l_Array_append___redArg(v___y_822_, v___x_840_);
lean_dec_ref(v___x_840_);
v___x_844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_844_, 0, v___y_819_);
lean_ctor_set(v___x_844_, 1, v___y_827_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
v___x_845_ = l_Lean_Syntax_node1(v___y_819_, v___x_842_, v___x_844_);
v___x_846_ = l_Lean_Syntax_node2(v___y_819_, v___x_841_, v___x_836_, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___y_826_);
return v___x_847_;
}
v___jp_848_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_858_ = lean_array_get_size(v___y_852_);
v___x_859_ = l_Array_toSubarray___redArg(v___y_852_, v___x_625_, v___x_858_);
lean_inc_ref(v___y_853_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___y_853_);
lean_ctor_set(v___x_860_, 1, v_body_855_);
v___x_861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_851_, v___x_859_, v___x_860_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v_a_863_; lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_884_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
v_a_863_ = lean_ctor_get(v___x_861_, 1);
lean_inc(v_a_863_);
lean_dec_ref(v___x_861_);
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
v___x_870_ = l_Lean_SourceInfo_fromRef(v_ref_869_, v___y_851_);
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
if (lean_obj_tag(v___y_849_) == 1)
{
lean_object* v_val_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_val_878_ = lean_ctor_get(v___y_849_, 0);
lean_inc(v_val_878_);
lean_dec_ref(v___y_849_);
v___x_879_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_870_);
v___x_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_870_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = l_Array_mkArray2___redArg(v_val_878_, v___x_880_);
v___y_818_ = v___x_871_;
v___y_819_ = v___x_870_;
v___y_820_ = v___x_875_;
v___y_821_ = v___y_850_;
v___y_822_ = v___x_877_;
v___y_823_ = v_fst_864_;
v___y_824_ = v_x_854_;
v___y_825_ = v_snd_865_;
v___y_826_ = v_a_863_;
v___y_827_ = v___x_876_;
v___y_828_ = v___x_881_;
goto v___jp_817_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v___y_849_);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_818_ = v___x_871_;
v___y_819_ = v___x_870_;
v___y_820_ = v___x_875_;
v___y_821_ = v___y_850_;
v___y_822_ = v___x_877_;
v___y_823_ = v_fst_864_;
v___y_824_ = v_x_854_;
v___y_825_ = v_snd_865_;
v___y_826_ = v_a_863_;
v___y_827_ = v___x_876_;
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
v___x_903_ = l_Lean_Syntax_getArg(v___y_895_, v___x_625_);
v___x_904_ = l_Lean_Syntax_getArg(v___y_895_, v___y_897_);
lean_dec(v___y_895_);
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
v___x_909_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_903_, v___y_896_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v_a_911_; lean_object* v_ref_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc_n(v_a_910_, 2);
v_a_911_ = lean_ctor_get(v___x_909_, 1);
lean_inc(v_a_911_);
lean_dec_ref(v___x_909_);
v_ref_912_ = lean_ctor_get(v___y_901_, 5);
v___x_913_ = l_Lean_SourceInfo_fromRef(v_ref_912_, v___y_896_);
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
v___x_935_ = l_Lean_Syntax_node4(v___x_913_, v___x_928_, v___x_930_, v___x_932_, v___x_934_, v___y_899_);
v___x_936_ = l_Lean_Syntax_node1(v___x_913_, v___x_915_, v___x_935_);
v___x_937_ = l_Lean_Syntax_node1(v___x_913_, v___x_927_, v___x_936_);
v___x_938_ = l_Lean_Syntax_node7(v___x_913_, v___x_917_, v___x_919_, v___x_921_, v___x_921_, v___x_921_, v___x_924_, v___x_926_, v___x_937_);
v___x_939_ = l_Lean_Syntax_node2(v___x_913_, v___x_916_, v___x_938_, v___x_921_);
v___x_940_ = l_Lean_Syntax_node1(v___x_913_, v___x_915_, v___x_939_);
v___x_941_ = l_Lean_Syntax_node1(v___x_913_, v___x_914_, v___x_940_);
v___y_849_ = v_h_x3f_900_;
v___y_850_ = v___x_904_;
v___y_851_ = v___y_896_;
v___y_852_ = v___y_898_;
v___y_853_ = v_doElems_905_;
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
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
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
v___x_951_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_903_, v___y_896_, v___y_901_, v___y_902_);
lean_dec(v___x_903_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_a_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
v_a_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_a_953_);
lean_dec_ref(v___x_951_);
v___y_849_ = v_h_x3f_900_;
v___y_850_ = v___x_904_;
v___y_851_ = v___y_896_;
v___y_852_ = v___y_898_;
v___y_853_ = v_doElems_905_;
v_x_854_ = v_a_952_;
v_body_855_ = v___y_899_;
v___y_856_ = v___y_901_;
v___y_857_ = v_a_953_;
goto v___jp_848_;
}
else
{
lean_object* v_a_954_; lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec(v___x_904_);
lean_dec(v_h_x3f_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
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
v___y_849_ = v_h_x3f_900_;
v___y_850_ = v___x_904_;
v___y_851_ = v___y_896_;
v___y_852_ = v___y_898_;
v___y_853_ = v_doElems_905_;
v_x_854_ = v___x_903_;
v_body_855_ = v___y_899_;
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
v___y_895_ = v___x_972_;
v___y_896_ = v___x_968_;
v___y_897_ = v___x_975_;
v___y_898_ = v_decls_970_;
v___y_899_ = v_body_976_;
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
v___y_895_ = v___x_972_;
v___y_896_ = v___x_968_;
v___y_897_ = v___x_975_;
v___y_898_ = v_decls_970_;
v___y_899_ = v_body_976_;
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
lean_inc_ref_n(v___y_988_, 3);
v___x_998_ = l_Array_append___redArg(v___y_988_, v___y_997_);
lean_dec_ref(v___y_997_);
lean_inc_n(v___y_995_, 4);
lean_inc_n(v___y_989_, 10);
v___x_999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_999_, 0, v___y_989_);
lean_ctor_set(v___x_999_, 1, v___y_995_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___y_989_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node4(v___y_989_, v___x_785_, v___x_999_, v___y_996_, v___x_1001_, v___y_994_);
v___x_1003_ = l_Lean_Syntax_node1(v___y_989_, v___y_995_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___y_989_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
lean_inc_ref(v___x_1005_);
v___x_1006_ = l_Lean_Syntax_node4(v___y_989_, v___x_620_, v___y_991_, v___x_1003_, v___x_1005_, v___y_993_);
v___x_1007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1007_, 0, v___y_989_);
lean_ctor_set(v___x_1007_, 1, v___y_995_);
lean_ctor_set(v___x_1007_, 2, v___y_988_);
lean_inc(v___y_992_);
v___x_1008_ = l_Lean_Syntax_node2(v___y_989_, v___y_992_, v___x_1006_, v___x_1007_);
v___x_1009_ = lean_array_push(v___y_987_, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1011_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1012_ = l_Array_append___redArg(v___y_988_, v___x_1009_);
lean_dec_ref(v___x_1009_);
v___x_1013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1013_, 0, v___y_989_);
lean_ctor_set(v___x_1013_, 1, v___y_995_);
lean_ctor_set(v___x_1013_, 2, v___x_1012_);
v___x_1014_ = l_Lean_Syntax_node1(v___y_989_, v___x_1011_, v___x_1013_);
v___x_1015_ = l_Lean_Syntax_node2(v___y_989_, v___x_1010_, v___x_1005_, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___y_990_);
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
lean_dec_ref(v___x_1477_);
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
uint8_t v___x_71071__boxed_1496_; lean_object* v_res_1497_; 
v___x_71071__boxed_1496_ = lean_unbox(v___x_1486_);
v_res_1497_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_a_1484_, v___x_1485_, v___x_71071__boxed_1496_, v_r_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
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
v___x_1513_ = l_Lean_TSyntax_getId(v_a_1512_);
v___x_1514_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_1513_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc_n(v_a_1515_, 2);
lean_dec_ref(v___x_1514_);
v___x_1516_ = l_Lean_LocalDecl_toExpr(v_a_1515_);
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_box(0);
v___x_1519_ = 0;
lean_inc_ref(v___x_1516_);
lean_inc(v_a_1512_);
v___x_1520_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_1512_, v___x_1516_, v___x_1517_, v___x_1517_, v___x_1518_, v___x_1519_, v___x_1519_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v___x_1520_);
v___x_1521_ = l_Lean_LocalDecl_type(v_a_1515_);
lean_dec(v_a_1515_);
v___x_1522_ = l_Lean_Meta_getDecLevel(v___x_1521_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v_u_1524_; lean_object* v___x_1525_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v_u_1524_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_u_1524_);
v___x_1525_ = l_Lean_Meta_isLevelDefEq(v_a_1523_, v_u_1524_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1526_; size_t v___x_1527_; size_t v___x_1528_; 
lean_dec_ref(v___x_1525_);
v___x_1526_ = lean_array_push(v_b_1502_, v___x_1516_);
v___x_1527_ = ((size_t)1ULL);
v___x_1528_ = lean_usize_add(v_i_1501_, v___x_1527_);
v_i_1501_ = v___x_1528_;
v_b_1502_ = v___x_1526_;
goto _start;
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v___x_1516_);
lean_dec_ref(v_b_1502_);
lean_dec_ref(v___x_1498_);
v_a_1530_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1525_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1525_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v___x_1516_);
lean_dec_ref(v_b_1502_);
lean_dec_ref(v___x_1498_);
v_a_1538_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1522_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1522_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v___x_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_b_1502_);
lean_dec_ref(v___x_1498_);
v_a_1546_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1520_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1520_);
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
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref(v_b_1502_);
lean_dec_ref(v___x_1498_);
v_a_1554_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1514_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1514_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v___x_1562_, lean_object* v_as_1563_, lean_object* v_sz_1564_, lean_object* v_i_1565_, lean_object* v_b_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
size_t v_sz_boxed_1574_; size_t v_i_boxed_1575_; lean_object* v_res_1576_; 
v_sz_boxed_1574_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1575_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_1562_, v_as_1563_, v_sz_boxed_1574_, v_i_boxed_1575_, v_b_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec_ref(v_as_1563_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(lean_object* v_msgData_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; lean_object* v_env_1584_; lean_object* v___x_1585_; lean_object* v_mctx_1586_; lean_object* v_lctx_1587_; lean_object* v_options_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1583_ = lean_st_ref_get(v___y_1581_);
v_env_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc_ref(v_env_1584_);
lean_dec(v___x_1583_);
v___x_1585_ = lean_st_ref_get(v___y_1579_);
v_mctx_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_mctx_1586_);
lean_dec(v___x_1585_);
v_lctx_1587_ = lean_ctor_get(v___y_1578_, 2);
v_options_1588_ = lean_ctor_get(v___y_1580_, 2);
lean_inc_ref(v_options_1588_);
lean_inc_ref(v_lctx_1587_);
v___x_1589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1589_, 0, v_env_1584_);
lean_ctor_set(v___x_1589_, 1, v_mctx_1586_);
lean_ctor_set(v___x_1589_, 2, v_lctx_1587_);
lean_ctor_set(v___x_1589_, 3, v_options_1588_);
v___x_1590_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v_msgData_1577_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(lean_object* v_msgData_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
return v_res_1598_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_box(1);
v___x_1600_ = l_Lean_MessageData_ofFormat(v___x_1599_);
return v___x_1600_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2));
v___x_1605_ = l_Lean_MessageData_ofFormat(v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(lean_object* v_x_1606_, lean_object* v_x_1607_){
_start:
{
if (lean_obj_tag(v_x_1607_) == 0)
{
return v_x_1606_;
}
else
{
lean_object* v_head_1608_; lean_object* v_tail_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1631_; 
v_head_1608_ = lean_ctor_get(v_x_1607_, 0);
v_tail_1609_ = lean_ctor_get(v_x_1607_, 1);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_x_1607_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1611_ = v_x_1607_;
v_isShared_1612_ = v_isSharedCheck_1631_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_tail_1609_);
lean_inc(v_head_1608_);
lean_dec(v_x_1607_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1631_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_before_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1629_; 
v_before_1613_ = lean_ctor_get(v_head_1608_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_head_1608_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v_head_1608_, 1);
lean_dec(v_unused_1630_);
v___x_1615_ = v_head_1608_;
v_isShared_1616_ = v_isSharedCheck_1629_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_before_1613_);
lean_dec(v_head_1608_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1629_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 7);
lean_ctor_set(v___x_1615_, 1, v___x_1617_);
lean_ctor_set(v___x_1615_, 0, v_x_1606_);
v___x_1619_ = v___x_1615_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_x_1606_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
if (v_isShared_1612_ == 0)
{
lean_ctor_set_tag(v___x_1611_, 7);
lean_ctor_set(v___x_1611_, 1, v___x_1620_);
lean_ctor_set(v___x_1611_, 0, v___x_1619_);
v___x_1622_ = v___x_1611_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = l_Lean_MessageData_ofSyntax(v_before_1613_);
v___x_1624_ = l_Lean_indentD(v___x_1623_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1622_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v_x_1606_ = v___x_1625_;
v_x_1607_ = v_tail_1609_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(lean_object* v_opts_1632_, lean_object* v_opt_1633_){
_start:
{
lean_object* v_name_1634_; lean_object* v_defValue_1635_; lean_object* v_map_1636_; lean_object* v___x_1637_; 
v_name_1634_ = lean_ctor_get(v_opt_1633_, 0);
v_defValue_1635_ = lean_ctor_get(v_opt_1633_, 1);
v_map_1636_ = lean_ctor_get(v_opts_1632_, 0);
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1636_, v_name_1634_);
if (lean_obj_tag(v___x_1637_) == 0)
{
uint8_t v___x_1638_; 
v___x_1638_ = lean_unbox(v_defValue_1635_);
return v___x_1638_;
}
else
{
lean_object* v_val_1639_; 
v_val_1639_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_val_1639_);
lean_dec_ref(v___x_1637_);
if (lean_obj_tag(v_val_1639_) == 1)
{
uint8_t v_v_1640_; 
v_v_1640_ = lean_ctor_get_uint8(v_val_1639_, 0);
lean_dec_ref(v_val_1639_);
return v_v_1640_;
}
else
{
uint8_t v___x_1641_; 
lean_dec(v_val_1639_);
v___x_1641_ = lean_unbox(v_defValue_1635_);
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_1642_, lean_object* v_opt_1643_){
_start:
{
uint8_t v_res_1644_; lean_object* v_r_1645_; 
v_res_1644_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_1642_, v_opt_1643_);
lean_dec_ref(v_opt_1643_);
lean_dec_ref(v_opts_1642_);
v_r_1645_ = lean_box(v_res_1644_);
return v_r_1645_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1));
v___x_1650_ = l_Lean_MessageData_ofFormat(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(lean_object* v_msgData_1651_, lean_object* v_macroStack_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_options_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v_options_1655_ = lean_ctor_get(v___y_1653_, 2);
v___x_1656_ = l_Lean_Elab_pp_macroStack;
v___x_1657_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec(v_macroStack_1652_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_msgData_1651_);
return v___x_1658_;
}
else
{
if (lean_obj_tag(v_macroStack_1652_) == 0)
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_msgData_1651_);
return v___x_1659_;
}
else
{
lean_object* v_head_1660_; lean_object* v_after_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1676_; 
v_head_1660_ = lean_ctor_get(v_macroStack_1652_, 0);
lean_inc(v_head_1660_);
v_after_1661_ = lean_ctor_get(v_head_1660_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_head_1660_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v_head_1660_, 0);
lean_dec(v_unused_1677_);
v___x_1663_ = v_head_1660_;
v_isShared_1664_ = v_isSharedCheck_1676_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_after_1661_);
lean_dec(v_head_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1676_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 7);
lean_ctor_set(v___x_1663_, 1, v___x_1665_);
lean_ctor_set(v___x_1663_, 0, v_msgData_1651_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_msgData_1651_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_msgData_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1668_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = l_Lean_MessageData_ofSyntax(v_after_1661_);
v___x_1671_ = l_Lean_indentD(v___x_1670_);
v_msgData_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1672_, 0, v___x_1669_);
lean_ctor_set(v_msgData_1672_, 1, v___x_1671_);
v___x_1673_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_1672_, v_macroStack_1652_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_1678_, lean_object* v_macroStack_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_1678_, v_macroStack_1679_, v___y_1680_);
lean_dec_ref(v___y_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_msg_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_ref_1691_; lean_object* v___x_1692_; lean_object* v_a_1693_; lean_object* v_macroStack_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1705_; 
v_ref_1691_ = lean_ctor_get(v___y_1688_, 5);
v___x_1692_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_1683_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref(v___x_1692_);
v_macroStack_1694_ = lean_ctor_get(v___y_1684_, 1);
v___x_1695_ = l_Lean_Elab_getBetterRef(v_ref_1691_, v_macroStack_1694_);
lean_inc(v_macroStack_1694_);
v___x_1696_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_1693_, v_macroStack_1694_, v___y_1688_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1695_);
lean_ctor_set(v___x_1701_, 1, v_a_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set_tag(v___x_1699_, 1);
lean_ctor_set(v___x_1699_, 0, v___x_1701_);
v___x_1703_ = v___x_1699_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_msg_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1714_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2));
v___x_1722_ = l_Lean_mkConst(v___x_1721_, v___x_1720_);
return v___x_1722_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6));
v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9));
v___x_1733_ = l_Lean_MessageData_ofFormat(v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v___y_1734_, lean_object* v_monadInfo_1735_, uint8_t v_returnsEarly_1736_, lean_object* v___x_1737_, lean_object* v_a_1738_, uint8_t v___x_1739_, lean_object* v_e_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_defs_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___x_1772_; lean_object* v_returnVar_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1807_; lean_object* v___y_1808_; 
v___x_1772_ = lean_mk_empty_array_with_capacity(v___x_1737_);
if (lean_obj_tag(v_e_1740_) == 0)
{
if (v___x_1739_ == 0)
{
goto v___jp_1821_;
}
else
{
goto v___jp_1782_;
}
}
else
{
goto v___jp_1821_;
}
v___jp_1748_:
{
size_t v_sz_1756_; size_t v___x_1757_; lean_object* v___x_1758_; 
v_sz_1756_ = lean_array_size(v___y_1734_);
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v_monadInfo_1735_, v___y_1734_, v_sz_1756_, v___x_1757_, v_defs_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
if (lean_obj_tag(v___x_1758_) == 0)
{
if (v_returnsEarly_1736_ == 0)
{
return v___x_1758_;
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
v___x_1760_ = lean_array_get_size(v___y_1734_);
v___x_1761_ = lean_nat_dec_eq(v___x_1760_, v___x_1737_);
if (v___x_1761_ == 0)
{
lean_dec(v_a_1759_);
return v___x_1758_;
}
else
{
lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1770_; 
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; 
v_unused_1771_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1771_);
v___x_1763_ = v___x_1758_;
v_isShared_1764_ = v_isSharedCheck_1770_;
goto v_resetjp_1762_;
}
else
{
lean_dec(v___x_1758_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1770_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1765_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3);
v___x_1766_ = lean_array_push(v_a_1759_, v___x_1765_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1766_);
v___x_1768_ = v___x_1763_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
return v___x_1758_;
}
}
v___jp_1773_:
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_array_push(v___x_1772_, v_returnVar_1774_);
v_defs_1749_ = v___x_1781_;
v___y_1750_ = v___y_1775_;
v___y_1751_ = v___y_1776_;
v___y_1752_ = v___y_1777_;
v___y_1753_ = v___y_1778_;
v___y_1754_ = v___y_1779_;
v___y_1755_ = v___y_1780_;
goto v___jp_1748_;
}
v___jp_1782_:
{
if (v_returnsEarly_1736_ == 0)
{
lean_dec(v_e_1740_);
lean_dec_ref(v_a_1738_);
v_defs_1749_ = v___x_1772_;
v___y_1750_ = v___y_1741_;
v___y_1751_ = v___y_1742_;
v___y_1752_ = v___y_1743_;
v___y_1753_ = v___y_1744_;
v___y_1754_ = v___y_1745_;
v___y_1755_ = v___y_1746_;
goto v___jp_1748_;
}
else
{
if (lean_obj_tag(v_e_1740_) == 0)
{
lean_object* v_resultType_1783_; lean_object* v___x_1784_; 
v_resultType_1783_ = lean_ctor_get(v_a_1738_, 0);
lean_inc_ref(v_resultType_1783_);
lean_dec_ref(v_a_1738_);
v___x_1784_ = l_Lean_Meta_mkNone(v_resultType_1783_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___x_1784_);
v_returnVar_1774_ = v_a_1785_;
v___y_1775_ = v___y_1741_;
v___y_1776_ = v___y_1742_;
v___y_1777_ = v___y_1743_;
v___y_1778_ = v___y_1744_;
v___y_1779_ = v___y_1745_;
v___y_1780_ = v___y_1746_;
goto v___jp_1773_;
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___x_1772_);
lean_dec_ref(v_monadInfo_1735_);
v_a_1786_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1784_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1784_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_val_1794_; lean_object* v_resultType_1795_; lean_object* v___x_1796_; 
v_val_1794_ = lean_ctor_get(v_e_1740_, 0);
lean_inc(v_val_1794_);
lean_dec_ref(v_e_1740_);
v_resultType_1795_ = lean_ctor_get(v_a_1738_, 0);
lean_inc_ref(v_resultType_1795_);
lean_dec_ref(v_a_1738_);
v___x_1796_ = l_Lean_Meta_mkSome(v_resultType_1795_, v_val_1794_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
v_returnVar_1774_ = v_a_1797_;
v___y_1775_ = v___y_1741_;
v___y_1776_ = v___y_1742_;
v___y_1777_ = v___y_1743_;
v___y_1778_ = v___y_1744_;
v___y_1779_ = v___y_1745_;
v___y_1780_ = v___y_1746_;
goto v___jp_1773_;
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref(v___x_1772_);
lean_dec_ref(v_monadInfo_1735_);
v_a_1798_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1796_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1796_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
}
v___jp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_inc_ref(v___y_1807_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___y_1807_);
lean_ctor_set(v___x_1809_, 1, v___y_1808_);
v___x_1810_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___x_1811_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
v___jp_1821_:
{
if (v_returnsEarly_1736_ == 0)
{
lean_object* v___x_1822_; 
lean_dec_ref(v___x_1772_);
lean_dec_ref(v_a_1738_);
lean_dec_ref(v_monadInfo_1735_);
v___x_1822_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7);
if (lean_obj_tag(v_e_1740_) == 0)
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10);
v___y_1807_ = v___x_1822_;
v___y_1808_ = v___x_1823_;
goto v___jp_1806_;
}
else
{
lean_object* v_val_1824_; lean_object* v___x_1825_; 
v_val_1824_ = lean_ctor_get(v_e_1740_, 0);
lean_inc(v_val_1824_);
lean_dec_ref(v_e_1740_);
v___x_1825_ = l_Lean_MessageData_ofExpr(v_val_1824_);
v___y_1807_ = v___x_1822_;
v___y_1808_ = v___x_1825_;
goto v___jp_1806_;
}
}
else
{
goto v___jp_1782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v___y_1826_, lean_object* v_monadInfo_1827_, lean_object* v_returnsEarly_1828_, lean_object* v___x_1829_, lean_object* v_a_1830_, lean_object* v___x_1831_, lean_object* v_e_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
uint8_t v_returnsEarly_boxed_1840_; uint8_t v___x_71502__boxed_1841_; lean_object* v_res_1842_; 
v_returnsEarly_boxed_1840_ = lean_unbox(v_returnsEarly_1828_);
v___x_71502__boxed_1841_ = lean_unbox(v___x_1831_);
v_res_1842_ = l_Lean_Elab_Do_elabDoFor___lam__3(v___y_1826_, v_monadInfo_1827_, v_returnsEarly_boxed_1840_, v___x_1829_, v_a_1830_, v___x_71502__boxed_1841_, v_e_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___x_1829_);
lean_dec_ref(v___y_1826_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object* v___f_1844_, lean_object* v_u_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v_snd_1848_, lean_object* v___x_1849_, lean_object* v_e_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_e_1850_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
v___x_1860_ = lean_apply_8(v___f_1844_, v___x_1859_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, lean_box(0));
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1862_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref(v___x_1860_);
v___x_1862_ = l_Lean_Meta_mkProdMkN(v_a_1861_, v_u_1845_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v_fst_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref(v___x_1862_);
v_fst_1864_ = lean_ctor_get(v_a_1863_, 0);
lean_inc(v_fst_1864_);
lean_dec(v_a_1863_);
v___x_1865_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1866_ = l_Lean_Name_mkStr2(v___x_1846_, v___x_1865_);
v___x_1867_ = l_Lean_mkConst(v___x_1866_, v___x_1847_);
v___x_1868_ = l_Lean_mkAppB(v___x_1867_, v_snd_1848_, v_fst_1864_);
v___x_1869_ = l_Lean_Elab_Do_mkPureApp(v___x_1849_, v___x_1868_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1869_;
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v___x_1849_);
lean_dec_ref(v_snd_1848_);
lean_dec(v___x_1847_);
lean_dec_ref(v___x_1846_);
v_a_1870_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1862_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1862_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec_ref(v___x_1849_);
lean_dec_ref(v_snd_1848_);
lean_dec(v___x_1847_);
lean_dec_ref(v___x_1846_);
lean_dec(v_u_1845_);
v_a_1878_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1860_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1860_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object* v___f_1886_, lean_object* v_u_1887_, lean_object* v___x_1888_, lean_object* v___x_1889_, lean_object* v_snd_1890_, lean_object* v___x_1891_, lean_object* v_e_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Elab_Do_elabDoFor___lam__4(v___f_1886_, v_u_1887_, v___x_1888_, v___x_1889_, v_snd_1890_, v___x_1891_, v_e_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___f_1903_, lean_object* v___x_1904_, lean_object* v_u_1905_, lean_object* v___x_1906_, lean_object* v___x_1907_, lean_object* v_snd_1908_, lean_object* v___x_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
lean_inc(v___y_1916_);
lean_inc_ref(v___y_1915_);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
v___x_1918_ = lean_apply_8(v___f_1903_, v___x_1904_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, lean_box(0));
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref(v___x_1918_);
v___x_1920_ = l_Lean_Meta_mkProdMkN(v_a_1919_, v_u_1905_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_fst_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
v_fst_1922_ = lean_ctor_get(v_a_1921_, 0);
lean_inc(v_fst_1922_);
lean_dec(v_a_1921_);
v___x_1923_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0));
v___x_1924_ = l_Lean_Name_mkStr2(v___x_1906_, v___x_1923_);
v___x_1925_ = l_Lean_mkConst(v___x_1924_, v___x_1907_);
v___x_1926_ = l_Lean_mkAppB(v___x_1925_, v_snd_1908_, v_fst_1922_);
v___x_1927_ = l_Lean_Elab_Do_mkPureApp(v___x_1909_, v___x_1926_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1927_;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v___x_1909_);
lean_dec_ref(v_snd_1908_);
lean_dec(v___x_1907_);
lean_dec_ref(v___x_1906_);
v_a_1928_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1920_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1920_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
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
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v___x_1909_);
lean_dec_ref(v_snd_1908_);
lean_dec(v___x_1907_);
lean_dec_ref(v___x_1906_);
lean_dec(v_u_1905_);
v_a_1936_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1918_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1918_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___f_1944_, lean_object* v___x_1945_, lean_object* v_u_1946_, lean_object* v___x_1947_, lean_object* v___x_1948_, lean_object* v_snd_1949_, lean_object* v___x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___f_1944_, v___x_1945_, v_u_1946_, v___x_1947_, v___x_1948_, v_snd_1949_, v___x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_1960_, lean_object* v___x_1961_, lean_object* v_u_1962_, lean_object* v___x_1963_, lean_object* v___x_1964_, lean_object* v_snd_1965_, lean_object* v___x_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
lean_inc(v___y_1971_);
lean_inc_ref(v___y_1970_);
lean_inc(v___y_1969_);
lean_inc_ref(v___y_1968_);
v___x_1975_ = lean_apply_8(v___f_1960_, v___x_1961_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, lean_box(0));
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = l_Lean_Meta_mkProdMkN(v_a_1976_, v_u_1962_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v_fst_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
v_fst_1979_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_fst_1979_);
lean_dec(v_a_1978_);
v___x_1980_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1981_ = l_Lean_Name_mkStr2(v___x_1963_, v___x_1980_);
v___x_1982_ = l_Lean_mkConst(v___x_1981_, v___x_1964_);
v___x_1983_ = l_Lean_mkAppB(v___x_1982_, v_snd_1965_, v_fst_1979_);
v___x_1984_ = l_Lean_Elab_Do_mkPureApp(v___x_1966_, v___x_1983_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
return v___x_1984_;
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v___x_1966_);
lean_dec_ref(v_snd_1965_);
lean_dec(v___x_1964_);
lean_dec_ref(v___x_1963_);
v_a_1985_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1977_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1977_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec_ref(v___x_1966_);
lean_dec_ref(v_snd_1965_);
lean_dec(v___x_1964_);
lean_dec_ref(v___x_1963_);
lean_dec(v_u_1962_);
v_a_1993_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1975_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1975_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_2001_, lean_object* v___x_2002_, lean_object* v_u_2003_, lean_object* v___x_2004_, lean_object* v___x_2005_, lean_object* v_snd_2006_, lean_object* v___x_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_2001_, v___x_2002_, v_u_2003_, v___x_2004_, v___x_2005_, v_snd_2006_, v___x_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___x_2017_, lean_object* v___f_2018_, lean_object* v___f_2019_, lean_object* v___x_2020_, lean_object* v___x_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_monadInfo_2030_; lean_object* v_mutVars_2031_; lean_object* v_mutVarDefs_2032_; lean_object* v_contInfo_2033_; uint8_t v_deadCode_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2042_; 
v_monadInfo_2030_ = lean_ctor_get(v___y_2022_, 0);
v_mutVars_2031_ = lean_ctor_get(v___y_2022_, 1);
v_mutVarDefs_2032_ = lean_ctor_get(v___y_2022_, 2);
v_contInfo_2033_ = lean_ctor_get(v___y_2022_, 4);
v_deadCode_2034_ = lean_ctor_get_uint8(v___y_2022_, sizeof(void*)*5);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___y_2022_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___y_2022_, 3);
lean_dec(v_unused_2043_);
v___x_2036_ = v___y_2022_;
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_contInfo_2033_);
lean_inc(v_mutVarDefs_2032_);
lean_inc(v_mutVars_2031_);
lean_inc(v_monadInfo_2030_);
lean_dec(v___y_2022_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 3, v___x_2017_);
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_monadInfo_2030_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_mutVars_2031_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_mutVarDefs_2032_);
lean_ctor_set(v_reuseFailAlloc_2041_, 3, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2041_, 4, v_contInfo_2033_);
lean_ctor_set_uint8(v_reuseFailAlloc_2041_, sizeof(void*)*5, v_deadCode_2034_);
v___x_2039_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_2018_, v___f_2019_, v___x_2020_, v___x_2021_, v___x_2039_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec_ref(v___x_2039_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___x_2044_, lean_object* v___f_2045_, lean_object* v___f_2046_, lean_object* v___x_2047_, lean_object* v___x_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___x_2044_, v___f_2045_, v___f_2046_, v___x_2047_, v___x_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_u_2063_, lean_object* v_snd_2064_, lean_object* v___f_2065_, lean_object* v___x_2066_, lean_object* v_body_2067_, uint8_t v___x_2068_, lean_object* v___y_2069_, lean_object* v_xh_2070_, lean_object* v_loopS_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_resultType_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2117_; 
v_resultType_2080_ = lean_ctor_get(v_a_2061_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2061_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v_a_2061_, 1);
lean_dec(v_unused_2118_);
v___x_2082_ = v_a_2061_;
v_isShared_2083_ = v_isSharedCheck_2117_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_resultType_2080_);
lean_dec(v_a_2061_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2117_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_resultName_2084_; lean_object* v_resultType_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2115_; 
v_resultName_2084_ = lean_ctor_get(v_a_2062_, 0);
v_resultType_2085_ = lean_ctor_get(v_a_2062_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v_a_2062_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v_a_2062_, 2);
lean_dec(v_unused_2116_);
v___x_2087_ = v_a_2062_;
v_isShared_2088_ = v_isSharedCheck_2115_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_resultType_2085_);
lean_inc(v_resultName_2084_);
lean_dec(v_a_2062_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2115_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___f_2096_; lean_object* v___f_2097_; lean_object* v___f_2098_; lean_object* v___x_2100_; 
v___x_2089_ = l_Lean_Expr_fvarId_x21(v_loopS_2071_);
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0));
v___x_2091_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1));
v___x_2092_ = lean_box(0);
lean_inc_n(v_u_2063_, 3);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v_u_2063_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
lean_inc_ref_n(v___x_2093_, 3);
v___x_2094_ = l_Lean_mkConst(v___x_2091_, v___x_2093_);
lean_inc_ref_n(v_snd_2064_, 3);
v___x_2095_ = l_Lean_Expr_app___override(v___x_2094_, v_snd_2064_);
lean_inc_ref_n(v___x_2095_, 3);
lean_inc_ref_n(v___f_2065_, 2);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 15, 6);
lean_closure_set(v___f_2096_, 0, v___f_2065_);
lean_closure_set(v___f_2096_, 1, v_u_2063_);
lean_closure_set(v___f_2096_, 2, v___x_2090_);
lean_closure_set(v___f_2096_, 3, v___x_2093_);
lean_closure_set(v___f_2096_, 4, v_snd_2064_);
lean_closure_set(v___f_2096_, 5, v___x_2095_);
lean_inc(v___x_2066_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 15, 7);
lean_closure_set(v___f_2097_, 0, v___f_2065_);
lean_closure_set(v___f_2097_, 1, v___x_2066_);
lean_closure_set(v___f_2097_, 2, v_u_2063_);
lean_closure_set(v___f_2097_, 3, v___x_2090_);
lean_closure_set(v___f_2097_, 4, v___x_2093_);
lean_closure_set(v___f_2097_, 5, v_snd_2064_);
lean_closure_set(v___f_2097_, 6, v___x_2095_);
v___f_2098_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 7);
lean_closure_set(v___f_2098_, 0, v___f_2065_);
lean_closure_set(v___f_2098_, 1, v___x_2066_);
lean_closure_set(v___f_2098_, 2, v_u_2063_);
lean_closure_set(v___f_2098_, 3, v___x_2090_);
lean_closure_set(v___f_2098_, 4, v___x_2093_);
lean_closure_set(v___f_2098_, 5, v_snd_2064_);
lean_closure_set(v___f_2098_, 6, v___x_2095_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v___f_2096_);
v___x_2100_ = v___x_2082_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_resultType_2080_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v___f_2096_);
v___x_2100_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
uint8_t v___x_2101_; lean_object* v___x_2103_; 
v___x_2101_ = 1;
lean_inc_ref(v___f_2097_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 2, v___f_2097_);
v___x_2103_ = v___x_2087_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_resultName_2084_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_resultType_2085_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v___f_2097_);
v___x_2103_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___f_2106_; lean_object* v___x_2107_; 
lean_ctor_set_uint8(v___x_2103_, sizeof(void*)*3, v___x_2101_);
v___x_2104_ = lean_box(v___x_2068_);
v___x_2105_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_2105_, 0, v_body_2067_);
lean_closure_set(v___x_2105_, 1, v___x_2103_);
lean_closure_set(v___x_2105_, 2, v___x_2104_);
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 13, 5);
lean_closure_set(v___f_2106_, 0, v___x_2095_);
lean_closure_set(v___f_2106_, 1, v___f_2098_);
lean_closure_set(v___f_2106_, 2, v___f_2097_);
lean_closure_set(v___f_2106_, 3, v___x_2100_);
lean_closure_set(v___f_2106_, 4, v___x_2105_);
v___x_2107_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2069_, v___x_2089_, v___f_2106_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref(v___x_2107_);
v___x_2109_ = lean_array_push(v_xh_2070_, v_loopS_2071_);
v___x_2110_ = 0;
v___x_2111_ = 1;
v___x_2112_ = l_Lean_Meta_mkLambdaFVars(v___x_2109_, v_a_2108_, v___x_2110_, v___x_2068_, v___x_2110_, v___x_2068_, v___x_2111_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec_ref(v___x_2109_);
return v___x_2112_;
}
else
{
lean_dec_ref(v_loopS_2071_);
lean_dec_ref(v_xh_2070_);
return v___x_2107_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object** _args){
lean_object* v_a_2119_ = _args[0];
lean_object* v_a_2120_ = _args[1];
lean_object* v_u_2121_ = _args[2];
lean_object* v_snd_2122_ = _args[3];
lean_object* v___f_2123_ = _args[4];
lean_object* v___x_2124_ = _args[5];
lean_object* v_body_2125_ = _args[6];
lean_object* v___x_2126_ = _args[7];
lean_object* v___y_2127_ = _args[8];
lean_object* v_xh_2128_ = _args[9];
lean_object* v_loopS_2129_ = _args[10];
lean_object* v___y_2130_ = _args[11];
lean_object* v___y_2131_ = _args[12];
lean_object* v___y_2132_ = _args[13];
lean_object* v___y_2133_ = _args[14];
lean_object* v___y_2134_ = _args[15];
lean_object* v___y_2135_ = _args[16];
lean_object* v___y_2136_ = _args[17];
lean_object* v___y_2137_ = _args[18];
_start:
{
uint8_t v___x_72059__boxed_2138_; lean_object* v_res_2139_; 
v___x_72059__boxed_2138_ = lean_unbox(v___x_2126_);
v_res_2139_ = l_Lean_Elab_Do_elabDoFor___lam__8(v_a_2119_, v_a_2120_, v_u_2121_, v_snd_2122_, v___f_2123_, v___x_2124_, v_body_2125_, v___x_72059__boxed_2138_, v___y_2127_, v_xh_2128_, v_loopS_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v___y_2130_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v___x_2140_, lean_object* v___x_2141_, lean_object* v_x_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_u_2145_, lean_object* v_snd_2146_, lean_object* v___f_2147_, lean_object* v___x_2148_, lean_object* v_body_2149_, uint8_t v___x_2150_, lean_object* v___y_2151_, lean_object* v_a_2152_, lean_object* v_h_x3f_2153_, lean_object* v___x_2154_, lean_object* v_xh_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_array_get_borrowed(v___x_2140_, v_xh_2155_, v___x_2141_);
lean_inc(v___x_2164_);
v___x_2165_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_2142_, v___x_2164_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2166_; lean_object* v___f_2167_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; 
lean_dec_ref(v___x_2165_);
v___x_2166_ = lean_box(v___x_2150_);
lean_inc_ref(v_xh_2155_);
lean_inc_ref(v_snd_2146_);
v___f_2167_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 19, 10);
lean_closure_set(v___f_2167_, 0, v_a_2143_);
lean_closure_set(v___f_2167_, 1, v_a_2144_);
lean_closure_set(v___f_2167_, 2, v_u_2145_);
lean_closure_set(v___f_2167_, 3, v_snd_2146_);
lean_closure_set(v___f_2167_, 4, v___f_2147_);
lean_closure_set(v___f_2167_, 5, v___x_2148_);
lean_closure_set(v___f_2167_, 6, v_body_2149_);
lean_closure_set(v___f_2167_, 7, v___x_2166_);
lean_closure_set(v___f_2167_, 8, v___y_2151_);
lean_closure_set(v___f_2167_, 9, v_xh_2155_);
if (lean_obj_tag(v_h_x3f_2153_) == 1)
{
lean_object* v_val_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_val_2179_ = lean_ctor_get(v_h_x3f_2153_, 0);
lean_inc(v_val_2179_);
lean_dec_ref(v_h_x3f_2153_);
v___x_2180_ = lean_array_get(v___x_2140_, v_xh_2155_, v___x_2154_);
lean_dec_ref(v_xh_2155_);
v___x_2181_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_2179_, v___x_2180_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_dec_ref(v___x_2181_);
v___y_2169_ = v___y_2156_;
v___y_2170_ = v___y_2157_;
v___y_2171_ = v___y_2158_;
v___y_2172_ = v___y_2159_;
v___y_2173_ = v___y_2160_;
v___y_2174_ = v___y_2161_;
v___y_2175_ = v___y_2162_;
goto v___jp_2168_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec_ref(v___f_2167_);
lean_dec(v_a_2152_);
lean_dec_ref(v_snd_2146_);
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_dec_ref(v_xh_2155_);
lean_dec(v_h_x3f_2153_);
v___y_2169_ = v___y_2156_;
v___y_2170_ = v___y_2157_;
v___y_2171_ = v___y_2158_;
v___y_2172_ = v___y_2159_;
v___y_2173_ = v___y_2160_;
v___y_2174_ = v___y_2161_;
v___y_2175_ = v___y_2162_;
goto v___jp_2168_;
}
v___jp_2168_:
{
uint8_t v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = 0;
v___x_2177_ = 1;
v___x_2178_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_2152_, v___x_2176_, v_snd_2146_, v___f_2167_, v___x_2177_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
return v___x_2178_;
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec_ref(v_xh_2155_);
lean_dec(v_h_x3f_2153_);
lean_dec(v_a_2152_);
lean_dec(v___y_2151_);
lean_dec(v_body_2149_);
lean_dec(v___x_2148_);
lean_dec_ref(v___f_2147_);
lean_dec_ref(v_snd_2146_);
lean_dec(v_u_2145_);
lean_dec_ref(v_a_2144_);
lean_dec_ref(v_a_2143_);
v_a_2190_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2165_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2165_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object** _args){
lean_object* v___x_2198_ = _args[0];
lean_object* v___x_2199_ = _args[1];
lean_object* v_x_2200_ = _args[2];
lean_object* v_a_2201_ = _args[3];
lean_object* v_a_2202_ = _args[4];
lean_object* v_u_2203_ = _args[5];
lean_object* v_snd_2204_ = _args[6];
lean_object* v___f_2205_ = _args[7];
lean_object* v___x_2206_ = _args[8];
lean_object* v_body_2207_ = _args[9];
lean_object* v___x_2208_ = _args[10];
lean_object* v___y_2209_ = _args[11];
lean_object* v_a_2210_ = _args[12];
lean_object* v_h_x3f_2211_ = _args[13];
lean_object* v___x_2212_ = _args[14];
lean_object* v_xh_2213_ = _args[15];
lean_object* v___y_2214_ = _args[16];
lean_object* v___y_2215_ = _args[17];
lean_object* v___y_2216_ = _args[18];
lean_object* v___y_2217_ = _args[19];
lean_object* v___y_2218_ = _args[20];
lean_object* v___y_2219_ = _args[21];
lean_object* v___y_2220_ = _args[22];
lean_object* v___y_2221_ = _args[23];
_start:
{
uint8_t v___x_72182__boxed_2222_; lean_object* v_res_2223_; 
v___x_72182__boxed_2222_ = lean_unbox(v___x_2208_);
v_res_2223_ = l_Lean_Elab_Do_elabDoFor___lam__9(v___x_2198_, v___x_2199_, v_x_2200_, v_a_2201_, v_a_2202_, v_u_2203_, v_snd_2204_, v___f_2205_, v___x_2206_, v_body_2207_, v___x_72182__boxed_2222_, v___y_2209_, v_a_2210_, v_h_x3f_2211_, v___x_2212_, v_xh_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___x_2212_);
lean_dec(v___x_2199_);
lean_dec_ref(v___x_2198_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(lean_object* v_name_2224_, lean_object* v_type_2225_, lean_object* v_k_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
uint8_t v___x_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = 0;
v___x_2236_ = 0;
v___x_2237_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2224_, v___x_2235_, v_type_2225_, v_k_2226_, v___x_2236_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(lean_object* v_name_2238_, lean_object* v_type_2239_, lean_object* v_k_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_2238_, v_type_2239_, v_k_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v___y_2241_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(uint8_t v_returnsEarly_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_doBlockResultType_2270_, lean_object* v_a_2271_, lean_object* v_v_2272_, lean_object* v_u_2273_, lean_object* v___f_2274_, lean_object* v___y_2275_, lean_object* v___x_2276_, lean_object* v___x_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_ret_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; 
if (v_returnsEarly_2267_ == 0)
{
lean_object* v___x_2341_; 
lean_dec_ref(v___f_2274_);
lean_dec(v_u_2273_);
lean_dec(v_v_2272_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_doBlockResultType_2270_);
lean_dec(v_a_2269_);
v___x_2341_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_2268_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2341_;
}
else
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Meta_getFVarFromUserName(v_a_2269_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = lean_array_get_size(v___y_2275_);
v___x_2345_ = lean_nat_dec_eq(v___x_2344_, v___x_2276_);
if (v___x_2345_ == 0)
{
v_ret_2287_ = v_a_2343_;
v___y_2288_ = v___y_2278_;
v___y_2289_ = v___y_2279_;
v___y_2290_ = v___y_2280_;
v___y_2291_ = v___y_2281_;
v___y_2292_ = v___y_2282_;
v___y_2293_ = v___y_2283_;
v___y_2294_ = v___y_2284_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2346_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9));
v___x_2347_ = lean_mk_empty_array_with_capacity(v___x_2277_);
v___x_2348_ = lean_array_push(v___x_2347_, v_a_2343_);
v___x_2349_ = l_Lean_Meta_mkAppM(v___x_2346_, v___x_2348_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v_ret_2287_ = v_a_2350_;
v___y_2288_ = v___y_2278_;
v___y_2289_ = v___y_2279_;
v___y_2290_ = v___y_2280_;
v___y_2291_ = v___y_2281_;
v___y_2292_ = v___y_2282_;
v___y_2293_ = v___y_2283_;
v___y_2294_ = v___y_2284_;
goto v___jp_2286_;
}
else
{
lean_dec_ref(v___f_2274_);
lean_dec(v_u_2273_);
lean_dec(v_v_2272_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_doBlockResultType_2270_);
lean_dec_ref(v_a_2268_);
return v___x_2349_;
}
}
}
else
{
lean_dec_ref(v___f_2274_);
lean_dec(v_u_2273_);
lean_dec(v_v_2272_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_doBlockResultType_2270_);
lean_dec_ref(v_a_2268_);
return v___x_2342_;
}
}
v___jp_2286_:
{
lean_object* v___x_2295_; 
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2291_);
lean_inc_ref(v_ret_2287_);
v___x_2295_ = lean_infer_type(v_ret_2287_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
v___x_2297_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_2270_, v___y_2288_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2299_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref(v___x_2297_);
v___x_2299_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_2268_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___x_2299_);
v___x_2301_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_2302_ = l_Lean_Core_mkFreshUserName(v___x_2301_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_resultType_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2331_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v_resultType_2304_ = lean_ctor_get(v_a_2271_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_a_2271_);
if (v_isSharedCheck_2331_ == 0)
{
lean_object* v_unused_2332_; 
v_unused_2332_ = lean_ctor_get(v_a_2271_, 1);
lean_dec(v_unused_2332_);
v___x_2306_ = v_a_2271_;
v_isShared_2307_ = v_isSharedCheck_2331_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_resultType_2304_);
lean_dec(v_a_2271_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2331_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2308_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2));
v___x_2309_ = 0;
v___x_2310_ = l_Lean_mkLambda(v___x_2308_, v___x_2309_, v_a_2296_, v_a_2298_);
v___x_2311_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6));
v___x_2312_ = l_Lean_Level_succ___override(v_v_2272_);
v___x_2313_ = lean_box(0);
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 1);
lean_ctor_set(v___x_2306_, 1, v___x_2313_);
lean_ctor_set(v___x_2306_, 0, v___x_2312_);
v___x_2315_ = v___x_2306_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2316_, 0, v_u_2273_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Lean_mkConst(v___x_2311_, v___x_2316_);
lean_inc_ref(v_resultType_2304_);
v___x_2318_ = l_Lean_mkApp3(v___x_2317_, v_resultType_2304_, v___x_2310_, v_ret_2287_);
v___x_2319_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_a_2303_, v_resultType_2304_, v___f_2274_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2329_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2329_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2329_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = l_Lean_mkSimpleThunk(v_a_2300_);
v___x_2325_ = l_Lean_mkAppB(v___x_2318_, v_a_2320_, v___x_2324_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_dec_ref(v___x_2318_);
lean_dec(v_a_2300_);
return v___x_2319_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_a_2300_);
lean_dec(v_a_2298_);
lean_dec(v_a_2296_);
lean_dec_ref(v_ret_2287_);
lean_dec_ref(v___f_2274_);
lean_dec(v_u_2273_);
lean_dec(v_v_2272_);
lean_dec_ref(v_a_2271_);
v_a_2333_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2302_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2302_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_dec(v_a_2298_);
lean_dec(v_a_2296_);
lean_dec_ref(v_ret_2287_);
lean_dec_ref(v___f_2274_);
lean_dec(v_u_2273_);
lean_dec(v_v_2272_);
lean_dec_ref(v_a_2271_);
return v___x_2299_;
}
}
else
{
lean_dec(v_a_2296_);
lean_dec_ref(v_ret_2287_);
lean_dec_ref(v___f_2274_);
lean_dec(v_u_2273_);
lean_dec(v_v_2272_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_a_2268_);
return v___x_2297_;
}
}
else
{
lean_dec_ref(v_ret_2287_);
lean_dec_ref(v___f_2274_);
lean_dec(v_u_2273_);
lean_dec(v_v_2272_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_doBlockResultType_2270_);
lean_dec_ref(v_a_2268_);
return v___x_2295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_returnsEarly_2351_ = _args[0];
lean_object* v_a_2352_ = _args[1];
lean_object* v_a_2353_ = _args[2];
lean_object* v_doBlockResultType_2354_ = _args[3];
lean_object* v_a_2355_ = _args[4];
lean_object* v_v_2356_ = _args[5];
lean_object* v_u_2357_ = _args[6];
lean_object* v___f_2358_ = _args[7];
lean_object* v___y_2359_ = _args[8];
lean_object* v___x_2360_ = _args[9];
lean_object* v___x_2361_ = _args[10];
lean_object* v___y_2362_ = _args[11];
lean_object* v___y_2363_ = _args[12];
lean_object* v___y_2364_ = _args[13];
lean_object* v___y_2365_ = _args[14];
lean_object* v___y_2366_ = _args[15];
lean_object* v___y_2367_ = _args[16];
lean_object* v___y_2368_ = _args[17];
lean_object* v___y_2369_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_2370_; lean_object* v_res_2371_; 
v_returnsEarly_boxed_2370_ = lean_unbox(v_returnsEarly_2351_);
v_res_2371_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_returnsEarly_boxed_2370_, v_a_2352_, v_a_2353_, v_doBlockResultType_2354_, v_a_2355_, v_v_2356_, v_u_2357_, v___f_2358_, v___y_2359_, v___x_2360_, v___x_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___x_2361_);
lean_dec(v___x_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___x_2374_, uint8_t v___x_2375_, lean_object* v_postS_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = l_Lean_Expr_fvarId_x21(v_postS_2376_);
v___x_2386_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2372_, v___x_2385_, v___y_2373_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref(v___x_2386_);
v___x_2388_ = lean_mk_empty_array_with_capacity(v___x_2374_);
v___x_2389_ = lean_array_push(v___x_2388_, v_postS_2376_);
v___x_2390_ = 0;
v___x_2391_ = 1;
v___x_2392_ = l_Lean_Meta_mkLambdaFVars(v___x_2389_, v_a_2387_, v___x_2390_, v___x_2375_, v___x_2390_, v___x_2375_, v___x_2391_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec_ref(v___x_2389_);
return v___x_2392_;
}
else
{
lean_dec_ref(v_postS_2376_);
return v___x_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___x_2395_, lean_object* v___x_2396_, lean_object* v_postS_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
uint8_t v___x_72564__boxed_2406_; lean_object* v_res_2407_; 
v___x_72564__boxed_2406_ = lean_unbox(v___x_2396_);
v_res_2407_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___y_2393_, v___y_2394_, v___x_2395_, v___x_72564__boxed_2406_, v_postS_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___x_2395_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v___x_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_val_2418_, lean_object* v_a_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v_a_2413_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2432_, 0, v_a_2414_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = l_Lean_mkConst(v___x_2429_, v___x_2432_);
v___x_2434_ = l_Lean_instInhabitedExpr;
v___x_2435_ = lean_array_get_borrowed(v___x_2434_, v_x_2420_, v___x_2415_);
lean_inc(v___x_2435_);
v___x_2436_ = l_Lean_mkApp5(v___x_2433_, v_a_2416_, v_a_2417_, v_val_2418_, v_a_2419_, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v___x_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_val_2443_, lean_object* v_a_2444_, lean_object* v_x_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_2438_, v_a_2439_, v___x_2440_, v_a_2441_, v_a_2442_, v_val_2443_, v_a_2444_, v_x_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec_ref(v_x_2445_);
lean_dec(v___x_2440_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(lean_object* v_a_2455_, lean_object* v_as_2456_, size_t v_i_2457_, size_t v_stop_2458_, lean_object* v_b_2459_){
_start:
{
lean_object* v___y_2461_; uint8_t v___x_2465_; 
v___x_2465_ = lean_usize_dec_eq(v_i_2457_, v_stop_2458_);
if (v___x_2465_ == 0)
{
lean_object* v_reassigns_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v_reassigns_2466_ = lean_ctor_get(v_a_2455_, 1);
v___x_2467_ = lean_array_uget_borrowed(v_as_2456_, v_i_2457_);
v___x_2468_ = l_Lean_TSyntax_getId(v___x_2467_);
v___x_2469_ = l_Lean_NameSet_contains(v_reassigns_2466_, v___x_2468_);
lean_dec(v___x_2468_);
if (v___x_2469_ == 0)
{
v___y_2461_ = v_b_2459_;
goto v___jp_2460_;
}
else
{
lean_object* v___x_2470_; 
lean_inc(v___x_2467_);
v___x_2470_ = lean_array_push(v_b_2459_, v___x_2467_);
v___y_2461_ = v___x_2470_;
goto v___jp_2460_;
}
}
else
{
return v_b_2459_;
}
v___jp_2460_:
{
size_t v___x_2462_; size_t v___x_2463_; 
v___x_2462_ = ((size_t)1ULL);
v___x_2463_ = lean_usize_add(v_i_2457_, v___x_2462_);
v_i_2457_ = v___x_2463_;
v_b_2459_ = v___y_2461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object* v_a_2471_, lean_object* v_as_2472_, lean_object* v_i_2473_, lean_object* v_stop_2474_, lean_object* v_b_2475_){
_start:
{
size_t v_i_boxed_2476_; size_t v_stop_boxed_2477_; lean_object* v_res_2478_; 
v_i_boxed_2476_ = lean_unbox_usize(v_i_2473_);
lean_dec(v_i_2473_);
v_stop_boxed_2477_ = lean_unbox_usize(v_stop_2474_);
lean_dec(v_stop_2474_);
v_res_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_2471_, v_as_2472_, v_i_boxed_2476_, v_stop_boxed_2477_, v_b_2475_);
lean_dec_ref(v_as_2472_);
lean_dec_ref(v_a_2471_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(size_t v_sz_2479_, size_t v_i_2480_, lean_object* v_bs_2481_){
_start:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_usize_dec_lt(v_i_2480_, v_sz_2479_);
if (v___x_2482_ == 0)
{
return v_bs_2481_;
}
else
{
lean_object* v_v_2483_; lean_object* v___x_2484_; lean_object* v_bs_x27_2485_; lean_object* v___x_2486_; size_t v___x_2487_; size_t v___x_2488_; lean_object* v___x_2489_; 
v_v_2483_ = lean_array_uget(v_bs_2481_, v_i_2480_);
v___x_2484_ = lean_unsigned_to_nat(0u);
v_bs_x27_2485_ = lean_array_uset(v_bs_2481_, v_i_2480_, v___x_2484_);
v___x_2486_ = l_Lean_TSyntax_getId(v_v_2483_);
lean_dec(v_v_2483_);
v___x_2487_ = ((size_t)1ULL);
v___x_2488_ = lean_usize_add(v_i_2480_, v___x_2487_);
v___x_2489_ = lean_array_uset(v_bs_x27_2485_, v_i_2480_, v___x_2486_);
v_i_2480_ = v___x_2488_;
v_bs_2481_ = v___x_2489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_sz_2491_, lean_object* v_i_2492_, lean_object* v_bs_2493_){
_start:
{
size_t v_sz_boxed_2494_; size_t v_i_boxed_2495_; lean_object* v_res_2496_; 
v_sz_boxed_2494_ = lean_unbox_usize(v_sz_2491_);
lean_dec(v_sz_2491_);
v_i_boxed_2495_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_boxed_2494_, v_i_boxed_2495_, v_bs_2493_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(lean_object* v___x_2497_, lean_object* v_a_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_70867__overap_2508_; lean_object* v___x_2509_; 
v___x_2507_ = l_Lean_instInhabitedExpr;
v___x_70867__overap_2508_ = l_instInhabitedOfMonad___redArg(v___x_2497_, v___x_2507_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc_ref(v___y_2499_);
v___x_2509_ = lean_apply_8(v___x_70867__overap_2508_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, lean_box(0));
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(lean_object* v___x_2510_, lean_object* v_a_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(v___x_2510_, v_a_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec_ref(v_a_2511_);
return v_res_2520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_instMonadEIO(lean_box(0));
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0);
v___x_2523_ = l_StateRefT_x27_instMonad___redArg(v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(lean_object* v_acc_2530_, lean_object* v_declInfos_2531_, lean_object* v_k_2532_, lean_object* v_kind_2533_, lean_object* v_x_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
uint8_t v_kind_boxed_2543_; lean_object* v_res_2544_; 
v_kind_boxed_2543_ = lean_unbox(v_kind_2533_);
v_res_2544_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(v_acc_2530_, v_declInfos_2531_, v_k_2532_, v_kind_boxed_2543_, v_x_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object* v_declInfos_2545_, lean_object* v_k_2546_, uint8_t v_kind_2547_, lean_object* v_acc_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v_toApplicative_2558_; lean_object* v_toFunctor_2559_; lean_object* v_toSeq_2560_; lean_object* v_toSeqLeft_2561_; lean_object* v_toSeqRight_2562_; lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_toApplicative_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2654_; 
v___x_2557_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1);
v_toApplicative_2558_ = lean_ctor_get(v___x_2557_, 0);
v_toFunctor_2559_ = lean_ctor_get(v_toApplicative_2558_, 0);
v_toSeq_2560_ = lean_ctor_get(v_toApplicative_2558_, 2);
v_toSeqLeft_2561_ = lean_ctor_get(v_toApplicative_2558_, 3);
v_toSeqRight_2562_ = lean_ctor_get(v_toApplicative_2558_, 4);
v___f_2563_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2));
v___f_2564_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3));
lean_inc_ref_n(v_toFunctor_2559_, 2);
v___f_2565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2565_, 0, v_toFunctor_2559_);
v___f_2566_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2566_, 0, v_toFunctor_2559_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___f_2565_);
lean_ctor_set(v___x_2567_, 1, v___f_2566_);
lean_inc(v_toSeqRight_2562_);
v___f_2568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2568_, 0, v_toSeqRight_2562_);
lean_inc(v_toSeqLeft_2561_);
v___f_2569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2569_, 0, v_toSeqLeft_2561_);
lean_inc(v_toSeq_2560_);
v___f_2570_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2570_, 0, v_toSeq_2560_);
v___x_2571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2567_);
lean_ctor_set(v___x_2571_, 1, v___f_2563_);
lean_ctor_set(v___x_2571_, 2, v___f_2570_);
lean_ctor_set(v___x_2571_, 3, v___f_2569_);
lean_ctor_set(v___x_2571_, 4, v___f_2568_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v___f_2564_);
v___x_2573_ = l_StateRefT_x27_instMonad___redArg(v___x_2572_);
v_toApplicative_2574_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v___x_2573_, 1);
lean_dec(v_unused_2655_);
v___x_2576_ = v___x_2573_;
v_isShared_2577_ = v_isSharedCheck_2654_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_toApplicative_2574_);
lean_dec(v___x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2654_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v_toFunctor_2578_; lean_object* v_toSeq_2579_; lean_object* v_toSeqLeft_2580_; lean_object* v_toSeqRight_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2652_; 
v_toFunctor_2578_ = lean_ctor_get(v_toApplicative_2574_, 0);
v_toSeq_2579_ = lean_ctor_get(v_toApplicative_2574_, 2);
v_toSeqLeft_2580_ = lean_ctor_get(v_toApplicative_2574_, 3);
v_toSeqRight_2581_ = lean_ctor_get(v_toApplicative_2574_, 4);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_toApplicative_2574_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v_toApplicative_2574_, 1);
lean_dec(v_unused_2653_);
v___x_2583_ = v_toApplicative_2574_;
v_isShared_2584_ = v_isSharedCheck_2652_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_toSeqRight_2581_);
lean_inc(v_toSeqLeft_2580_);
lean_inc(v_toSeq_2579_);
lean_inc(v_toFunctor_2578_);
lean_dec(v_toApplicative_2574_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2652_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___f_2585_; lean_object* v___f_2586_; lean_object* v___f_2587_; lean_object* v___f_2588_; lean_object* v___x_2589_; lean_object* v___f_2590_; lean_object* v___f_2591_; lean_object* v___f_2592_; lean_object* v___x_2594_; 
v___f_2585_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4));
v___f_2586_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5));
lean_inc_ref(v_toFunctor_2578_);
v___f_2587_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2587_, 0, v_toFunctor_2578_);
v___f_2588_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2588_, 0, v_toFunctor_2578_);
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___f_2587_);
lean_ctor_set(v___x_2589_, 1, v___f_2588_);
v___f_2590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2590_, 0, v_toSeqRight_2581_);
v___f_2591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2591_, 0, v_toSeqLeft_2580_);
v___f_2592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2592_, 0, v_toSeq_2579_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 4, v___f_2590_);
lean_ctor_set(v___x_2583_, 3, v___f_2591_);
lean_ctor_set(v___x_2583_, 2, v___f_2592_);
lean_ctor_set(v___x_2583_, 1, v___f_2585_);
lean_ctor_set(v___x_2583_, 0, v___x_2589_);
v___x_2594_ = v___x_2583_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___f_2585_);
lean_ctor_set(v_reuseFailAlloc_2651_, 2, v___f_2592_);
lean_ctor_set(v_reuseFailAlloc_2651_, 3, v___f_2591_);
lean_ctor_set(v_reuseFailAlloc_2651_, 4, v___f_2590_);
v___x_2594_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2596_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 1, v___f_2586_);
lean_ctor_set(v___x_2576_, 0, v___x_2594_);
v___x_2596_ = v___x_2576_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___f_2586_);
v___x_2596_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; lean_object* v_toApplicative_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2648_; 
v___x_2597_ = l_StateRefT_x27_instMonad___redArg(v___x_2596_);
v_toApplicative_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v___x_2597_, 1);
lean_dec(v_unused_2649_);
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2648_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_toApplicative_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2648_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_toFunctor_2602_; lean_object* v_toSeq_2603_; lean_object* v_toSeqLeft_2604_; lean_object* v_toSeqRight_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2646_; 
v_toFunctor_2602_ = lean_ctor_get(v_toApplicative_2598_, 0);
v_toSeq_2603_ = lean_ctor_get(v_toApplicative_2598_, 2);
v_toSeqLeft_2604_ = lean_ctor_get(v_toApplicative_2598_, 3);
v_toSeqRight_2605_ = lean_ctor_get(v_toApplicative_2598_, 4);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_toApplicative_2598_);
if (v_isSharedCheck_2646_ == 0)
{
lean_object* v_unused_2647_; 
v_unused_2647_ = lean_ctor_get(v_toApplicative_2598_, 1);
lean_dec(v_unused_2647_);
v___x_2607_ = v_toApplicative_2598_;
v_isShared_2608_ = v_isSharedCheck_2646_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_toSeqRight_2605_);
lean_inc(v_toSeqLeft_2604_);
lean_inc(v_toSeq_2603_);
lean_inc(v_toFunctor_2602_);
lean_dec(v_toApplicative_2598_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2646_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___f_2609_; lean_object* v___f_2610_; lean_object* v___f_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___x_2618_; 
v___f_2609_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6));
v___f_2610_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7));
lean_inc_ref(v_toFunctor_2602_);
v___f_2611_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2611_, 0, v_toFunctor_2602_);
v___f_2612_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2612_, 0, v_toFunctor_2602_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___f_2611_);
lean_ctor_set(v___x_2613_, 1, v___f_2612_);
v___f_2614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2614_, 0, v_toSeqRight_2605_);
v___f_2615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2615_, 0, v_toSeqLeft_2604_);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toSeq_2603_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 4, v___f_2614_);
lean_ctor_set(v___x_2607_, 3, v___f_2615_);
lean_ctor_set(v___x_2607_, 2, v___f_2616_);
lean_ctor_set(v___x_2607_, 1, v___f_2609_);
lean_ctor_set(v___x_2607_, 0, v___x_2613_);
v___x_2618_ = v___x_2607_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___f_2609_);
lean_ctor_set(v_reuseFailAlloc_2645_, 2, v___f_2616_);
lean_ctor_set(v_reuseFailAlloc_2645_, 3, v___f_2615_);
lean_ctor_set(v_reuseFailAlloc_2645_, 4, v___f_2614_);
v___x_2618_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2620_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 1, v___f_2610_);
lean_ctor_set(v___x_2600_, 0, v___x_2618_);
v___x_2620_ = v___x_2600_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___f_2610_);
v___x_2620_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2621_ = l_ReaderT_instMonad___redArg(v___x_2620_);
v___x_2622_ = lean_array_get_size(v_acc_2548_);
v___x_2623_ = lean_array_get_size(v_declInfos_2545_);
v___x_2624_ = lean_nat_dec_lt(v___x_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
lean_dec_ref(v___x_2621_);
lean_dec_ref(v_declInfos_2545_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2550_);
lean_inc_ref(v___y_2549_);
v___x_2625_ = lean_apply_9(v_k_2546_, v_acc_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, lean_box(0));
return v___x_2625_;
}
else
{
lean_object* v___f_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___f_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v_snd_2634_; lean_object* v_fst_2635_; lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v___x_2638_; 
v___f_2626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2626_, 0, v___x_2621_);
v___x_2627_ = lean_box(0);
v___x_2628_ = 0;
v___f_2629_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2629_, 0, v___f_2626_);
v___x_2630_ = lean_box(v___x_2628_);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
lean_ctor_set(v___x_2631_, 1, v___f_2629_);
v___x_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2627_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_array_get(v___x_2632_, v_declInfos_2545_, v___x_2622_);
lean_dec_ref(v___x_2632_);
v_snd_2634_ = lean_ctor_get(v___x_2633_, 1);
lean_inc(v_snd_2634_);
v_fst_2635_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_fst_2635_);
lean_dec(v___x_2633_);
v_fst_2636_ = lean_ctor_get(v_snd_2634_, 0);
lean_inc(v_fst_2636_);
v_snd_2637_ = lean_ctor_get(v_snd_2634_, 1);
lean_inc(v_snd_2637_);
lean_dec(v_snd_2634_);
lean_inc(v___y_2555_);
lean_inc_ref(v___y_2554_);
lean_inc(v___y_2553_);
lean_inc_ref(v___y_2552_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2550_);
lean_inc_ref(v___y_2549_);
lean_inc_ref(v_acc_2548_);
v___x_2638_ = lean_apply_9(v_snd_2637_, v_acc_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, lean_box(0));
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; lean_object* v___f_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref(v___x_2638_);
v___x_2640_ = lean_box(v_kind_2547_);
v___f_2641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2641_, 0, v_acc_2548_);
lean_closure_set(v___f_2641_, 1, v_declInfos_2545_);
lean_closure_set(v___f_2641_, 2, v_k_2546_);
lean_closure_set(v___f_2641_, 3, v___x_2640_);
v___x_2642_ = lean_unbox(v_fst_2636_);
lean_dec(v_fst_2636_);
v___x_2643_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_2635_, v___x_2642_, v_a_2639_, v___f_2641_, v_kind_2547_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
return v___x_2643_;
}
else
{
lean_dec(v_fst_2636_);
lean_dec(v_fst_2635_);
lean_dec_ref(v_acc_2548_);
lean_dec_ref(v_k_2546_);
lean_dec_ref(v_declInfos_2545_);
return v___x_2638_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(lean_object* v_acc_2656_, lean_object* v_declInfos_2657_, lean_object* v_k_2658_, uint8_t v_kind_2659_, lean_object* v_x_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = lean_array_push(v_acc_2656_, v_x_2660_);
v___x_2670_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2657_, v_k_2658_, v_kind_2659_, v___x_2669_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object* v_declInfos_2671_, lean_object* v_k_2672_, lean_object* v_kind_2673_, lean_object* v_acc_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v_kind_boxed_2683_; lean_object* v_res_2684_; 
v_kind_boxed_2683_ = lean_unbox(v_kind_2673_);
v_res_2684_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2671_, v_k_2672_, v_kind_boxed_2683_, v_acc_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object* v_declInfos_2687_, lean_object* v_k_2688_, uint8_t v_kind_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0));
v___x_2699_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2687_, v_k_2688_, v_kind_2689_, v___x_2698_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object* v_declInfos_2700_, lean_object* v_k_2701_, lean_object* v_kind_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
uint8_t v_kind_boxed_2711_; lean_object* v_res_2712_; 
v_kind_boxed_2711_ = lean_unbox(v_kind_2702_);
v_res_2712_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_declInfos_2700_, v_k_2701_, v_kind_boxed_2711_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t v_sz_2713_, size_t v_i_2714_, lean_object* v_bs_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = lean_usize_dec_lt(v_i_2714_, v_sz_2713_);
if (v___x_2716_ == 0)
{
return v_bs_2715_;
}
else
{
lean_object* v_v_2717_; lean_object* v_fst_2718_; lean_object* v_snd_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2735_; 
v_v_2717_ = lean_array_uget(v_bs_2715_, v_i_2714_);
v_fst_2718_ = lean_ctor_get(v_v_2717_, 0);
v_snd_2719_ = lean_ctor_get(v_v_2717_, 1);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_v_2717_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2721_ = v_v_2717_;
v_isShared_2722_ = v_isSharedCheck_2735_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_snd_2719_);
lean_inc(v_fst_2718_);
lean_dec(v_v_2717_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2735_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2723_; lean_object* v_bs_x27_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2723_ = lean_unsigned_to_nat(0u);
v_bs_x27_2724_ = lean_array_uset(v_bs_2715_, v_i_2714_, v___x_2723_);
v___x_2725_ = 0;
v___x_2726_ = lean_box(v___x_2725_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v___x_2726_);
v___x_2728_ = v___x_2721_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_snd_2719_);
v___x_2728_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; lean_object* v___x_2732_; 
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v_fst_2718_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_add(v_i_2714_, v___x_2730_);
v___x_2732_ = lean_array_uset(v_bs_x27_2724_, v_i_2714_, v___x_2729_);
v_i_2714_ = v___x_2731_;
v_bs_2715_ = v___x_2732_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_sz_2736_, lean_object* v_i_2737_, lean_object* v_bs_2738_){
_start:
{
size_t v_sz_boxed_2739_; size_t v_i_boxed_2740_; lean_object* v_res_2741_; 
v_sz_boxed_2739_ = lean_unbox_usize(v_sz_2736_);
lean_dec(v_sz_2736_);
v_i_boxed_2740_ = lean_unbox_usize(v_i_2737_);
lean_dec(v_i_2737_);
v_res_2741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_2739_, v_i_boxed_2740_, v_bs_2738_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_2742_, lean_object* v_k_2743_, uint8_t v_kind_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
size_t v_sz_2753_; size_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v_sz_2753_ = lean_array_size(v_declInfos_2742_);
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_2753_, v___x_2754_, v_declInfos_2742_);
v___x_2756_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v___x_2755_, v_k_2743_, v_kind_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_2757_, lean_object* v_k_2758_, lean_object* v_kind_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v_kind_boxed_2768_; lean_object* v_res_2769_; 
v_kind_boxed_2768_ = lean_unbox(v_kind_2759_);
v_res_2769_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_2757_, v_k_2758_, v_kind_boxed_2768_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec_ref(v___y_2760_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_2798_, lean_object* v_dec_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_2798_);
v___x_2809_ = l_Lean_Syntax_isOfKind(v_stx_2798_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec_ref(v_dec_2799_);
lean_dec(v_stx_2798_);
v___x_2810_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2811_ = lean_unsigned_to_nat(1u);
v___x_2812_ = l_Lean_Syntax_getArg(v_stx_2798_, v___x_2811_);
lean_inc(v___x_2812_);
v___x_2813_ = l_Lean_Syntax_matchesNull(v___x_2812_, v___x_2811_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
lean_dec(v___x_2812_);
lean_dec_ref(v_dec_2799_);
lean_dec(v_stx_2798_);
v___x_2814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; uint8_t v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; uint8_t v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v_fst_2886_; lean_object* v_snd_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; uint8_t v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; uint8_t v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; uint8_t v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; 
v___x_2815_ = lean_unsigned_to_nat(0u);
v___x_2816_ = l_Lean_Syntax_getArg(v___x_2812_, v___x_2815_);
lean_dec(v___x_2812_);
v___x_2817_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_2816_);
v___x_2818_ = l_Lean_Syntax_isOfKind(v___x_2816_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_3086_; 
lean_dec(v___x_2816_);
lean_dec_ref(v_dec_2799_);
lean_dec(v_stx_2798_);
v___x_3086_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3086_;
}
else
{
lean_object* v_tk_3087_; lean_object* v_h_x3f_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_tk_3087_ = l_Lean_Syntax_getArg(v_stx_2798_, v___x_2815_);
v___x_3221_ = l_Lean_Syntax_getArg(v___x_2816_, v___x_2815_);
v___x_3222_ = l_Lean_Syntax_isNone(v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3223_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3221_);
v___x_3224_ = l_Lean_Syntax_matchesNull(v___x_3221_, v___x_3223_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
lean_dec(v___x_3221_);
lean_dec(v_tk_3087_);
lean_dec(v___x_2816_);
lean_dec_ref(v_dec_2799_);
lean_dec(v_stx_2798_);
v___x_3225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3225_;
}
else
{
lean_object* v_h_x3f_3226_; lean_object* v___x_3227_; 
v_h_x3f_3226_ = l_Lean_Syntax_getArg(v___x_3221_, v___x_2815_);
lean_dec(v___x_3221_);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_h_x3f_3226_);
v_h_x3f_3089_ = v___x_3227_;
v___y_3090_ = v_a_2800_;
v___y_3091_ = v_a_2801_;
v___y_3092_ = v_a_2802_;
v___y_3093_ = v_a_2803_;
v___y_3094_ = v_a_2804_;
v___y_3095_ = v_a_2805_;
v___y_3096_ = v_a_2806_;
goto v___jp_3088_;
}
}
else
{
lean_object* v___x_3228_; 
lean_dec(v___x_3221_);
v___x_3228_ = lean_box(0);
v_h_x3f_3089_ = v___x_3228_;
v___y_3090_ = v_a_2800_;
v___y_3091_ = v_a_2801_;
v___y_3092_ = v_a_2802_;
v___y_3093_ = v_a_2803_;
v___y_3094_ = v_a_2804_;
v___y_3095_ = v_a_2805_;
v___y_3096_ = v_a_2806_;
goto v___jp_3088_;
}
v___jp_3088_:
{
lean_object* v_x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_x_3097_ = l_Lean_Syntax_getArg(v___x_2816_, v___x_2811_);
v___x_3098_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
lean_inc(v_x_3097_);
v___x_3099_ = l_Lean_Syntax_isOfKind(v_x_3097_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; 
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
lean_dec(v_tk_3087_);
lean_dec(v___x_2816_);
lean_dec_ref(v_dec_2799_);
lean_dec(v_stx_2798_);
v___x_3100_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_2799_, v_tk_3087_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v_tk_3087_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref(v___x_3101_);
v___x_3103_ = lean_mk_empty_array_with_capacity(v___x_2811_);
lean_inc(v_x_3097_);
v___x_3104_ = lean_array_push(v___x_3103_, v_x_3097_);
v___x_3105_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_3104_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec_ref(v___x_3104_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v___x_3106_; 
lean_dec_ref(v___x_3105_);
v___x_3106_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3108_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref(v___x_3106_);
v___x_3108_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref(v___x_3108_);
lean_inc(v_a_3107_);
v___x_3110_ = l_Lean_Level_succ___override(v_a_3107_);
v___x_3111_ = l_Lean_mkSort(v___x_3110_);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
v___x_3113_ = 0;
v___x_3114_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__12));
v___x_3115_ = l_Lean_Meta_mkFreshExprMVar(v___x_3112_, v___x_3113_, v___x_3114_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3188_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3118_ = v___x_3115_;
v_isShared_3119_ = v_isSharedCheck_3188_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3188_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
lean_inc(v_a_3109_);
v___x_3120_ = l_Lean_Level_succ___override(v_a_3109_);
v___x_3121_ = l_Lean_mkSort(v___x_3120_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set_tag(v___x_3118_, 1);
lean_ctor_set(v___x_3118_, 0, v___x_3121_);
v___x_3123_ = v___x_3118_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__14));
v___x_3125_ = l_Lean_Meta_mkFreshExprMVar(v___x_3123_, v___x_3113_, v___x_3124_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3186_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3186_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3186_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3130_ = lean_unsigned_to_nat(3u);
v___x_3131_ = l_Lean_Syntax_getArg(v___x_2816_, v___x_3130_);
lean_dec(v___x_2816_);
lean_inc(v_a_3126_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set_tag(v___x_3128_, 1);
v___x_3133_ = v___x_3128_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3126_);
v___x_3133_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_3131_, v___x_3133_, v___x_2818_, v___x_2818_, v___x_3134_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v_body_3137_; lean_object* v___x_3138_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3135_);
v_body_3137_ = l_Lean_Syntax_getArg(v_stx_2798_, v___x_3130_);
lean_dec(v_stx_2798_);
lean_inc(v_body_3137_);
v___x_3138_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_3137_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3140_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref(v___x_3138_);
v___x_3140_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_3090_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref(v___x_3140_);
v___x_3142_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__16));
v___x_3143_ = l_Lean_Core_mkFreshUserName(v___x_3142_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v_monadInfo_3145_; lean_object* v_mutVars_3146_; lean_object* v___f_3147_; lean_object* v___f_3148_; lean_object* v___x_3149_; lean_object* v___f_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3143_);
v_monadInfo_3145_ = lean_ctor_get(v___y_3090_, 0);
v_mutVars_3146_ = lean_ctor_get(v___y_3090_, 1);
lean_inc(v_a_3116_);
v___f_3147_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3147_, 0, v_a_3116_);
lean_inc_ref(v___f_3147_);
lean_inc(v_x_3097_);
v___f_3148_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 5, 3);
lean_closure_set(v___f_3148_, 0, v_x_3097_);
lean_closure_set(v___f_3148_, 1, v___f_3147_);
lean_closure_set(v___f_3148_, 2, v___x_2811_);
v___x_3149_ = lean_box(v___x_2818_);
lean_inc(v_a_3141_);
v___f_3150_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 12, 3);
lean_closure_set(v___f_3150_, 0, v_a_3141_);
lean_closure_set(v___f_3150_, 1, v___x_2811_);
lean_closure_set(v___f_3150_, 2, v___x_3149_);
v___x_3151_ = lean_array_get_size(v_mutVars_3146_);
v___x_3152_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_3153_ = lean_nat_dec_lt(v___x_2815_, v___x_3151_);
if (v___x_3153_ == 0)
{
lean_inc(v_x_3097_);
lean_inc(v_a_3136_);
lean_inc(v_a_3107_);
lean_inc(v_a_3126_);
lean_inc(v_h_x3f_3089_);
lean_inc(v_a_3116_);
lean_inc(v_a_3109_);
lean_inc(v_a_3144_);
v___y_3039_ = v_body_3137_;
v___y_3040_ = v_a_3144_;
v___y_3041_ = v_monadInfo_3145_;
v___y_3042_ = v_a_3109_;
v___y_3043_ = v_a_3141_;
v___y_3044_ = v___x_3099_;
v___y_3045_ = v_a_3116_;
v___y_3046_ = v_h_x3f_3089_;
v___y_3047_ = v_a_3126_;
v___y_3048_ = v_a_3107_;
v___y_3049_ = v_a_3102_;
v___y_3050_ = v___f_3147_;
v___y_3051_ = v___f_3150_;
v___y_3052_ = v_a_3136_;
v___y_3053_ = v_x_3097_;
v___y_3054_ = v___f_3148_;
v___y_3055_ = v_a_3139_;
v___y_3056_ = v___y_3096_;
v___y_3057_ = v___y_3094_;
v___y_3058_ = v_a_3144_;
v___y_3059_ = v_a_3109_;
v___y_3060_ = v___y_3090_;
v___y_3061_ = v___y_3093_;
v___y_3062_ = v_a_3116_;
v___y_3063_ = v_h_x3f_3089_;
v___y_3064_ = v___x_3113_;
v___y_3065_ = v_a_3126_;
v___y_3066_ = v_a_3107_;
v___y_3067_ = v___y_3091_;
v___y_3068_ = v_a_3136_;
v___y_3069_ = v_x_3097_;
v___y_3070_ = v___y_3092_;
v___y_3071_ = v___y_3095_;
v___y_3072_ = v___x_3152_;
goto v___jp_3038_;
}
else
{
uint8_t v___x_3154_; 
v___x_3154_ = lean_nat_dec_le(v___x_3151_, v___x_3151_);
if (v___x_3154_ == 0)
{
if (v___x_3153_ == 0)
{
lean_inc(v_x_3097_);
lean_inc(v_a_3136_);
lean_inc(v_a_3107_);
lean_inc(v_a_3126_);
lean_inc(v_h_x3f_3089_);
lean_inc(v_a_3116_);
lean_inc(v_a_3109_);
lean_inc(v_a_3144_);
v___y_3039_ = v_body_3137_;
v___y_3040_ = v_a_3144_;
v___y_3041_ = v_monadInfo_3145_;
v___y_3042_ = v_a_3109_;
v___y_3043_ = v_a_3141_;
v___y_3044_ = v___x_3099_;
v___y_3045_ = v_a_3116_;
v___y_3046_ = v_h_x3f_3089_;
v___y_3047_ = v_a_3126_;
v___y_3048_ = v_a_3107_;
v___y_3049_ = v_a_3102_;
v___y_3050_ = v___f_3147_;
v___y_3051_ = v___f_3150_;
v___y_3052_ = v_a_3136_;
v___y_3053_ = v_x_3097_;
v___y_3054_ = v___f_3148_;
v___y_3055_ = v_a_3139_;
v___y_3056_ = v___y_3096_;
v___y_3057_ = v___y_3094_;
v___y_3058_ = v_a_3144_;
v___y_3059_ = v_a_3109_;
v___y_3060_ = v___y_3090_;
v___y_3061_ = v___y_3093_;
v___y_3062_ = v_a_3116_;
v___y_3063_ = v_h_x3f_3089_;
v___y_3064_ = v___x_3113_;
v___y_3065_ = v_a_3126_;
v___y_3066_ = v_a_3107_;
v___y_3067_ = v___y_3091_;
v___y_3068_ = v_a_3136_;
v___y_3069_ = v_x_3097_;
v___y_3070_ = v___y_3092_;
v___y_3071_ = v___y_3095_;
v___y_3072_ = v___x_3152_;
goto v___jp_3038_;
}
else
{
size_t v___x_3155_; size_t v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = ((size_t)0ULL);
v___x_3156_ = lean_usize_of_nat(v___x_3151_);
v___x_3157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_3139_, v_mutVars_3146_, v___x_3155_, v___x_3156_, v___x_3152_);
lean_inc(v_x_3097_);
lean_inc(v_a_3136_);
lean_inc(v_a_3107_);
lean_inc(v_a_3126_);
lean_inc(v_h_x3f_3089_);
lean_inc(v_a_3116_);
lean_inc(v_a_3109_);
lean_inc(v_a_3144_);
v___y_3039_ = v_body_3137_;
v___y_3040_ = v_a_3144_;
v___y_3041_ = v_monadInfo_3145_;
v___y_3042_ = v_a_3109_;
v___y_3043_ = v_a_3141_;
v___y_3044_ = v___x_3099_;
v___y_3045_ = v_a_3116_;
v___y_3046_ = v_h_x3f_3089_;
v___y_3047_ = v_a_3126_;
v___y_3048_ = v_a_3107_;
v___y_3049_ = v_a_3102_;
v___y_3050_ = v___f_3147_;
v___y_3051_ = v___f_3150_;
v___y_3052_ = v_a_3136_;
v___y_3053_ = v_x_3097_;
v___y_3054_ = v___f_3148_;
v___y_3055_ = v_a_3139_;
v___y_3056_ = v___y_3096_;
v___y_3057_ = v___y_3094_;
v___y_3058_ = v_a_3144_;
v___y_3059_ = v_a_3109_;
v___y_3060_ = v___y_3090_;
v___y_3061_ = v___y_3093_;
v___y_3062_ = v_a_3116_;
v___y_3063_ = v_h_x3f_3089_;
v___y_3064_ = v___x_3113_;
v___y_3065_ = v_a_3126_;
v___y_3066_ = v_a_3107_;
v___y_3067_ = v___y_3091_;
v___y_3068_ = v_a_3136_;
v___y_3069_ = v_x_3097_;
v___y_3070_ = v___y_3092_;
v___y_3071_ = v___y_3095_;
v___y_3072_ = v___x_3157_;
goto v___jp_3038_;
}
}
else
{
size_t v___x_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = ((size_t)0ULL);
v___x_3159_ = lean_usize_of_nat(v___x_3151_);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_3139_, v_mutVars_3146_, v___x_3158_, v___x_3159_, v___x_3152_);
lean_inc(v_x_3097_);
lean_inc(v_a_3136_);
lean_inc(v_a_3107_);
lean_inc(v_a_3126_);
lean_inc(v_h_x3f_3089_);
lean_inc(v_a_3116_);
lean_inc(v_a_3109_);
lean_inc(v_a_3144_);
v___y_3039_ = v_body_3137_;
v___y_3040_ = v_a_3144_;
v___y_3041_ = v_monadInfo_3145_;
v___y_3042_ = v_a_3109_;
v___y_3043_ = v_a_3141_;
v___y_3044_ = v___x_3099_;
v___y_3045_ = v_a_3116_;
v___y_3046_ = v_h_x3f_3089_;
v___y_3047_ = v_a_3126_;
v___y_3048_ = v_a_3107_;
v___y_3049_ = v_a_3102_;
v___y_3050_ = v___f_3147_;
v___y_3051_ = v___f_3150_;
v___y_3052_ = v_a_3136_;
v___y_3053_ = v_x_3097_;
v___y_3054_ = v___f_3148_;
v___y_3055_ = v_a_3139_;
v___y_3056_ = v___y_3096_;
v___y_3057_ = v___y_3094_;
v___y_3058_ = v_a_3144_;
v___y_3059_ = v_a_3109_;
v___y_3060_ = v___y_3090_;
v___y_3061_ = v___y_3093_;
v___y_3062_ = v_a_3116_;
v___y_3063_ = v_h_x3f_3089_;
v___y_3064_ = v___x_3113_;
v___y_3065_ = v_a_3126_;
v___y_3066_ = v_a_3107_;
v___y_3067_ = v___y_3091_;
v___y_3068_ = v_a_3136_;
v___y_3069_ = v_x_3097_;
v___y_3070_ = v___y_3092_;
v___y_3071_ = v___y_3095_;
v___y_3072_ = v___x_3160_;
goto v___jp_3038_;
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_a_3141_);
lean_dec(v_a_3139_);
lean_dec(v_body_3137_);
lean_dec(v_a_3136_);
lean_dec(v_a_3126_);
lean_dec(v_a_3116_);
lean_dec(v_a_3109_);
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
v_a_3161_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3143_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3143_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_a_3139_);
lean_dec(v_body_3137_);
lean_dec(v_a_3136_);
lean_dec(v_a_3126_);
lean_dec(v_a_3116_);
lean_dec(v_a_3109_);
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
v_a_3169_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3140_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3140_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v_body_3137_);
lean_dec(v_a_3136_);
lean_dec(v_a_3126_);
lean_dec(v_a_3116_);
lean_dec(v_a_3109_);
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
v_a_3177_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3138_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3138_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_dec(v_a_3126_);
lean_dec(v_a_3116_);
lean_dec(v_a_3109_);
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
lean_dec(v_stx_2798_);
return v___x_3135_;
}
}
}
}
else
{
lean_dec(v_a_3116_);
lean_dec(v_a_3109_);
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
lean_dec(v___x_2816_);
lean_dec(v_stx_2798_);
return v___x_3125_;
}
}
}
}
else
{
lean_dec(v_a_3109_);
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
lean_dec(v___x_2816_);
lean_dec(v_stx_2798_);
return v___x_3115_;
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v_a_3107_);
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
lean_dec(v___x_2816_);
lean_dec(v_stx_2798_);
v_a_3189_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3108_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3108_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
lean_dec(v___x_2816_);
lean_dec(v_stx_2798_);
v_a_3197_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3106_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3106_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec(v_a_3102_);
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
lean_dec(v___x_2816_);
lean_dec(v_stx_2798_);
v_a_3205_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3105_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3105_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_x_3097_);
lean_dec(v_h_x3f_3089_);
lean_dec(v___x_2816_);
lean_dec(v_stx_2798_);
v_a_3213_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3101_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3101_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
}
v___jp_2819_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___f_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; 
v___x_2846_ = l_Lean_instInhabitedExpr;
v___x_2847_ = lean_box(v___x_2818_);
lean_inc(v___y_2828_);
lean_inc(v___y_2835_);
lean_inc(v___y_2823_);
lean_inc_ref(v___y_2831_);
lean_inc_ref(v___y_2825_);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 24, 15);
lean_closure_set(v___f_2848_, 0, v___x_2846_);
lean_closure_set(v___f_2848_, 1, v___x_2815_);
lean_closure_set(v___f_2848_, 2, v___y_2833_);
lean_closure_set(v___f_2848_, 3, v___y_2825_);
lean_closure_set(v___f_2848_, 4, v___y_2831_);
lean_closure_set(v___f_2848_, 5, v___y_2823_);
lean_closure_set(v___f_2848_, 6, v___y_2826_);
lean_closure_set(v___f_2848_, 7, v___y_2824_);
lean_closure_set(v___f_2848_, 8, v___y_2834_);
lean_closure_set(v___f_2848_, 9, v___y_2821_);
lean_closure_set(v___f_2848_, 10, v___x_2847_);
lean_closure_set(v___f_2848_, 11, v___y_2835_);
lean_closure_set(v___f_2848_, 12, v___y_2828_);
lean_closure_set(v___f_2848_, 13, v___y_2829_);
lean_closure_set(v___f_2848_, 14, v___x_2811_);
v___x_2849_ = 0;
v___x_2850_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_2845_, v___f_2848_, v___x_2849_, v___y_2838_, v___y_2840_, v___y_2843_, v___y_2844_, v___y_2842_, v___y_2837_, v___y_2841_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v_doBlockResultType_2852_; lean_object* v___x_2853_; lean_object* v___y_2854_; lean_object* v___x_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2850_);
v_doBlockResultType_2852_ = lean_ctor_get(v___y_2838_, 3);
v___x_2853_ = lean_box(v___y_2827_);
lean_inc(v___y_2820_);
lean_inc_ref(v_doBlockResultType_2852_);
v___y_2854_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 11);
lean_closure_set(v___y_2854_, 0, v___x_2853_);
lean_closure_set(v___y_2854_, 1, v___y_2831_);
lean_closure_set(v___y_2854_, 2, v___y_2822_);
lean_closure_set(v___y_2854_, 3, v_doBlockResultType_2852_);
lean_closure_set(v___y_2854_, 4, v___y_2825_);
lean_closure_set(v___y_2854_, 5, v___y_2820_);
lean_closure_set(v___y_2854_, 6, v___y_2823_);
lean_closure_set(v___y_2854_, 7, v___y_2832_);
lean_closure_set(v___y_2854_, 8, v___y_2830_);
lean_closure_set(v___y_2854_, 9, v___x_2815_);
lean_closure_set(v___y_2854_, 10, v___x_2811_);
v___x_2855_ = lean_box(v___x_2818_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 13, 4);
lean_closure_set(v___f_2856_, 0, v___y_2835_);
lean_closure_set(v___f_2856_, 1, v___y_2854_);
lean_closure_set(v___f_2856_, 2, v___x_2811_);
lean_closure_set(v___f_2856_, 3, v___x_2855_);
lean_inc_ref(v___y_2836_);
v___x_2857_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v___y_2828_, v___y_2836_, v___f_2856_, v___y_2838_, v___y_2840_, v___y_2843_, v___y_2844_, v___y_2842_, v___y_2837_, v___y_2841_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2857_);
v___x_2859_ = l_Lean_Expr_app___override(v___y_2839_, v_a_2851_);
lean_inc_ref(v_doBlockResultType_2852_);
v___x_2860_ = l_Lean_Elab_Do_mkBindApp(v___y_2836_, v_doBlockResultType_2852_, v___x_2859_, v_a_2858_, v___y_2838_, v___y_2840_, v___y_2843_, v___y_2844_, v___y_2842_, v___y_2837_, v___y_2841_);
return v___x_2860_;
}
else
{
lean_dec(v_a_2851_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___y_2836_);
return v___x_2857_;
}
}
else
{
lean_dec_ref(v___y_2839_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2823_);
lean_dec(v___y_2822_);
return v___x_2850_;
}
}
v___jp_2861_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_2896_ = l_Lean_Core_mkFreshUserName(v___x_2895_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2896_) == 0)
{
if (lean_obj_tag(v___y_2882_) == 1)
{
if (lean_obj_tag(v_snd_2887_) == 1)
{
lean_object* v_a_2897_; lean_object* v_val_2898_; lean_object* v_val_2899_; lean_object* v___f_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
lean_dec_ref(v___y_2885_);
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___x_2896_);
v_val_2898_ = lean_ctor_get(v___y_2882_, 0);
lean_inc(v_val_2898_);
lean_dec_ref(v___y_2882_);
v_val_2899_ = lean_ctor_get(v_snd_2887_, 0);
lean_inc(v_val_2899_);
lean_dec_ref(v_snd_2887_);
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_2900_, 0, v___y_2865_);
lean_closure_set(v___f_2900_, 1, v___y_2875_);
lean_closure_set(v___f_2900_, 2, v___x_2815_);
lean_closure_set(v___f_2900_, 3, v___y_2868_);
lean_closure_set(v___f_2900_, 4, v___y_2874_);
lean_closure_set(v___f_2900_, 5, v_val_2899_);
lean_closure_set(v___f_2900_, 6, v___y_2878_);
v___x_2901_ = l_Lean_TSyntax_getId(v___y_2884_);
lean_dec(v___y_2884_);
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
lean_ctor_set(v___x_2902_, 1, v___y_2883_);
v___x_2903_ = l_Lean_TSyntax_getId(v_val_2898_);
lean_dec(v_val_2898_);
v___x_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
lean_ctor_set(v___x_2904_, 1, v___f_2900_);
v___x_2905_ = lean_unsigned_to_nat(2u);
v___x_2906_ = lean_mk_empty_array_with_capacity(v___x_2905_);
v___x_2907_ = lean_array_push(v___x_2906_, v___x_2902_);
v___x_2908_ = lean_array_push(v___x_2907_, v___x_2904_);
lean_inc_ref(v___y_2870_);
v___y_2820_ = v___y_2862_;
v___y_2821_ = v___y_2863_;
v___y_2822_ = v___y_2864_;
v___y_2823_ = v___y_2866_;
v___y_2824_ = v___y_2867_;
v___y_2825_ = v___y_2869_;
v___y_2826_ = v___y_2870_;
v___y_2827_ = v___y_2871_;
v___y_2828_ = v_a_2897_;
v___y_2829_ = v___y_2872_;
v___y_2830_ = v___y_2873_;
v___y_2831_ = v___y_2876_;
v___y_2832_ = v___y_2877_;
v___y_2833_ = v___y_2879_;
v___y_2834_ = v___y_2881_;
v___y_2835_ = v___y_2880_;
v___y_2836_ = v___y_2870_;
v___y_2837_ = v___y_2893_;
v___y_2838_ = v___y_2888_;
v___y_2839_ = v_fst_2886_;
v___y_2840_ = v___y_2889_;
v___y_2841_ = v___y_2894_;
v___y_2842_ = v___y_2892_;
v___y_2843_ = v___y_2890_;
v___y_2844_ = v___y_2891_;
v___y_2845_ = v___x_2908_;
goto v___jp_2819_;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2910_; 
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2865_);
v_a_2909_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2896_);
v___x_2910_ = lean_apply_2(v___y_2885_, v___y_2882_, v_snd_2887_);
lean_inc_ref(v___y_2870_);
v___y_2820_ = v___y_2862_;
v___y_2821_ = v___y_2863_;
v___y_2822_ = v___y_2864_;
v___y_2823_ = v___y_2866_;
v___y_2824_ = v___y_2867_;
v___y_2825_ = v___y_2869_;
v___y_2826_ = v___y_2870_;
v___y_2827_ = v___y_2871_;
v___y_2828_ = v_a_2909_;
v___y_2829_ = v___y_2872_;
v___y_2830_ = v___y_2873_;
v___y_2831_ = v___y_2876_;
v___y_2832_ = v___y_2877_;
v___y_2833_ = v___y_2879_;
v___y_2834_ = v___y_2881_;
v___y_2835_ = v___y_2880_;
v___y_2836_ = v___y_2870_;
v___y_2837_ = v___y_2893_;
v___y_2838_ = v___y_2888_;
v___y_2839_ = v_fst_2886_;
v___y_2840_ = v___y_2889_;
v___y_2841_ = v___y_2894_;
v___y_2842_ = v___y_2892_;
v___y_2843_ = v___y_2890_;
v___y_2844_ = v___y_2891_;
v___y_2845_ = v___x_2910_;
goto v___jp_2819_;
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2912_; 
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2865_);
v_a_2911_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2896_);
v___x_2912_ = lean_apply_2(v___y_2885_, v___y_2882_, v_snd_2887_);
lean_inc_ref(v___y_2870_);
v___y_2820_ = v___y_2862_;
v___y_2821_ = v___y_2863_;
v___y_2822_ = v___y_2864_;
v___y_2823_ = v___y_2866_;
v___y_2824_ = v___y_2867_;
v___y_2825_ = v___y_2869_;
v___y_2826_ = v___y_2870_;
v___y_2827_ = v___y_2871_;
v___y_2828_ = v_a_2911_;
v___y_2829_ = v___y_2872_;
v___y_2830_ = v___y_2873_;
v___y_2831_ = v___y_2876_;
v___y_2832_ = v___y_2877_;
v___y_2833_ = v___y_2879_;
v___y_2834_ = v___y_2881_;
v___y_2835_ = v___y_2880_;
v___y_2836_ = v___y_2870_;
v___y_2837_ = v___y_2893_;
v___y_2838_ = v___y_2888_;
v___y_2839_ = v_fst_2886_;
v___y_2840_ = v___y_2889_;
v___y_2841_ = v___y_2894_;
v___y_2842_ = v___y_2892_;
v___y_2843_ = v___y_2890_;
v___y_2844_ = v___y_2891_;
v___y_2845_ = v___x_2912_;
goto v___jp_2819_;
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_snd_2887_);
lean_dec_ref(v_fst_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
v_a_2913_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2896_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2896_);
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
v___jp_2921_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_box(0);
lean_inc_ref(v___y_2925_);
lean_inc(v___y_2937_);
lean_inc_ref(v___y_2953_);
lean_inc(v___y_2938_);
lean_inc_ref(v___y_2942_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2948_);
v___x_2957_ = lean_apply_8(v___y_2925_, v___x_2956_, v___y_2948_, v___y_2951_, v___y_2942_, v___y_2938_, v___y_2953_, v___y_2937_, lean_box(0));
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v_m_2959_; lean_object* v_u_2960_; lean_object* v_v_2961_; lean_object* v___x_2962_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2957_);
v_m_2959_ = lean_ctor_get(v___y_2939_, 0);
v_u_2960_ = lean_ctor_get(v___y_2939_, 1);
v_v_2961_ = lean_ctor_get(v___y_2939_, 2);
lean_inc(v_u_2960_);
v___x_2962_ = l_Lean_Meta_mkProdMkN(v_a_2958_, v_u_2960_, v___y_2942_, v___y_2938_, v___y_2953_, v___y_2937_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref(v___x_2962_);
if (lean_obj_tag(v___y_2944_) == 0)
{
lean_object* v_fst_2964_; lean_object* v_snd_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2984_; 
v_fst_2964_ = lean_ctor_get(v_a_2963_, 0);
v_snd_2965_ = lean_ctor_get(v_a_2963_, 1);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_a_2963_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2967_ = v_a_2963_;
v_isShared_2968_ = v_isSharedCheck_2984_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_snd_2965_);
lean_inc(v_fst_2964_);
lean_dec(v_a_2963_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2984_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__1));
v___x_2970_ = lean_box(0);
lean_inc(v_v_2961_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 1);
lean_ctor_set(v___x_2967_, 1, v___x_2970_);
lean_ctor_set(v___x_2967_, 0, v_v_2961_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_v_2961_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_inc(v_u_2960_);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v_u_2960_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___y_2947_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___y_2940_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
lean_inc_ref(v___x_2975_);
v___x_2976_ = l_Lean_mkConst(v___x_2969_, v___x_2975_);
lean_inc_ref(v___y_2943_);
lean_inc_ref(v___y_2946_);
lean_inc_ref(v_m_2959_);
v___x_2977_ = l_Lean_mkApp3(v___x_2976_, v_m_2959_, v___y_2946_, v___y_2943_);
v___x_2978_ = l_Lean_Elab_Term_mkInstMVar(v___x_2977_, v___x_2956_, v___y_2948_, v___y_2951_, v___y_2942_, v___y_2938_, v___y_2953_, v___y_2937_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref(v___x_2978_);
v___x_2980_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_2981_ = l_Lean_mkConst(v___x_2980_, v___x_2975_);
lean_inc(v_snd_2965_);
lean_inc_ref(v_m_2959_);
v___x_2982_ = l_Lean_mkApp7(v___x_2981_, v_m_2959_, v___y_2946_, v___y_2943_, v_a_2979_, v_snd_2965_, v___y_2950_, v_fst_2964_);
lean_inc(v_u_2960_);
v___y_2862_ = v_v_2961_;
v___y_2863_ = v___y_2922_;
v___y_2864_ = v___y_2923_;
v___y_2865_ = v___y_2924_;
v___y_2866_ = v_u_2960_;
v___y_2867_ = v___y_2925_;
v___y_2868_ = v___y_2926_;
v___y_2869_ = v___y_2927_;
v___y_2870_ = v_snd_2965_;
v___y_2871_ = v___y_2928_;
v___y_2872_ = v___y_2929_;
v___y_2873_ = v___y_2930_;
v___y_2874_ = v___y_2931_;
v___y_2875_ = v___y_2932_;
v___y_2876_ = v___y_2933_;
v___y_2877_ = v___y_2934_;
v___y_2878_ = v___y_2935_;
v___y_2879_ = v___y_2936_;
v___y_2880_ = v___y_2955_;
v___y_2881_ = v___x_2956_;
v___y_2882_ = v___y_2944_;
v___y_2883_ = v___y_2949_;
v___y_2884_ = v___y_2952_;
v___y_2885_ = v___y_2954_;
v_fst_2886_ = v___x_2982_;
v_snd_2887_ = v___x_2956_;
v___y_2888_ = v___y_2941_;
v___y_2889_ = v___y_2948_;
v___y_2890_ = v___y_2951_;
v___y_2891_ = v___y_2942_;
v___y_2892_ = v___y_2938_;
v___y_2893_ = v___y_2953_;
v___y_2894_ = v___y_2937_;
goto v___jp_2861_;
}
else
{
lean_dec_ref(v___x_2975_);
lean_dec(v_snd_2965_);
lean_dec(v_fst_2964_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2946_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
return v___x_2978_;
}
}
}
}
else
{
lean_object* v_fst_2985_; lean_object* v_snd_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3021_; 
v_fst_2985_ = lean_ctor_get(v_a_2963_, 0);
v_snd_2986_ = lean_ctor_get(v_a_2963_, 1);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_a_2963_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2988_ = v_a_2963_;
v_isShared_2989_ = v_isSharedCheck_3021_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_snd_2986_);
lean_inc(v_fst_2985_);
lean_dec(v_a_2963_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3021_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2990_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__4));
v___x_2991_ = lean_box(0);
lean_inc(v___y_2940_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set_tag(v___x_2988_, 1);
lean_ctor_set(v___x_2988_, 1, v___x_2991_);
lean_ctor_set(v___x_2988_, 0, v___y_2940_);
v___x_2993_ = v___x_2988_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___y_2940_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_3020_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_inc(v___y_2947_);
v___x_2994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2994_, 0, v___y_2947_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = l_Lean_mkConst(v___x_2990_, v___x_2994_);
lean_inc_ref(v___y_2946_);
lean_inc_ref(v___y_2943_);
v___x_2996_ = l_Lean_mkAppB(v___x_2995_, v___y_2943_, v___y_2946_);
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
v___x_2998_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
v___x_2999_ = l_Lean_Meta_mkFreshExprMVar(v___x_2997_, v___y_2945_, v___x_2998_, v___y_2942_, v___y_2938_, v___y_2953_, v___y_2937_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_n(v_a_3000_, 2);
lean_dec_ref(v___x_2999_);
v___x_3001_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
lean_inc(v_v_2961_);
v___x_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_v_2961_);
lean_ctor_set(v___x_3002_, 1, v___x_2991_);
lean_inc(v_u_2960_);
v___x_3003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3003_, 0, v_u_2960_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___y_2947_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___y_2940_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
lean_inc_ref(v___x_3005_);
v___x_3006_ = l_Lean_mkConst(v___x_3001_, v___x_3005_);
lean_inc_ref(v___y_2943_);
lean_inc_ref(v___y_2946_);
lean_inc_ref(v_m_2959_);
v___x_3007_ = l_Lean_mkApp4(v___x_3006_, v_m_2959_, v___y_2946_, v___y_2943_, v_a_3000_);
v___x_3008_ = l_Lean_Elab_Term_mkInstMVar(v___x_3007_, v___x_2956_, v___y_2948_, v___y_2951_, v___y_2942_, v___y_2938_, v___y_2953_, v___y_2937_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3019_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3019_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3019_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3013_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_3014_ = l_Lean_mkConst(v___x_3013_, v___x_3005_);
lean_inc(v_snd_2986_);
lean_inc(v_a_3000_);
lean_inc_ref(v_m_2959_);
v___x_3015_ = l_Lean_mkApp8(v___x_3014_, v_m_2959_, v___y_2946_, v___y_2943_, v_a_3000_, v_a_3009_, v_snd_2986_, v___y_2950_, v_fst_2985_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set_tag(v___x_3011_, 1);
lean_ctor_set(v___x_3011_, 0, v_a_3000_);
v___x_3017_ = v___x_3011_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3000_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_inc(v_u_2960_);
v___y_2862_ = v_v_2961_;
v___y_2863_ = v___y_2922_;
v___y_2864_ = v___y_2923_;
v___y_2865_ = v___y_2924_;
v___y_2866_ = v_u_2960_;
v___y_2867_ = v___y_2925_;
v___y_2868_ = v___y_2926_;
v___y_2869_ = v___y_2927_;
v___y_2870_ = v_snd_2986_;
v___y_2871_ = v___y_2928_;
v___y_2872_ = v___y_2929_;
v___y_2873_ = v___y_2930_;
v___y_2874_ = v___y_2931_;
v___y_2875_ = v___y_2932_;
v___y_2876_ = v___y_2933_;
v___y_2877_ = v___y_2934_;
v___y_2878_ = v___y_2935_;
v___y_2879_ = v___y_2936_;
v___y_2880_ = v___y_2955_;
v___y_2881_ = v___x_2956_;
v___y_2882_ = v___y_2944_;
v___y_2883_ = v___y_2949_;
v___y_2884_ = v___y_2952_;
v___y_2885_ = v___y_2954_;
v_fst_2886_ = v___x_3015_;
v_snd_2887_ = v___x_3017_;
v___y_2888_ = v___y_2941_;
v___y_2889_ = v___y_2948_;
v___y_2890_ = v___y_2951_;
v___y_2891_ = v___y_2942_;
v___y_2892_ = v___y_2938_;
v___y_2893_ = v___y_2953_;
v___y_2894_ = v___y_2937_;
goto v___jp_2861_;
}
}
}
else
{
lean_dec_ref(v___x_3005_);
lean_dec(v_a_3000_);
lean_dec(v_snd_2986_);
lean_dec(v_fst_2985_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2946_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
return v___x_3008_;
}
}
else
{
lean_dec(v_snd_2986_);
lean_dec(v_fst_2985_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2940_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
return v___x_2999_;
}
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2940_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
v_a_3022_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2962_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2962_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2940_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
v_a_3030_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2957_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2957_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
v___jp_3038_:
{
uint8_t v_returnsEarly_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___f_3076_; 
v_returnsEarly_3073_ = lean_ctor_get_uint8(v___y_3055_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_3055_);
v___x_3074_ = lean_box(v_returnsEarly_3073_);
v___x_3075_ = lean_box(v___y_3044_);
lean_inc_ref(v___y_3043_);
lean_inc_ref(v___y_3041_);
lean_inc_ref(v___y_3072_);
v___f_3076_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 14, 6);
lean_closure_set(v___f_3076_, 0, v___y_3072_);
lean_closure_set(v___f_3076_, 1, v___y_3041_);
lean_closure_set(v___f_3076_, 2, v___x_3074_);
lean_closure_set(v___f_3076_, 3, v___x_2815_);
lean_closure_set(v___f_3076_, 4, v___y_3043_);
lean_closure_set(v___f_3076_, 5, v___x_3075_);
if (v_returnsEarly_3073_ == 0)
{
size_t v_sz_3077_; size_t v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_dec(v___y_3058_);
v_sz_3077_ = lean_array_size(v___y_3072_);
v___x_3078_ = ((size_t)0ULL);
lean_inc_ref(v___y_3072_);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_3077_, v___x_3078_, v___y_3072_);
v___x_3080_ = lean_array_to_list(v___x_3079_);
v___y_2922_ = v___y_3039_;
v___y_2923_ = v___y_3040_;
v___y_2924_ = v___y_3042_;
v___y_2925_ = v___f_3076_;
v___y_2926_ = v___y_3045_;
v___y_2927_ = v___y_3043_;
v___y_2928_ = v_returnsEarly_3073_;
v___y_2929_ = v___y_3046_;
v___y_2930_ = v___y_3072_;
v___y_2931_ = v___y_3047_;
v___y_2932_ = v___y_3048_;
v___y_2933_ = v___y_3049_;
v___y_2934_ = v___y_3051_;
v___y_2935_ = v___y_3052_;
v___y_2936_ = v___y_3053_;
v___y_2937_ = v___y_3056_;
v___y_2938_ = v___y_3057_;
v___y_2939_ = v___y_3041_;
v___y_2940_ = v___y_3059_;
v___y_2941_ = v___y_3060_;
v___y_2942_ = v___y_3061_;
v___y_2943_ = v___y_3062_;
v___y_2944_ = v___y_3063_;
v___y_2945_ = v___y_3064_;
v___y_2946_ = v___y_3065_;
v___y_2947_ = v___y_3066_;
v___y_2948_ = v___y_3067_;
v___y_2949_ = v___y_3050_;
v___y_2950_ = v___y_3068_;
v___y_2951_ = v___y_3070_;
v___y_2952_ = v___y_3069_;
v___y_2953_ = v___y_3071_;
v___y_2954_ = v___y_3054_;
v___y_2955_ = v___x_3080_;
goto v___jp_2921_;
}
else
{
size_t v_sz_3081_; size_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v_sz_3081_ = lean_array_size(v___y_3072_);
v___x_3082_ = ((size_t)0ULL);
lean_inc_ref(v___y_3072_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_3081_, v___x_3082_, v___y_3072_);
v___x_3084_ = lean_array_to_list(v___x_3083_);
v___x_3085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___y_3058_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___y_2922_ = v___y_3039_;
v___y_2923_ = v___y_3040_;
v___y_2924_ = v___y_3042_;
v___y_2925_ = v___f_3076_;
v___y_2926_ = v___y_3045_;
v___y_2927_ = v___y_3043_;
v___y_2928_ = v_returnsEarly_3073_;
v___y_2929_ = v___y_3046_;
v___y_2930_ = v___y_3072_;
v___y_2931_ = v___y_3047_;
v___y_2932_ = v___y_3048_;
v___y_2933_ = v___y_3049_;
v___y_2934_ = v___y_3051_;
v___y_2935_ = v___y_3052_;
v___y_2936_ = v___y_3053_;
v___y_2937_ = v___y_3056_;
v___y_2938_ = v___y_3057_;
v___y_2939_ = v___y_3041_;
v___y_2940_ = v___y_3059_;
v___y_2941_ = v___y_3060_;
v___y_2942_ = v___y_3061_;
v___y_2943_ = v___y_3062_;
v___y_2944_ = v___y_3063_;
v___y_2945_ = v___y_3064_;
v___y_2946_ = v___y_3065_;
v___y_2947_ = v___y_3066_;
v___y_2948_ = v___y_3067_;
v___y_2949_ = v___y_3050_;
v___y_2950_ = v___y_3068_;
v___y_2951_ = v___y_3070_;
v___y_2952_ = v___y_3069_;
v___y_2953_ = v___y_3071_;
v___y_2954_ = v___y_3054_;
v___y_2955_ = v___x_3085_;
goto v___jp_2921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_3229_, lean_object* v_dec_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_Elab_Do_elabDoFor(v_stx_3229_, v_dec_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec_ref(v_a_3231_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_3240_, lean_object* v_msg_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_3250_, lean_object* v_msg_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_3250_, v_msg_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object* v_00_u03b1_3260_, lean_object* v_name_3261_, lean_object* v_type_3262_, lean_object* v_k_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_3261_, v_type_3262_, v_k_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_00_u03b1_3273_, lean_object* v_name_3274_, lean_object* v_type_3275_, lean_object* v_k_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(v_00_u03b1_3273_, v_name_3274_, v_type_3275_, v_k_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v___y_3277_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object* v_msgData_3286_, lean_object* v_macroStack_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_3286_, v_macroStack_3287_, v___y_3292_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object* v_msgData_3296_, lean_object* v_macroStack_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_3296_, v_macroStack_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3313_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_3314_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_3316_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_3317_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3313_, v___x_3314_, v___x_3315_, v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_3319_;
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
