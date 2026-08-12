// Lean compiler output
// Module: Lean.Elab.BuiltinDo.For
// Imports: public import Lean.Elab.BuiltinDo.Basic meta import Lean.Parser.Do import Init.Control.Do import Init.While import Lean.Meta.ProdN
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
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProdMkN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkPureApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_enterLoopBody___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_bindMutVarsFromTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Do_MutVar_getId(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkBindApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 98, .m_capacity = 98, .m_length = 95, .m_data = "The `invariant` clause is only supported on `for x in xs do …` with a single identifier binder."};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "doForInvariant"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value),LEAN_SCALAR_PTR_LITERAL(21, 233, 74, 150, 27, 16, 165, 242)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__17 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__18 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__18_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__19 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expandDoFor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 157, 21, 52, 135, 185, 36, 254)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "the `invariant` clause elaborates to a `vcgen` gadget; add `import Std.Internal.Do` to use it."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ForIn"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "forInWithInvariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(1, 144, 23, 37, 138, 194, 167, 30)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__7_value),LEAN_SCALAR_PTR_LITERAL(216, 106, 59, 179, 156, 229, 113, 6)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ForIn'"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "forInWithInvariant'"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12_value),LEAN_SCALAR_PTR_LITERAL(213, 93, 110, 114, 180, 94, 138, 151)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value),LEAN_SCALAR_PTR_LITERAL(190, 73, 23, 142, 83, 242, 60, 31)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__18 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Break"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "runK"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "match_1"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 204, 143, 3, 84, 67, 92, 151)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 178, 64, 100, 79, 118, 122, 28)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 194, 234, 57, 172, 104, 157, 179)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__8_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "yield"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ForInStep"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 23, 255, 201, 194, 179, 65, 111)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mem"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 90, 126, 237, 128, 148, 153, 69)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "forIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 12, 142, 239, 44, 138, 10, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 234, 148, 175, 115, 149, 2, 231)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value),LEAN_SCALAR_PTR_LITERAL(10, 254, 232, 131, 195, 189, 138, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "ρ"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value),LEAN_SCALAR_PTR_LITERAL(148, 87, 172, 24, 54, 35, 28, 246)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value),LEAN_SCALAR_PTR_LITERAL(38, 26, 183, 93, 43, 136, 227, 87)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__14_value;
static const lean_array_object l_Lean_Elab_Do_elabDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_192254__boxed_428_; lean_object* v_res_429_; 
v___x_192254__boxed_428_ = lean_unbox(v___x_416_);
v_res_429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_413_, v___x_414_, v___x_415_, v___x_192254__boxed_428_, v___x_417_, v___x_418_, v___x_419_, v___f_420_, v_fst_421_, v___x_422_, v_snd_423_, v_x_424_, v_h_x3f_425_, v___y_426_, v___y_427_);
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
uint8_t v___x_192860__boxed_440_; lean_object* v_res_441_; 
v___x_192860__boxed_440_ = lean_unbox(v___x_436_);
v_res_441_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(v___x_192860__boxed_440_, v_____do__lift_437_, v___y_438_, v___y_439_);
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
uint8_t v___x_192896__boxed_559_; lean_object* v_res_560_; 
v___x_192896__boxed_559_ = lean_unbox(v___x_554_);
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_192896__boxed_559_, v_a_555_, v_b_556_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(uint8_t v___x_561_, lean_object* v_a_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_array_566_; lean_object* v_start_567_; lean_object* v_stop_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_662_; 
v_array_566_ = lean_ctor_get(v_a_562_, 0);
v_start_567_ = lean_ctor_get(v_a_562_, 1);
v_stop_568_ = lean_ctor_get(v_a_562_, 2);
v_isSharedCheck_662_ = !lean_is_exclusive(v_a_562_);
if (v_isSharedCheck_662_ == 0)
{
v___x_570_ = v_a_562_;
v_isShared_571_ = v_isSharedCheck_662_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_stop_568_);
lean_inc(v_start_567_);
lean_inc(v_array_566_);
lean_dec(v_a_562_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_662_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint8_t v___x_572_; 
v___x_572_ = lean_nat_dec_lt(v_start_567_, v_stop_568_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_del_object(v___x_570_);
lean_dec(v_stop_568_);
lean_dec(v_start_567_);
lean_dec_ref(v_array_566_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_b_563_);
lean_ctor_set(v___x_573_, 1, v___y_565_);
return v___x_573_;
}
else
{
lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_661_; 
v_fst_574_ = lean_ctor_get(v_b_563_, 0);
v_snd_575_ = lean_ctor_get(v_b_563_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_b_563_);
if (v_isSharedCheck_661_ == 0)
{
v___x_577_ = v_b_563_;
v_isShared_578_ = v_isSharedCheck_661_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_574_);
lean_dec(v_b_563_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_661_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_581_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_583_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v___x_584_ = lean_nat_add(v_start_567_, v___x_579_);
lean_inc_ref(v_array_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_584_);
v___x_586_ = v___x_570_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_array_566_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_stop_568_);
v___x_586_ = v_reuseFailAlloc_660_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___y_588_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_fget(v_array_566_, v_start_567_);
lean_dec(v_start_567_);
lean_dec_ref(v_array_566_);
lean_inc(v___x_612_);
v___x_613_ = l_Lean_Syntax_isOfKind(v___x_612_, v___x_583_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_dec(v___x_612_);
v___x_614_ = l_Lean_Macro_throwUnsupported___redArg(v___y_565_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; 
v_a_615_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 2);
if (v_isShared_578_ == 0)
{
v___x_617_ = v___x_577_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_fst_574_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_snd_575_);
v___x_617_ = v_reuseFailAlloc_619_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v_a_562_ = v___x_586_;
v_b_563_ = v___x_617_;
v___y_565_ = v_a_615_;
goto _start;
}
}
else
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
v_a_620_ = lean_ctor_get(v___x_614_, 0);
v_a_621_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_614_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_inc(v_a_620_);
lean_dec(v___x_614_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_629_ = lean_box(v___x_561_);
v___f_630_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_630_, 0, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(3u);
v___x_632_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_Lean_Syntax_getArg(v___x_612_, v___x_633_);
v___x_635_ = l_Lean_Syntax_isNone(v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_634_);
v___x_637_ = l_Lean_Syntax_matchesNull(v___x_634_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec(v___x_634_);
lean_dec_ref(v___f_630_);
lean_dec(v___x_612_);
v___x_638_ = l_Lean_Macro_throwUnsupported___redArg(v___y_565_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 2);
if (v_isShared_578_ == 0)
{
v___x_641_ = v___x_577_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_fst_574_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_snd_575_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
v_a_562_ = v___x_586_;
v_b_563_ = v___x_641_;
v___y_565_ = v_a_639_;
goto _start;
}
}
else
{
lean_object* v_a_644_; lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
v_a_644_ = lean_ctor_get(v___x_638_, 0);
v_a_645_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_638_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_inc(v_a_644_);
lean_dec(v___x_638_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_644_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_del_object(v___x_577_);
v___x_653_ = l_Lean_Syntax_getArg(v___x_634_, v___x_633_);
lean_dec(v___x_634_);
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
v___x_656_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_612_, v___x_579_, v___x_631_, v___x_561_, v___x_580_, v___x_581_, v___x_582_, v___f_630_, v_fst_574_, v___x_632_, v_snd_575_, v___x_654_, v___x_655_, v___y_564_, v___y_565_);
lean_dec_ref_known(v___x_655_, 1);
lean_dec(v___x_612_);
v___y_588_ = v___x_656_;
goto v___jp_587_;
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v___x_634_);
lean_del_object(v___x_577_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_box(0);
v___x_659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_612_, v___x_579_, v___x_631_, v___x_561_, v___x_580_, v___x_581_, v___x_582_, v___f_630_, v_fst_574_, v___x_632_, v_snd_575_, v___x_657_, v___x_658_, v___y_564_, v___y_565_);
lean_dec(v___x_612_);
v___y_588_ = v___x_659_;
goto v___jp_587_;
}
}
v___jp_587_:
{
if (lean_obj_tag(v___y_588_) == 0)
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v___y_588_, 0);
lean_inc(v_a_589_);
if (lean_obj_tag(v_a_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref(v___x_586_);
v_a_590_ = lean_ctor_get(v___y_588_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v___y_588_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___y_588_, 0);
lean_dec(v_unused_599_);
v___x_592_ = v___y_588_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___y_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_a_594_; lean_object* v___x_596_; 
v_a_594_ = lean_ctor_get(v_a_589_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v_a_589_, 1);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v_a_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_a_590_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v_a_601_; 
v_a_600_ = lean_ctor_get(v___y_588_, 1);
lean_inc(v_a_600_);
lean_dec_ref_known(v___y_588_, 2);
v_a_601_ = lean_ctor_get(v_a_589_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v_a_589_, 1);
v_a_562_ = v___x_586_;
v_b_563_ = v_a_601_;
v___y_565_ = v_a_600_;
goto _start;
}
}
else
{
lean_object* v_a_603_; lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v___x_586_);
v_a_603_ = lean_ctor_get(v___y_588_, 0);
v_a_604_ = lean_ctor_get(v___y_588_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v___y_588_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___y_588_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_inc(v_a_603_);
lean_dec(v___y_588_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___boxed(lean_object* v___x_663_, lean_object* v_a_664_, lean_object* v_b_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v___x_193111__boxed_668_; lean_object* v_res_669_; 
v___x_193111__boxed_668_ = lean_unbox(v___x_663_);
v_res_669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v___x_193111__boxed_668_, v_a_664_, v_b_665_, v___y_666_, v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object* v_stx_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; uint8_t v___x_769_; 
v___x_736_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_733_);
v___x_769_ = l_Lean_Syntax_isOfKind(v_stx_733_, v___x_736_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v_stx_733_);
v___x_770_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_770_;
}
else
{
lean_object* v___x_771_; lean_object* v_tk_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v_x_782_; lean_object* v_body_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v_h_x3f_828_; lean_object* v___y_829_; lean_object* v___y_830_; 
v___x_771_ = lean_unsigned_to_nat(0u);
v_tk_772_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_771_);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_773_);
lean_inc(v___x_774_);
v___x_775_ = l_Lean_Syntax_matchesNull(v___x_774_, v___x_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_891_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v_inv_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_891_ = lean_unsigned_to_nat(2u);
v___x_933_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_891_);
v___x_934_ = l_Lean_Syntax_isNone(v___x_933_);
if (v___x_934_ == 0)
{
uint8_t v___x_935_; 
lean_inc(v___x_933_);
v___x_935_ = l_Lean_Syntax_matchesNull(v___x_933_, v___x_773_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; 
lean_dec(v___x_933_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_936_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_936_;
}
else
{
lean_object* v_inv_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_inv_937_ = l_Lean_Syntax_getArg(v___x_933_, v___x_771_);
lean_dec(v___x_933_);
v___x_938_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_937_);
v___x_939_ = l_Lean_Syntax_isOfKind(v_inv_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_dec(v_inv_937_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_940_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_inv_937_);
v_inv_912_ = v___x_941_;
v___y_913_ = v_a_734_;
v___y_914_ = v_a_735_;
goto v___jp_911_;
}
}
}
else
{
lean_object* v___x_942_; 
lean_dec(v___x_933_);
v___x_942_ = lean_box(0);
v_inv_912_ = v___x_942_;
v___y_913_ = v_a_734_;
v___y_914_ = v_a_735_;
goto v___jp_911_;
}
v___jp_892_:
{
lean_object* v_decls_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_decls_899_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_896_);
lean_dec_ref(v___y_896_);
v___x_900_ = lean_box(0);
v___x_901_ = lean_array_get(v___x_900_, v_decls_899_, v___x_771_);
lean_inc(v___x_901_);
v___x_902_ = l_Lean_Syntax_isOfKind(v___x_901_, v___y_894_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v___x_901_);
lean_dec_ref(v_decls_899_);
lean_dec(v___y_893_);
lean_dec(v_tk_772_);
v___x_903_ = l_Lean_Macro_throwUnsupported___redArg(v___y_898_);
return v___x_903_;
}
else
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = l_Lean_Syntax_getArg(v___x_901_, v___x_771_);
v___x_905_ = l_Lean_Syntax_isNone(v___x_904_);
if (v___x_905_ == 0)
{
uint8_t v___x_906_; 
lean_inc(v___x_904_);
v___x_906_ = l_Lean_Syntax_matchesNull(v___x_904_, v___x_891_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v___x_904_);
lean_dec(v___x_901_);
lean_dec_ref(v_decls_899_);
lean_dec(v___y_893_);
lean_dec(v_tk_772_);
v___x_907_ = l_Lean_Macro_throwUnsupported___redArg(v___y_898_);
return v___x_907_;
}
else
{
lean_object* v_h_x3f_908_; lean_object* v___x_909_; 
v_h_x3f_908_ = l_Lean_Syntax_getArg(v___x_904_, v___x_771_);
lean_dec(v___x_904_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v_h_x3f_908_);
v___y_823_ = v___y_893_;
v___y_824_ = v___x_901_;
v___y_825_ = v_decls_899_;
v___y_826_ = v___y_894_;
v___y_827_ = v___y_895_;
v_h_x3f_828_ = v___x_909_;
v___y_829_ = v___y_897_;
v___y_830_ = v___y_898_;
goto v___jp_822_;
}
}
else
{
lean_object* v___x_910_; 
lean_dec(v___x_904_);
v___x_910_ = lean_box(0);
v___y_823_ = v___y_893_;
v___y_824_ = v___x_901_;
v___y_825_ = v_decls_899_;
v___y_826_ = v___y_894_;
v___y_827_ = v___y_895_;
v_h_x3f_828_ = v___x_910_;
v___y_829_ = v___y_897_;
v___y_830_ = v___y_898_;
goto v___jp_822_;
}
}
}
v___jp_911_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_body_917_; lean_object* v___x_918_; lean_object* v_decls_919_; 
v___x_915_ = lean_unsigned_to_nat(3u);
v___x_916_ = lean_unsigned_to_nat(4u);
v_body_917_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_916_);
lean_dec(v_stx_733_);
v___x_918_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v_decls_919_ = l_Lean_Syntax_getArgs(v___x_774_);
lean_dec(v___x_774_);
if (lean_obj_tag(v_inv_912_) == 1)
{
lean_object* v_val_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_val_920_ = lean_ctor_get(v_inv_912_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v_inv_912_, 1);
v___x_921_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_922_ = l_Lean_Macro_throwErrorAt___redArg(v_val_920_, v___x_921_, v___y_913_, v___y_914_);
lean_dec(v_val_920_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; 
v_a_923_ = lean_ctor_get(v___x_922_, 1);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 2);
v___y_893_ = v_body_917_;
v___y_894_ = v___x_918_;
v___y_895_ = v___x_915_;
v___y_896_ = v_decls_919_;
v___y_897_ = v___y_913_;
v___y_898_ = v_a_923_;
goto v___jp_892_;
}
else
{
lean_object* v_a_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_decls_919_);
lean_dec(v_body_917_);
lean_dec(v_tk_772_);
v_a_924_ = lean_ctor_get(v___x_922_, 0);
v_a_925_ = lean_ctor_get(v___x_922_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_922_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_inc(v_a_924_);
lean_dec(v___x_922_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_924_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_dec(v_inv_912_);
v___y_893_ = v_body_917_;
v___y_894_ = v___x_918_;
v___y_895_ = v___x_915_;
v___y_896_ = v_decls_919_;
v___y_897_ = v___y_913_;
v___y_898_ = v___y_914_;
goto v___jp_892_;
}
}
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; uint8_t v___y_1012_; lean_object* v_x_1013_; lean_object* v_body_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; lean_object* v___y_1058_; lean_object* v_h_x3f_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1143_; lean_object* v___y_1144_; uint8_t v___y_1145_; lean_object* v_inv_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; uint8_t v___y_1200_; lean_object* v___y_1201_; lean_object* v_x_1202_; lean_object* v_body_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; uint8_t v___y_1247_; lean_object* v_h_x3f_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; uint8_t v___x_1399_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v_x_1405_; lean_object* v_body_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v_h_x3f_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; 
v___x_943_ = l_Lean_Syntax_getArg(v___x_774_, v___x_771_);
v___x_944_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_943_);
v___x_1399_ = l_Lean_Syntax_isOfKind(v___x_943_, v___x_944_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1513_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v_inv_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
lean_dec(v___x_943_);
v___x_1513_ = lean_unsigned_to_nat(2u);
v___x_1553_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1513_);
v___x_1554_ = l_Lean_Syntax_isNone(v___x_1553_);
if (v___x_1554_ == 0)
{
uint8_t v___x_1555_; 
lean_inc(v___x_1553_);
v___x_1555_ = l_Lean_Syntax_matchesNull(v___x_1553_, v___x_773_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_dec(v___x_1553_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1556_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1556_;
}
else
{
lean_object* v_inv_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_inv_1557_ = l_Lean_Syntax_getArg(v___x_1553_, v___x_771_);
lean_dec(v___x_1553_);
v___x_1558_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_1557_);
v___x_1559_ = l_Lean_Syntax_isOfKind(v_inv_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_dec(v_inv_1557_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1560_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1560_;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_inv_1557_);
v_inv_1533_ = v___x_1561_;
v___y_1534_ = v_a_734_;
v___y_1535_ = v_a_735_;
goto v___jp_1532_;
}
}
}
else
{
lean_object* v___x_1562_; 
lean_dec(v___x_1553_);
v___x_1562_ = lean_box(0);
v_inv_1533_ = v___x_1562_;
v___y_1534_ = v_a_734_;
v___y_1535_ = v_a_735_;
goto v___jp_1532_;
}
v___jp_1514_:
{
lean_object* v_decls_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_decls_1520_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1516_);
lean_dec_ref(v___y_1516_);
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_array_get(v___x_1521_, v_decls_1520_, v___x_771_);
lean_inc(v___x_1522_);
v___x_1523_ = l_Lean_Syntax_isOfKind(v___x_1522_, v___x_944_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; 
lean_dec(v___x_1522_);
lean_dec_ref(v_decls_1520_);
lean_dec(v___y_1517_);
lean_dec(v_tk_772_);
v___x_1524_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1519_);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = l_Lean_Syntax_getArg(v___x_1522_, v___x_771_);
v___x_1526_ = l_Lean_Syntax_isNone(v___x_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; 
lean_inc(v___x_1525_);
v___x_1527_ = l_Lean_Syntax_matchesNull(v___x_1525_, v___x_1513_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; 
lean_dec(v___x_1525_);
lean_dec(v___x_1522_);
lean_dec_ref(v_decls_1520_);
lean_dec(v___y_1517_);
lean_dec(v_tk_772_);
v___x_1528_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1519_);
return v___x_1528_;
}
else
{
lean_object* v_h_x3f_1529_; lean_object* v___x_1530_; 
v_h_x3f_1529_ = l_Lean_Syntax_getArg(v___x_1525_, v___x_771_);
lean_dec(v___x_1525_);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_h_x3f_1529_);
v___y_1446_ = v_decls_1520_;
v___y_1447_ = v___y_1515_;
v___y_1448_ = v___x_1522_;
v___y_1449_ = v___y_1517_;
v_h_x3f_1450_ = v___x_1530_;
v___y_1451_ = v___y_1518_;
v___y_1452_ = v___y_1519_;
goto v___jp_1445_;
}
}
else
{
lean_object* v___x_1531_; 
lean_dec(v___x_1525_);
v___x_1531_ = lean_box(0);
v___y_1446_ = v_decls_1520_;
v___y_1447_ = v___y_1515_;
v___y_1448_ = v___x_1522_;
v___y_1449_ = v___y_1517_;
v_h_x3f_1450_ = v___x_1531_;
v___y_1451_ = v___y_1518_;
v___y_1452_ = v___y_1519_;
goto v___jp_1445_;
}
}
}
v___jp_1532_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_body_1538_; lean_object* v_decls_1539_; 
v___x_1536_ = lean_unsigned_to_nat(3u);
v___x_1537_ = lean_unsigned_to_nat(4u);
v_body_1538_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1537_);
lean_dec(v_stx_733_);
v_decls_1539_ = l_Lean_Syntax_getArgs(v___x_774_);
lean_dec(v___x_774_);
if (lean_obj_tag(v_inv_1533_) == 1)
{
lean_object* v_val_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_val_1540_ = lean_ctor_get(v_inv_1533_, 0);
lean_inc(v_val_1540_);
lean_dec_ref_known(v_inv_1533_, 1);
v___x_1541_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1542_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1540_, v___x_1541_, v___y_1534_, v___y_1535_);
lean_dec(v_val_1540_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 1);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 2);
v___y_1515_ = v___x_1536_;
v___y_1516_ = v_decls_1539_;
v___y_1517_ = v_body_1538_;
v___y_1518_ = v___y_1534_;
v___y_1519_ = v_a_1543_;
goto v___jp_1514_;
}
else
{
lean_object* v_a_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec_ref(v_decls_1539_);
lean_dec(v_body_1538_);
lean_dec(v_tk_772_);
v_a_1544_ = lean_ctor_get(v___x_1542_, 0);
v_a_1545_ = lean_ctor_get(v___x_1542_, 1);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1542_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_inc(v_a_1544_);
lean_dec(v___x_1542_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1544_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_dec(v_inv_1533_);
v___y_1515_ = v___x_1536_;
v___y_1516_ = v_decls_1539_;
v___y_1517_ = v_body_1538_;
v___y_1518_ = v___y_1534_;
v___y_1519_ = v___y_1535_;
goto v___jp_1514_;
}
}
}
else
{
lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1563_ = l_Lean_Syntax_getArg(v___x_943_, v___x_771_);
v___x_1564_ = l_Lean_Syntax_isNone(v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v_x_1572_; lean_object* v_body_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; 
v___x_1565_ = lean_unsigned_to_nat(2u);
v___x_1566_ = l_Lean_Syntax_matchesNull(v___x_1563_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1612_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v_h_x3f_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v_inv_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
lean_dec(v___x_943_);
v___x_1612_ = lean_unsigned_to_nat(3u);
v___x_1717_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1565_);
v___x_1718_ = l_Lean_Syntax_isNone(v___x_1717_);
if (v___x_1718_ == 0)
{
uint8_t v___x_1719_; 
lean_inc(v___x_1717_);
v___x_1719_ = l_Lean_Syntax_matchesNull(v___x_1717_, v___x_773_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec(v___x_1717_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1720_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1720_;
}
else
{
lean_object* v_inv_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v_inv_1721_ = l_Lean_Syntax_getArg(v___x_1717_, v___x_771_);
lean_dec(v___x_1717_);
v___x_1722_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_1721_);
v___x_1723_ = l_Lean_Syntax_isOfKind(v_inv_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_dec(v_inv_1721_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1724_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_inv_1721_);
v_inv_1698_ = v___x_1725_;
v___y_1699_ = v_a_734_;
v___y_1700_ = v_a_735_;
goto v___jp_1697_;
}
}
}
else
{
lean_object* v___x_1726_; 
lean_dec(v___x_1717_);
v___x_1726_ = lean_box(0);
v_inv_1698_ = v___x_1726_;
v___y_1699_ = v_a_734_;
v___y_1700_ = v_a_735_;
goto v___jp_1697_;
}
v___jp_1613_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_doElems_1622_; uint8_t v___x_1623_; 
v___x_1620_ = l_Lean_Syntax_getArg(v___y_1616_, v___x_773_);
v___x_1621_ = l_Lean_Syntax_getArg(v___y_1616_, v___x_1612_);
lean_dec(v___y_1616_);
v_doElems_1622_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1623_ = l_Lean_Syntax_isIdent(v___x_1620_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1620_);
v___x_1625_ = l_Lean_Syntax_isOfKind(v___x_1620_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1620_, v___x_1625_, v___y_1618_, v___y_1619_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v_a_1628_; lean_object* v_ref_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_n(v_a_1627_, 2);
v_a_1628_ = lean_ctor_get(v___x_1626_, 1);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1626_, 2);
v_ref_1629_ = lean_ctor_get(v___y_1618_, 5);
v___x_1630_ = l_Lean_SourceInfo_fromRef(v_ref_1629_, v___x_1625_);
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1632_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1634_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1635_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1630_, 15);
v___x_1636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1630_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1638_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1630_);
lean_ctor_set(v___x_1638_, 1, v___x_1632_);
lean_ctor_set(v___x_1638_, 2, v___x_1637_);
v___x_1639_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1638_, 4);
v___x_1640_ = l_Lean_Syntax_node2(v___x_1630_, v___x_1639_, v___x_1638_, v_a_1627_);
v___x_1641_ = l_Lean_Syntax_node1(v___x_1630_, v___x_1632_, v___x_1640_);
v___x_1642_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1630_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1645_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1646_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1630_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_Syntax_node1(v___x_1630_, v___x_1632_, v___x_1620_);
v___x_1649_ = l_Lean_Syntax_node1(v___x_1630_, v___x_1632_, v___x_1648_);
v___x_1650_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1651_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1630_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = l_Lean_Syntax_node4(v___x_1630_, v___x_1645_, v___x_1647_, v___x_1649_, v___x_1651_, v___y_1614_);
v___x_1653_ = l_Lean_Syntax_node1(v___x_1630_, v___x_1632_, v___x_1652_);
v___x_1654_ = l_Lean_Syntax_node1(v___x_1630_, v___x_1644_, v___x_1653_);
v___x_1655_ = l_Lean_Syntax_node7(v___x_1630_, v___x_1634_, v___x_1636_, v___x_1638_, v___x_1638_, v___x_1638_, v___x_1641_, v___x_1643_, v___x_1654_);
v___x_1656_ = l_Lean_Syntax_node2(v___x_1630_, v___x_1633_, v___x_1655_, v___x_1638_);
v___x_1657_ = l_Lean_Syntax_node1(v___x_1630_, v___x_1632_, v___x_1656_);
v___x_1658_ = l_Lean_Syntax_node1(v___x_1630_, v___x_1631_, v___x_1657_);
v___y_1568_ = v___x_1621_;
v___y_1569_ = v___y_1615_;
v___y_1570_ = v_doElems_1622_;
v___y_1571_ = v_h_x3f_1617_;
v_x_1572_ = v_a_1627_;
v_body_1573_ = v___x_1658_;
v___y_1574_ = v___y_1618_;
v___y_1575_ = v_a_1628_;
goto v___jp_1567_;
}
else
{
lean_object* v_a_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v___x_1621_);
lean_dec(v___x_1620_);
lean_dec(v_h_x3f_1617_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v_tk_772_);
v_a_1659_ = lean_ctor_get(v___x_1626_, 0);
v_a_1660_ = lean_ctor_get(v___x_1626_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1626_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_inc(v_a_1659_);
lean_dec(v___x_1626_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1659_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1620_, v___x_1623_, v___y_1618_, v___y_1619_);
lean_dec(v___x_1620_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v_a_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
v_a_1670_ = lean_ctor_get(v___x_1668_, 1);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1668_, 2);
v___y_1568_ = v___x_1621_;
v___y_1569_ = v___y_1615_;
v___y_1570_ = v_doElems_1622_;
v___y_1571_ = v_h_x3f_1617_;
v_x_1572_ = v_a_1669_;
v_body_1573_ = v___y_1614_;
v___y_1574_ = v___y_1618_;
v___y_1575_ = v_a_1670_;
goto v___jp_1567_;
}
else
{
lean_object* v_a_1671_; lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v___x_1621_);
lean_dec(v_h_x3f_1617_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v_tk_772_);
v_a_1671_ = lean_ctor_get(v___x_1668_, 0);
v_a_1672_ = lean_ctor_get(v___x_1668_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1668_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_inc(v_a_1671_);
lean_dec(v___x_1668_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1671_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
else
{
v___y_1568_ = v___x_1621_;
v___y_1569_ = v___y_1615_;
v___y_1570_ = v_doElems_1622_;
v___y_1571_ = v_h_x3f_1617_;
v_x_1572_ = v___x_1620_;
v_body_1573_ = v___y_1614_;
v___y_1574_ = v___y_1618_;
v___y_1575_ = v___y_1619_;
goto v___jp_1567_;
}
}
v___jp_1680_:
{
lean_object* v_decls_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_decls_1685_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1682_);
lean_dec_ref(v___y_1682_);
v___x_1686_ = lean_box(0);
v___x_1687_ = lean_array_get(v___x_1686_, v_decls_1685_, v___x_771_);
lean_inc(v___x_1687_);
v___x_1688_ = l_Lean_Syntax_isOfKind(v___x_1687_, v___x_944_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; 
lean_dec(v___x_1687_);
lean_dec_ref(v_decls_1685_);
lean_dec(v___y_1681_);
lean_dec(v_tk_772_);
v___x_1689_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1684_);
return v___x_1689_;
}
else
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = l_Lean_Syntax_getArg(v___x_1687_, v___x_771_);
v___x_1691_ = l_Lean_Syntax_isNone(v___x_1690_);
if (v___x_1691_ == 0)
{
uint8_t v___x_1692_; 
lean_inc(v___x_1690_);
v___x_1692_ = l_Lean_Syntax_matchesNull(v___x_1690_, v___x_1565_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
lean_dec(v___x_1690_);
lean_dec(v___x_1687_);
lean_dec_ref(v_decls_1685_);
lean_dec(v___y_1681_);
lean_dec(v_tk_772_);
v___x_1693_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1684_);
return v___x_1693_;
}
else
{
lean_object* v_h_x3f_1694_; lean_object* v___x_1695_; 
v_h_x3f_1694_ = l_Lean_Syntax_getArg(v___x_1690_, v___x_771_);
lean_dec(v___x_1690_);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_h_x3f_1694_);
v___y_1614_ = v___y_1681_;
v___y_1615_ = v_decls_1685_;
v___y_1616_ = v___x_1687_;
v_h_x3f_1617_ = v___x_1695_;
v___y_1618_ = v___y_1683_;
v___y_1619_ = v___y_1684_;
goto v___jp_1613_;
}
}
else
{
lean_object* v___x_1696_; 
lean_dec(v___x_1690_);
v___x_1696_ = lean_box(0);
v___y_1614_ = v___y_1681_;
v___y_1615_ = v_decls_1685_;
v___y_1616_ = v___x_1687_;
v_h_x3f_1617_ = v___x_1696_;
v___y_1618_ = v___y_1683_;
v___y_1619_ = v___y_1684_;
goto v___jp_1613_;
}
}
}
v___jp_1697_:
{
lean_object* v___x_1701_; lean_object* v_body_1702_; lean_object* v_decls_1703_; 
v___x_1701_ = lean_unsigned_to_nat(4u);
v_body_1702_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1701_);
lean_dec(v_stx_733_);
v_decls_1703_ = l_Lean_Syntax_getArgs(v___x_774_);
lean_dec(v___x_774_);
if (lean_obj_tag(v_inv_1698_) == 1)
{
lean_object* v_val_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_val_1704_ = lean_ctor_get(v_inv_1698_, 0);
lean_inc(v_val_1704_);
lean_dec_ref_known(v_inv_1698_, 1);
v___x_1705_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1706_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1704_, v___x_1705_, v___y_1699_, v___y_1700_);
lean_dec(v_val_1704_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 1);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 2);
v___y_1681_ = v_body_1702_;
v___y_1682_ = v_decls_1703_;
v___y_1683_ = v___y_1699_;
v___y_1684_ = v_a_1707_;
goto v___jp_1680_;
}
else
{
lean_object* v_a_1708_; lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref(v_decls_1703_);
lean_dec(v_body_1702_);
lean_dec(v_tk_772_);
v_a_1708_ = lean_ctor_get(v___x_1706_, 0);
v_a_1709_ = lean_ctor_get(v___x_1706_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1706_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_inc(v_a_1708_);
lean_dec(v___x_1706_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1708_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_dec(v_inv_1698_);
v___y_1681_ = v_body_1702_;
v___y_1682_ = v_decls_1703_;
v___y_1683_ = v___y_1699_;
v___y_1684_ = v___y_1700_;
goto v___jp_1680_;
}
}
}
else
{
v___y_1312_ = v_a_734_;
v___y_1313_ = v_a_735_;
goto v___jp_1311_;
}
v___jp_1567_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1576_ = lean_array_get_size(v___y_1569_);
v___x_1577_ = l_Array_toSubarray___redArg(v___y_1569_, v___x_773_, v___x_1576_);
lean_inc_ref(v___y_1570_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___y_1570_);
lean_ctor_set(v___x_1578_, 1, v_body_1573_);
v___x_1579_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1566_, v___x_1577_, v___x_1578_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v_a_1581_; lean_object* v_fst_1582_; lean_object* v_snd_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1602_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
v_a_1581_ = lean_ctor_get(v___x_1579_, 1);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1579_, 2);
v_fst_1582_ = lean_ctor_get(v_a_1580_, 0);
v_snd_1583_ = lean_ctor_get(v_a_1580_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_a_1580_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1585_ = v_a_1580_;
v_isShared_1586_ = v_isSharedCheck_1602_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snd_1583_);
lean_inc(v_fst_1582_);
lean_dec(v_a_1580_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1602_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_ref_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v_ref_1587_ = lean_ctor_get(v___y_1574_, 5);
v___x_1588_ = l_Lean_SourceInfo_fromRef(v_ref_1587_, v___x_1566_);
v___x_1589_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1590_ = l_Lean_SourceInfo_fromRef(v_tk_772_, v___x_769_);
lean_dec(v_tk_772_);
v___x_1591_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 2);
lean_ctor_set(v___x_1585_, 1, v___x_1591_);
lean_ctor_set(v___x_1585_, 0, v___x_1590_);
v___x_1593_ = v___x_1585_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1595_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1571_) == 1)
{
lean_object* v_val_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_val_1596_ = lean_ctor_get(v___y_1571_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___y_1571_, 1);
v___x_1597_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1588_);
v___x_1598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1588_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = l_Array_mkArray2___redArg(v_val_1596_, v___x_1598_);
v___y_946_ = v___x_1593_;
v___y_947_ = v___y_1568_;
v___y_948_ = v___x_1595_;
v___y_949_ = v_snd_1583_;
v___y_950_ = v_x_1572_;
v___y_951_ = v_fst_1582_;
v___y_952_ = v_a_1581_;
v___y_953_ = v___x_1589_;
v___y_954_ = v___x_1594_;
v___y_955_ = v___x_1588_;
v___y_956_ = v___x_1599_;
goto v___jp_945_;
}
else
{
lean_object* v___x_1600_; 
lean_dec(v___y_1571_);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_946_ = v___x_1593_;
v___y_947_ = v___y_1568_;
v___y_948_ = v___x_1595_;
v___y_949_ = v_snd_1583_;
v___y_950_ = v_x_1572_;
v___y_951_ = v_fst_1582_;
v___y_952_ = v_a_1581_;
v___y_953_ = v___x_1589_;
v___y_954_ = v___x_1594_;
v___y_955_ = v___x_1588_;
v___y_956_ = v___x_1600_;
goto v___jp_945_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_x_1572_);
lean_dec(v___y_1571_);
lean_dec(v___y_1568_);
lean_dec(v_tk_772_);
v_a_1603_ = lean_ctor_get(v___x_1579_, 0);
v_a_1604_ = lean_ctor_get(v___x_1579_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1579_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_inc(v_a_1603_);
lean_dec(v___x_1579_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1603_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
else
{
lean_dec(v___x_1563_);
v___y_1312_ = v_a_734_;
v___y_1313_ = v_a_735_;
goto v___jp_1311_;
}
}
v___jp_945_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
lean_inc_ref_n(v___y_948_, 3);
v___x_957_ = l_Array_append___redArg(v___y_948_, v___y_956_);
lean_dec_ref(v___y_956_);
lean_inc_n(v___y_954_, 4);
lean_inc_n(v___y_955_, 10);
v___x_958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_958_, 0, v___y_955_);
lean_ctor_set(v___x_958_, 1, v___y_954_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
v___x_959_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_960_, 0, v___y_955_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = l_Lean_Syntax_node4(v___y_955_, v___x_944_, v___x_958_, v___y_950_, v___x_960_, v___y_947_);
v___x_962_ = l_Lean_Syntax_node1(v___y_955_, v___y_954_, v___x_961_);
v___x_963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_963_, 0, v___y_955_);
lean_ctor_set(v___x_963_, 1, v___y_954_);
lean_ctor_set(v___x_963_, 2, v___y_948_);
v___x_964_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_965_, 0, v___y_955_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
lean_inc_ref(v___x_965_);
lean_inc_ref(v___x_963_);
v___x_966_ = l_Lean_Syntax_node5(v___y_955_, v___x_736_, v___y_946_, v___x_962_, v___x_963_, v___x_965_, v___y_949_);
lean_inc(v___y_953_);
v___x_967_ = l_Lean_Syntax_node2(v___y_955_, v___y_953_, v___x_966_, v___x_963_);
v___x_968_ = lean_array_push(v___y_951_, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_970_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_971_ = l_Array_append___redArg(v___y_948_, v___x_968_);
lean_dec_ref(v___x_968_);
v___x_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_972_, 0, v___y_955_);
lean_ctor_set(v___x_972_, 1, v___y_954_);
lean_ctor_set(v___x_972_, 2, v___x_971_);
v___x_973_ = l_Lean_Syntax_node1(v___y_955_, v___x_970_, v___x_972_);
v___x_974_ = l_Lean_Syntax_node2(v___y_955_, v___x_969_, v___x_965_, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___y_952_);
return v___x_975_;
}
v___jp_976_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc_ref_n(v___y_983_, 3);
v___x_988_ = l_Array_append___redArg(v___y_983_, v___y_987_);
lean_dec_ref(v___y_987_);
lean_inc_n(v___y_985_, 4);
lean_inc_n(v___y_982_, 10);
v___x_989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_989_, 0, v___y_982_);
lean_ctor_set(v___x_989_, 1, v___y_985_);
lean_ctor_set(v___x_989_, 2, v___x_988_);
v___x_990_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_991_, 0, v___y_982_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Lean_Syntax_node4(v___y_982_, v___x_944_, v___x_989_, v___y_979_, v___x_991_, v___y_980_);
v___x_993_ = l_Lean_Syntax_node1(v___y_982_, v___y_985_, v___x_992_);
v___x_994_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_994_, 0, v___y_982_);
lean_ctor_set(v___x_994_, 1, v___y_985_);
lean_ctor_set(v___x_994_, 2, v___y_983_);
v___x_995_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_996_, 0, v___y_982_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
lean_inc_ref(v___x_996_);
lean_inc_ref(v___x_994_);
v___x_997_ = l_Lean_Syntax_node5(v___y_982_, v___x_736_, v___y_981_, v___x_993_, v___x_994_, v___x_996_, v___y_978_);
lean_inc(v___y_984_);
v___x_998_ = l_Lean_Syntax_node2(v___y_982_, v___y_984_, v___x_997_, v___x_994_);
v___x_999_ = lean_array_push(v___y_977_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1002_ = l_Array_append___redArg(v___y_983_, v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1003_, 0, v___y_982_);
lean_ctor_set(v___x_1003_, 1, v___y_985_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node1(v___y_982_, v___x_1001_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node2(v___y_982_, v___x_1000_, v___x_996_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___y_986_);
return v___x_1006_;
}
v___jp_1007_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1017_ = lean_array_get_size(v___y_1009_);
v___x_1018_ = l_Array_toSubarray___redArg(v___y_1009_, v___x_773_, v___x_1017_);
lean_inc_ref(v___y_1011_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___y_1011_);
lean_ctor_set(v___x_1019_, 1, v_body_1014_);
v___x_1020_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_1012_, v___x_1018_, v___x_1019_, v___y_1015_, v___y_1016_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v_a_1022_; lean_object* v_fst_1023_; lean_object* v_snd_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1043_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
v_a_1022_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1020_, 2);
v_fst_1023_ = lean_ctor_get(v_a_1021_, 0);
v_snd_1024_ = lean_ctor_get(v_a_1021_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_a_1021_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1026_ = v_a_1021_;
v_isShared_1027_ = v_isSharedCheck_1043_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_snd_1024_);
lean_inc(v_fst_1023_);
lean_dec(v_a_1021_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1043_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_ref_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v_ref_1028_ = lean_ctor_get(v___y_1015_, 5);
v___x_1029_ = l_Lean_SourceInfo_fromRef(v_ref_1028_, v___y_1012_);
v___x_1030_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1031_ = l_Lean_SourceInfo_fromRef(v_tk_772_, v___x_769_);
lean_dec(v_tk_772_);
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 2);
lean_ctor_set(v___x_1026_, 1, v___x_1032_);
lean_ctor_set(v___x_1026_, 0, v___x_1031_);
v___x_1034_ = v___x_1026_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1036_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1008_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_val_1037_ = lean_ctor_get(v___y_1008_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v___y_1008_, 1);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1029_);
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1029_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Array_mkArray2___redArg(v_val_1037_, v___x_1039_);
v___y_977_ = v_fst_1023_;
v___y_978_ = v_snd_1024_;
v___y_979_ = v_x_1013_;
v___y_980_ = v___y_1010_;
v___y_981_ = v___x_1034_;
v___y_982_ = v___x_1029_;
v___y_983_ = v___x_1036_;
v___y_984_ = v___x_1030_;
v___y_985_ = v___x_1035_;
v___y_986_ = v_a_1022_;
v___y_987_ = v___x_1040_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1041_; 
lean_dec(v___y_1008_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_977_ = v_fst_1023_;
v___y_978_ = v_snd_1024_;
v___y_979_ = v_x_1013_;
v___y_980_ = v___y_1010_;
v___y_981_ = v___x_1034_;
v___y_982_ = v___x_1029_;
v___y_983_ = v___x_1036_;
v___y_984_ = v___x_1030_;
v___y_985_ = v___x_1035_;
v___y_986_ = v_a_1022_;
v___y_987_ = v___x_1041_;
goto v___jp_976_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_x_1013_);
lean_dec(v___y_1010_);
lean_dec(v___y_1008_);
lean_dec(v_tk_772_);
v_a_1044_ = lean_ctor_get(v___x_1020_, 0);
v_a_1045_ = lean_ctor_get(v___x_1020_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1020_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_inc(v_a_1044_);
lean_dec(v___x_1020_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1044_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
v___jp_1053_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_doElems_1064_; uint8_t v___x_1065_; 
v___x_1062_ = l_Lean_Syntax_getArg(v___y_1058_, v___x_773_);
v___x_1063_ = l_Lean_Syntax_getArg(v___y_1058_, v___y_1056_);
lean_dec(v___y_1058_);
v_doElems_1064_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1065_ = l_Lean_Syntax_isIdent(v___x_1062_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1062_);
v___x_1067_ = l_Lean_Syntax_isOfKind(v___x_1062_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1062_, v___y_1057_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v_a_1070_; lean_object* v_ref_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc_n(v_a_1069_, 2);
v_a_1070_ = lean_ctor_get(v___x_1068_, 1);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1068_, 2);
v_ref_1071_ = lean_ctor_get(v___y_1060_, 5);
v___x_1072_ = l_Lean_SourceInfo_fromRef(v_ref_1071_, v___y_1057_);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1074_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1075_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1077_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1072_, 15);
v___x_1078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1072_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1072_);
lean_ctor_set(v___x_1080_, 1, v___x_1074_);
lean_ctor_set(v___x_1080_, 2, v___x_1079_);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1080_, 4);
v___x_1082_ = l_Lean_Syntax_node2(v___x_1072_, v___x_1081_, v___x_1080_, v_a_1069_);
v___x_1083_ = l_Lean_Syntax_node1(v___x_1072_, v___x_1074_, v___x_1082_);
v___x_1084_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1072_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1088_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1072_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_Syntax_node1(v___x_1072_, v___x_1074_, v___x_1062_);
v___x_1091_ = l_Lean_Syntax_node1(v___x_1072_, v___x_1074_, v___x_1090_);
v___x_1092_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1072_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_Syntax_node4(v___x_1072_, v___x_1087_, v___x_1089_, v___x_1091_, v___x_1093_, v___y_1054_);
v___x_1095_ = l_Lean_Syntax_node1(v___x_1072_, v___x_1074_, v___x_1094_);
v___x_1096_ = l_Lean_Syntax_node1(v___x_1072_, v___x_1086_, v___x_1095_);
v___x_1097_ = l_Lean_Syntax_node7(v___x_1072_, v___x_1076_, v___x_1078_, v___x_1080_, v___x_1080_, v___x_1080_, v___x_1083_, v___x_1085_, v___x_1096_);
v___x_1098_ = l_Lean_Syntax_node2(v___x_1072_, v___x_1075_, v___x_1097_, v___x_1080_);
v___x_1099_ = l_Lean_Syntax_node1(v___x_1072_, v___x_1074_, v___x_1098_);
v___x_1100_ = l_Lean_Syntax_node1(v___x_1072_, v___x_1073_, v___x_1099_);
v___y_1008_ = v_h_x3f_1059_;
v___y_1009_ = v___y_1055_;
v___y_1010_ = v___x_1063_;
v___y_1011_ = v_doElems_1064_;
v___y_1012_ = v___y_1057_;
v_x_1013_ = v_a_1069_;
v_body_1014_ = v___x_1100_;
v___y_1015_ = v___y_1060_;
v___y_1016_ = v_a_1070_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1101_; lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v___x_1063_);
lean_dec(v___x_1062_);
lean_dec(v_h_x3f_1059_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v_tk_772_);
v_a_1101_ = lean_ctor_get(v___x_1068_, 0);
v_a_1102_ = lean_ctor_get(v___x_1068_, 1);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1068_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
lean_dec(v___x_1068_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1101_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1062_, v___y_1057_, v___y_1060_, v___y_1061_);
lean_dec(v___x_1062_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v_a_1112_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
v_a_1112_ = lean_ctor_get(v___x_1110_, 1);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1110_, 2);
v___y_1008_ = v_h_x3f_1059_;
v___y_1009_ = v___y_1055_;
v___y_1010_ = v___x_1063_;
v___y_1011_ = v_doElems_1064_;
v___y_1012_ = v___y_1057_;
v_x_1013_ = v_a_1111_;
v_body_1014_ = v___y_1054_;
v___y_1015_ = v___y_1060_;
v___y_1016_ = v_a_1112_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1113_; lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v___x_1063_);
lean_dec(v_h_x3f_1059_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v_tk_772_);
v_a_1113_ = lean_ctor_get(v___x_1110_, 0);
v_a_1114_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1110_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_inc(v_a_1113_);
lean_dec(v___x_1110_);
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
}
else
{
v___y_1008_ = v_h_x3f_1059_;
v___y_1009_ = v___y_1055_;
v___y_1010_ = v___x_1063_;
v___y_1011_ = v_doElems_1064_;
v___y_1012_ = v___y_1057_;
v_x_1013_ = v___x_1062_;
v_body_1014_ = v___y_1054_;
v___y_1015_ = v___y_1060_;
v___y_1016_ = v___y_1061_;
goto v___jp_1007_;
}
}
v___jp_1122_:
{
lean_object* v_decls_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_decls_1130_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1124_);
lean_dec_ref(v___y_1124_);
v___x_1131_ = lean_box(0);
v___x_1132_ = lean_array_get(v___x_1131_, v_decls_1130_, v___x_771_);
lean_inc(v___x_1132_);
v___x_1133_ = l_Lean_Syntax_isOfKind(v___x_1132_, v___x_944_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___x_1132_);
lean_dec_ref(v_decls_1130_);
lean_dec(v___y_1123_);
lean_dec(v_tk_772_);
v___x_1134_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1129_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = l_Lean_Syntax_getArg(v___x_1132_, v___x_771_);
v___x_1136_ = l_Lean_Syntax_isNone(v___x_1135_);
if (v___x_1136_ == 0)
{
uint8_t v___x_1137_; 
lean_inc(v___x_1135_);
v___x_1137_ = l_Lean_Syntax_matchesNull(v___x_1135_, v___y_1125_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec(v___x_1135_);
lean_dec(v___x_1132_);
lean_dec_ref(v_decls_1130_);
lean_dec(v___y_1123_);
lean_dec(v_tk_772_);
v___x_1138_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1129_);
return v___x_1138_;
}
else
{
lean_object* v_h_x3f_1139_; lean_object* v___x_1140_; 
v_h_x3f_1139_ = l_Lean_Syntax_getArg(v___x_1135_, v___x_771_);
lean_dec(v___x_1135_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v_h_x3f_1139_);
v___y_1054_ = v___y_1123_;
v___y_1055_ = v_decls_1130_;
v___y_1056_ = v___y_1126_;
v___y_1057_ = v___y_1127_;
v___y_1058_ = v___x_1132_;
v_h_x3f_1059_ = v___x_1140_;
v___y_1060_ = v___y_1128_;
v___y_1061_ = v___y_1129_;
goto v___jp_1053_;
}
}
else
{
lean_object* v___x_1141_; 
lean_dec(v___x_1135_);
v___x_1141_ = lean_box(0);
v___y_1054_ = v___y_1123_;
v___y_1055_ = v_decls_1130_;
v___y_1056_ = v___y_1126_;
v___y_1057_ = v___y_1127_;
v___y_1058_ = v___x_1132_;
v_h_x3f_1059_ = v___x_1141_;
v___y_1060_ = v___y_1128_;
v___y_1061_ = v___y_1129_;
goto v___jp_1053_;
}
}
}
v___jp_1142_:
{
lean_object* v___x_1149_; lean_object* v_body_1150_; lean_object* v_decls_1151_; 
v___x_1149_ = lean_unsigned_to_nat(4u);
v_body_1150_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1149_);
lean_dec(v_stx_733_);
v_decls_1151_ = l_Lean_Syntax_getArgs(v___x_774_);
lean_dec(v___x_774_);
if (lean_obj_tag(v_inv_1146_) == 1)
{
lean_object* v_val_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_val_1152_ = lean_ctor_get(v_inv_1146_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v_inv_1146_, 1);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1154_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1152_, v___x_1153_, v___y_1147_, v___y_1148_);
lean_dec(v_val_1152_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 1);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 2);
v___y_1123_ = v_body_1150_;
v___y_1124_ = v_decls_1151_;
v___y_1125_ = v___y_1143_;
v___y_1126_ = v___y_1144_;
v___y_1127_ = v___y_1145_;
v___y_1128_ = v___y_1147_;
v___y_1129_ = v_a_1155_;
goto v___jp_1122_;
}
else
{
lean_object* v_a_1156_; lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v_decls_1151_);
lean_dec(v_body_1150_);
lean_dec(v_tk_772_);
v_a_1156_ = lean_ctor_get(v___x_1154_, 0);
v_a_1157_ = lean_ctor_get(v___x_1154_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1154_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_inc(v_a_1156_);
lean_dec(v___x_1154_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1156_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_dec(v_inv_1146_);
v___y_1123_ = v_body_1150_;
v___y_1124_ = v_decls_1151_;
v___y_1125_ = v___y_1143_;
v___y_1126_ = v___y_1144_;
v___y_1127_ = v___y_1145_;
v___y_1128_ = v___y_1147_;
v___y_1129_ = v___y_1148_;
goto v___jp_1122_;
}
}
v___jp_1165_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_inc_ref_n(v___y_1168_, 3);
v___x_1177_ = l_Array_append___redArg(v___y_1168_, v___y_1176_);
lean_dec_ref(v___y_1176_);
lean_inc_n(v___y_1172_, 4);
lean_inc_n(v___y_1170_, 10);
v___x_1178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1178_, 0, v___y_1170_);
lean_ctor_set(v___x_1178_, 1, v___y_1172_);
lean_ctor_set(v___x_1178_, 2, v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___y_1170_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_Syntax_node4(v___y_1170_, v___x_944_, v___x_1178_, v___y_1174_, v___x_1180_, v___y_1171_);
v___x_1182_ = l_Lean_Syntax_node1(v___y_1170_, v___y_1172_, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1183_, 0, v___y_1170_);
lean_ctor_set(v___x_1183_, 1, v___y_1172_);
lean_ctor_set(v___x_1183_, 2, v___y_1168_);
v___x_1184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1185_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___y_1170_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
lean_inc_ref(v___x_1185_);
lean_inc_ref(v___x_1183_);
v___x_1186_ = l_Lean_Syntax_node5(v___y_1170_, v___x_736_, v___y_1169_, v___x_1182_, v___x_1183_, v___x_1185_, v___y_1167_);
lean_inc(v___y_1175_);
v___x_1187_ = l_Lean_Syntax_node2(v___y_1170_, v___y_1175_, v___x_1186_, v___x_1183_);
v___x_1188_ = lean_array_push(v___y_1166_, v___x_1187_);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1190_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1191_ = l_Array_append___redArg(v___y_1168_, v___x_1188_);
lean_dec_ref(v___x_1188_);
v___x_1192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1192_, 0, v___y_1170_);
lean_ctor_set(v___x_1192_, 1, v___y_1172_);
lean_ctor_set(v___x_1192_, 2, v___x_1191_);
v___x_1193_ = l_Lean_Syntax_node1(v___y_1170_, v___x_1190_, v___x_1192_);
v___x_1194_ = l_Lean_Syntax_node2(v___y_1170_, v___x_1189_, v___x_1185_, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___y_1173_);
return v___x_1195_;
}
v___jp_1196_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = lean_array_get_size(v___y_1199_);
v___x_1207_ = l_Array_toSubarray___redArg(v___y_1199_, v___x_773_, v___x_1206_);
lean_inc_ref(v___y_1197_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___y_1197_);
lean_ctor_set(v___x_1208_, 1, v_body_1203_);
v___x_1209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v___y_1200_, v___x_1207_, v___x_1208_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v_a_1211_; lean_object* v_fst_1212_; lean_object* v_snd_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1232_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
v_a_1211_ = lean_ctor_get(v___x_1209_, 1);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1209_, 2);
v_fst_1212_ = lean_ctor_get(v_a_1210_, 0);
v_snd_1213_ = lean_ctor_get(v_a_1210_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1215_ = v_a_1210_;
v_isShared_1216_ = v_isSharedCheck_1232_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_snd_1213_);
lean_inc(v_fst_1212_);
lean_dec(v_a_1210_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1232_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v_ref_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v_ref_1217_ = lean_ctor_get(v___y_1204_, 5);
v___x_1218_ = l_Lean_SourceInfo_fromRef(v_ref_1217_, v___y_1200_);
v___x_1219_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1220_ = l_Lean_SourceInfo_fromRef(v_tk_772_, v___x_769_);
lean_dec(v_tk_772_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 2);
lean_ctor_set(v___x_1215_, 1, v___x_1221_);
lean_ctor_set(v___x_1215_, 0, v___x_1220_);
v___x_1223_ = v___x_1215_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1225_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1201_) == 1)
{
lean_object* v_val_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_val_1226_ = lean_ctor_get(v___y_1201_, 0);
lean_inc(v_val_1226_);
lean_dec_ref_known(v___y_1201_, 1);
v___x_1227_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1218_);
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1218_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Array_mkArray2___redArg(v_val_1226_, v___x_1228_);
v___y_1166_ = v_fst_1212_;
v___y_1167_ = v_snd_1213_;
v___y_1168_ = v___x_1225_;
v___y_1169_ = v___x_1223_;
v___y_1170_ = v___x_1218_;
v___y_1171_ = v___y_1198_;
v___y_1172_ = v___x_1224_;
v___y_1173_ = v_a_1211_;
v___y_1174_ = v_x_1202_;
v___y_1175_ = v___x_1219_;
v___y_1176_ = v___x_1229_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1230_; 
lean_dec(v___y_1201_);
v___x_1230_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_1166_ = v_fst_1212_;
v___y_1167_ = v_snd_1213_;
v___y_1168_ = v___x_1225_;
v___y_1169_ = v___x_1223_;
v___y_1170_ = v___x_1218_;
v___y_1171_ = v___y_1198_;
v___y_1172_ = v___x_1224_;
v___y_1173_ = v_a_1211_;
v___y_1174_ = v_x_1202_;
v___y_1175_ = v___x_1219_;
v___y_1176_ = v___x_1230_;
goto v___jp_1165_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_x_1202_);
lean_dec(v___y_1201_);
lean_dec(v___y_1198_);
lean_dec(v_tk_772_);
v_a_1233_ = lean_ctor_get(v___x_1209_, 0);
v_a_1234_ = lean_ctor_get(v___x_1209_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1209_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_inc(v_a_1233_);
lean_dec(v___x_1209_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1233_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
v___jp_1242_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_doElems_1253_; uint8_t v___x_1254_; 
v___x_1251_ = l_Lean_Syntax_getArg(v___y_1246_, v___x_773_);
v___x_1252_ = l_Lean_Syntax_getArg(v___y_1246_, v___y_1243_);
lean_dec(v___y_1246_);
v_doElems_1253_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1254_ = l_Lean_Syntax_isIdent(v___x_1251_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1251_);
v___x_1256_ = l_Lean_Syntax_isOfKind(v___x_1251_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1251_, v___y_1247_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v_ref_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_n(v_a_1258_, 2);
v_a_1259_ = lean_ctor_get(v___x_1257_, 1);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1257_, 2);
v_ref_1260_ = lean_ctor_get(v___y_1249_, 5);
v___x_1261_ = l_Lean_SourceInfo_fromRef(v_ref_1260_, v___y_1247_);
v___x_1262_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1263_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1264_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1265_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1266_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1261_, 15);
v___x_1267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1261_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1261_);
lean_ctor_set(v___x_1269_, 1, v___x_1263_);
lean_ctor_set(v___x_1269_, 2, v___x_1268_);
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1269_, 4);
v___x_1271_ = l_Lean_Syntax_node2(v___x_1261_, v___x_1270_, v___x_1269_, v_a_1258_);
v___x_1272_ = l_Lean_Syntax_node1(v___x_1261_, v___x_1263_, v___x_1271_);
v___x_1273_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1261_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1261_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_Syntax_node1(v___x_1261_, v___x_1263_, v___x_1251_);
v___x_1280_ = l_Lean_Syntax_node1(v___x_1261_, v___x_1263_, v___x_1279_);
v___x_1281_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1261_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l_Lean_Syntax_node4(v___x_1261_, v___x_1276_, v___x_1278_, v___x_1280_, v___x_1282_, v___y_1245_);
v___x_1284_ = l_Lean_Syntax_node1(v___x_1261_, v___x_1263_, v___x_1283_);
v___x_1285_ = l_Lean_Syntax_node1(v___x_1261_, v___x_1275_, v___x_1284_);
v___x_1286_ = l_Lean_Syntax_node7(v___x_1261_, v___x_1265_, v___x_1267_, v___x_1269_, v___x_1269_, v___x_1269_, v___x_1272_, v___x_1274_, v___x_1285_);
v___x_1287_ = l_Lean_Syntax_node2(v___x_1261_, v___x_1264_, v___x_1286_, v___x_1269_);
v___x_1288_ = l_Lean_Syntax_node1(v___x_1261_, v___x_1263_, v___x_1287_);
v___x_1289_ = l_Lean_Syntax_node1(v___x_1261_, v___x_1262_, v___x_1288_);
v___y_1197_ = v_doElems_1253_;
v___y_1198_ = v___x_1252_;
v___y_1199_ = v___y_1244_;
v___y_1200_ = v___y_1247_;
v___y_1201_ = v_h_x3f_1248_;
v_x_1202_ = v_a_1258_;
v_body_1203_ = v___x_1289_;
v___y_1204_ = v___y_1249_;
v___y_1205_ = v_a_1259_;
goto v___jp_1196_;
}
else
{
lean_object* v_a_1290_; lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v___x_1252_);
lean_dec(v___x_1251_);
lean_dec(v_h_x3f_1248_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v_tk_772_);
v_a_1290_ = lean_ctor_get(v___x_1257_, 0);
v_a_1291_ = lean_ctor_get(v___x_1257_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1257_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_inc(v_a_1290_);
lean_dec(v___x_1257_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1290_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1251_, v___y_1247_, v___y_1249_, v___y_1250_);
lean_dec(v___x_1251_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v_a_1301_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
v_a_1301_ = lean_ctor_get(v___x_1299_, 1);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1299_, 2);
v___y_1197_ = v_doElems_1253_;
v___y_1198_ = v___x_1252_;
v___y_1199_ = v___y_1244_;
v___y_1200_ = v___y_1247_;
v___y_1201_ = v_h_x3f_1248_;
v_x_1202_ = v_a_1300_;
v_body_1203_ = v___y_1245_;
v___y_1204_ = v___y_1249_;
v___y_1205_ = v_a_1301_;
goto v___jp_1196_;
}
else
{
lean_object* v_a_1302_; lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v___x_1252_);
lean_dec(v_h_x3f_1248_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v_tk_772_);
v_a_1302_ = lean_ctor_get(v___x_1299_, 0);
v_a_1303_ = lean_ctor_get(v___x_1299_, 1);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1299_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_inc(v_a_1302_);
lean_dec(v___x_1299_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1302_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
else
{
v___y_1197_ = v_doElems_1253_;
v___y_1198_ = v___x_1252_;
v___y_1199_ = v___y_1244_;
v___y_1200_ = v___y_1247_;
v___y_1201_ = v_h_x3f_1248_;
v_x_1202_ = v___x_1251_;
v_body_1203_ = v___y_1245_;
v___y_1204_ = v___y_1249_;
v___y_1205_ = v___y_1250_;
goto v___jp_1196_;
}
}
v___jp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = l_Lean_Syntax_getArg(v___x_943_, v___x_773_);
lean_dec(v___x_943_);
v___x_1315_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
v___x_1316_ = l_Lean_Syntax_isOfKind(v___x_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1317_ = lean_unsigned_to_nat(2u);
v___x_1318_ = lean_unsigned_to_nat(3u);
v___x_1319_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1317_);
v___x_1320_ = l_Lean_Syntax_isNone(v___x_1319_);
if (v___x_1320_ == 0)
{
uint8_t v___x_1321_; 
lean_inc(v___x_1319_);
v___x_1321_ = l_Lean_Syntax_matchesNull(v___x_1319_, v___x_773_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_dec(v___x_1319_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1322_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1313_);
return v___x_1322_;
}
else
{
lean_object* v_inv_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_inv_1323_ = l_Lean_Syntax_getArg(v___x_1319_, v___x_771_);
lean_dec(v___x_1319_);
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_1323_);
v___x_1325_ = l_Lean_Syntax_isOfKind(v_inv_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_dec(v_inv_1323_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1326_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1313_);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_inv_1323_);
v___y_1143_ = v___x_1317_;
v___y_1144_ = v___x_1318_;
v___y_1145_ = v___x_1316_;
v_inv_1146_ = v___x_1327_;
v___y_1147_ = v___y_1312_;
v___y_1148_ = v___y_1313_;
goto v___jp_1142_;
}
}
}
else
{
lean_object* v___x_1328_; 
lean_dec(v___x_1319_);
v___x_1328_ = lean_box(0);
v___y_1143_ = v___x_1317_;
v___y_1144_ = v___x_1318_;
v___y_1145_ = v___x_1316_;
v_inv_1146_ = v___x_1328_;
v___y_1147_ = v___y_1312_;
v___y_1148_ = v___y_1313_;
goto v___jp_1142_;
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1329_ = lean_unsigned_to_nat(2u);
v___x_1330_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1329_);
v___x_1331_ = l_Lean_Syntax_isNone(v___x_1330_);
if (v___x_1331_ == 0)
{
uint8_t v___x_1332_; 
lean_inc(v___x_1330_);
v___x_1332_ = l_Lean_Syntax_matchesNull(v___x_1330_, v___x_773_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec(v___x_1330_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1333_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1313_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1334_ = l_Lean_Syntax_getArg(v___x_1330_, v___x_771_);
lean_dec(v___x_1330_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v___x_1334_);
v___x_1336_ = l_Lean_Syntax_isOfKind(v___x_1334_, v___x_1335_);
if (v___x_1336_ == 0)
{
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec(v___x_1334_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1337_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1313_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1339_ = l_Lean_Macro_throwErrorAt___redArg(v___x_1334_, v___x_1338_, v___y_1312_, v___y_1313_);
lean_dec(v___x_1334_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v_decls_1341_; lean_object* v_decls_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 1);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 2);
v_decls_1341_ = l_Lean_Syntax_getArgs(v___x_774_);
lean_dec(v___x_774_);
v_decls_1342_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1341_);
lean_dec_ref(v_decls_1341_);
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_array_get(v___x_1343_, v_decls_1342_, v___x_771_);
lean_inc(v___x_1344_);
v___x_1345_ = l_Lean_Syntax_isOfKind(v___x_1344_, v___x_944_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
lean_dec(v___x_1344_);
lean_dec_ref(v_decls_1342_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1346_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1340_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_body_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1347_ = lean_unsigned_to_nat(3u);
v___x_1348_ = lean_unsigned_to_nat(4u);
v_body_1349_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1348_);
lean_dec(v_stx_733_);
v___x_1350_ = l_Lean_Syntax_getArg(v___x_1344_, v___x_771_);
v___x_1351_ = l_Lean_Syntax_isNone(v___x_1350_);
if (v___x_1351_ == 0)
{
uint8_t v___x_1352_; 
lean_inc(v___x_1350_);
v___x_1352_ = l_Lean_Syntax_matchesNull(v___x_1350_, v___x_1329_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v___x_1350_);
lean_dec(v_body_1349_);
lean_dec(v___x_1344_);
lean_dec_ref(v_decls_1342_);
lean_dec(v_tk_772_);
v___x_1353_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1340_);
return v___x_1353_;
}
else
{
lean_object* v_h_x3f_1354_; lean_object* v___x_1355_; 
v_h_x3f_1354_ = l_Lean_Syntax_getArg(v___x_1350_, v___x_771_);
lean_dec(v___x_1350_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_h_x3f_1354_);
v___y_1243_ = v___x_1347_;
v___y_1244_ = v_decls_1342_;
v___y_1245_ = v_body_1349_;
v___y_1246_ = v___x_1344_;
v___y_1247_ = v___x_1336_;
v_h_x3f_1248_ = v___x_1355_;
v___y_1249_ = v___y_1312_;
v___y_1250_ = v_a_1340_;
goto v___jp_1242_;
}
}
else
{
lean_object* v___x_1356_; 
lean_dec(v___x_1350_);
v___x_1356_ = lean_box(0);
v___y_1243_ = v___x_1347_;
v___y_1244_ = v_decls_1342_;
v___y_1245_ = v_body_1349_;
v___y_1246_ = v___x_1344_;
v___y_1247_ = v___x_1336_;
v_h_x3f_1248_ = v___x_1356_;
v___y_1249_ = v___y_1312_;
v___y_1250_ = v_a_1340_;
goto v___jp_1242_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v_a_1357_ = lean_ctor_get(v___x_1339_, 0);
v_a_1358_ = lean_ctor_get(v___x_1339_, 1);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1339_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_inc(v_a_1357_);
lean_dec(v___x_1339_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1357_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_object* v___x_1366_; 
lean_dec(v___x_1334_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1366_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1313_);
return v___x_1366_;
}
}
}
else
{
lean_object* v___x_1367_; 
lean_dec(v___x_1330_);
lean_dec(v___x_774_);
lean_dec(v_tk_772_);
lean_dec(v_stx_733_);
v___x_1367_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1313_);
return v___x_1367_;
}
}
}
v___jp_1368_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_inc_ref_n(v___y_1377_, 3);
v___x_1380_ = l_Array_append___redArg(v___y_1377_, v___y_1379_);
lean_dec_ref(v___y_1379_);
lean_inc_n(v___y_1374_, 4);
lean_inc_n(v___y_1372_, 10);
v___x_1381_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1372_);
lean_ctor_set(v___x_1381_, 1, v___y_1374_);
lean_ctor_set(v___x_1381_, 2, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___y_1372_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_Syntax_node4(v___y_1372_, v___x_944_, v___x_1381_, v___y_1373_, v___x_1383_, v___y_1376_);
v___x_1385_ = l_Lean_Syntax_node1(v___y_1372_, v___y_1374_, v___x_1384_);
v___x_1386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1386_, 0, v___y_1372_);
lean_ctor_set(v___x_1386_, 1, v___y_1374_);
lean_ctor_set(v___x_1386_, 2, v___y_1377_);
v___x_1387_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___y_1372_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
lean_inc_ref(v___x_1388_);
lean_inc_ref(v___x_1386_);
v___x_1389_ = l_Lean_Syntax_node5(v___y_1372_, v___x_736_, v___y_1370_, v___x_1385_, v___x_1386_, v___x_1388_, v___y_1371_);
lean_inc(v___y_1378_);
v___x_1390_ = l_Lean_Syntax_node2(v___y_1372_, v___y_1378_, v___x_1389_, v___x_1386_);
v___x_1391_ = lean_array_push(v___y_1369_, v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1393_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1394_ = l_Array_append___redArg(v___y_1377_, v___x_1391_);
lean_dec_ref(v___x_1391_);
v___x_1395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1395_, 0, v___y_1372_);
lean_ctor_set(v___x_1395_, 1, v___y_1374_);
lean_ctor_set(v___x_1395_, 2, v___x_1394_);
v___x_1396_ = l_Lean_Syntax_node1(v___y_1372_, v___x_1393_, v___x_1395_);
v___x_1397_ = l_Lean_Syntax_node2(v___y_1372_, v___x_1392_, v___x_1388_, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___y_1375_);
return v___x_1398_;
}
v___jp_1400_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1409_ = lean_array_get_size(v___y_1401_);
v___x_1410_ = l_Array_toSubarray___redArg(v___y_1401_, v___x_773_, v___x_1409_);
lean_inc_ref(v___y_1403_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1403_);
lean_ctor_set(v___x_1411_, 1, v_body_1406_);
v___x_1412_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1399_, v___x_1410_, v___x_1411_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v_a_1414_; lean_object* v_fst_1415_; lean_object* v_snd_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1435_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
v_a_1414_ = lean_ctor_get(v___x_1412_, 1);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1412_, 2);
v_fst_1415_ = lean_ctor_get(v_a_1413_, 0);
v_snd_1416_ = lean_ctor_get(v_a_1413_, 1);
v_isSharedCheck_1435_ = !lean_is_exclusive(v_a_1413_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1418_ = v_a_1413_;
v_isShared_1419_ = v_isSharedCheck_1435_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_snd_1416_);
lean_inc(v_fst_1415_);
lean_dec(v_a_1413_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1435_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_ref_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v_ref_1420_ = lean_ctor_get(v___y_1407_, 5);
v___x_1421_ = l_Lean_SourceInfo_fromRef(v_ref_1420_, v___x_1399_);
v___x_1422_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1423_ = l_Lean_SourceInfo_fromRef(v_tk_772_, v___x_769_);
lean_dec(v_tk_772_);
v___x_1424_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 2);
lean_ctor_set(v___x_1418_, 1, v___x_1424_);
lean_ctor_set(v___x_1418_, 0, v___x_1423_);
v___x_1426_ = v___x_1418_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1428_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1404_) == 1)
{
lean_object* v_val_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_val_1429_ = lean_ctor_get(v___y_1404_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___y_1404_, 1);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1421_);
v___x_1431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1421_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = l_Array_mkArray2___redArg(v_val_1429_, v___x_1431_);
v___y_1369_ = v_fst_1415_;
v___y_1370_ = v___x_1426_;
v___y_1371_ = v_snd_1416_;
v___y_1372_ = v___x_1421_;
v___y_1373_ = v_x_1405_;
v___y_1374_ = v___x_1427_;
v___y_1375_ = v_a_1414_;
v___y_1376_ = v___y_1402_;
v___y_1377_ = v___x_1428_;
v___y_1378_ = v___x_1422_;
v___y_1379_ = v___x_1432_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1433_; 
lean_dec(v___y_1404_);
v___x_1433_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_1369_ = v_fst_1415_;
v___y_1370_ = v___x_1426_;
v___y_1371_ = v_snd_1416_;
v___y_1372_ = v___x_1421_;
v___y_1373_ = v_x_1405_;
v___y_1374_ = v___x_1427_;
v___y_1375_ = v_a_1414_;
v___y_1376_ = v___y_1402_;
v___y_1377_ = v___x_1428_;
v___y_1378_ = v___x_1422_;
v___y_1379_ = v___x_1433_;
goto v___jp_1368_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_x_1405_);
lean_dec(v___y_1404_);
lean_dec(v___y_1402_);
lean_dec(v_tk_772_);
v_a_1436_ = lean_ctor_get(v___x_1412_, 0);
v_a_1437_ = lean_ctor_get(v___x_1412_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1412_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_inc(v_a_1436_);
lean_dec(v___x_1412_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1436_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
v___jp_1445_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v_doElems_1455_; uint8_t v___x_1456_; 
v___x_1453_ = l_Lean_Syntax_getArg(v___y_1448_, v___x_773_);
v___x_1454_ = l_Lean_Syntax_getArg(v___y_1448_, v___y_1447_);
lean_dec(v___y_1448_);
v_doElems_1455_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1456_ = l_Lean_Syntax_isIdent(v___x_1453_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1457_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1453_);
v___x_1458_ = l_Lean_Syntax_isOfKind(v___x_1453_, v___x_1457_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1453_, v___x_1458_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v_a_1461_; lean_object* v_ref_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc_n(v_a_1460_, 2);
v_a_1461_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1459_, 2);
v_ref_1462_ = lean_ctor_get(v___y_1451_, 5);
v___x_1463_ = l_Lean_SourceInfo_fromRef(v_ref_1462_, v___x_1458_);
v___x_1464_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1465_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1466_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1467_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1468_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1463_, 15);
v___x_1469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1463_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1463_);
lean_ctor_set(v___x_1471_, 1, v___x_1465_);
lean_ctor_set(v___x_1471_, 2, v___x_1470_);
v___x_1472_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1471_, 4);
v___x_1473_ = l_Lean_Syntax_node2(v___x_1463_, v___x_1472_, v___x_1471_, v_a_1460_);
v___x_1474_ = l_Lean_Syntax_node1(v___x_1463_, v___x_1465_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1476_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1463_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1478_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1479_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1463_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = l_Lean_Syntax_node1(v___x_1463_, v___x_1465_, v___x_1453_);
v___x_1482_ = l_Lean_Syntax_node1(v___x_1463_, v___x_1465_, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1463_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
v___x_1485_ = l_Lean_Syntax_node4(v___x_1463_, v___x_1478_, v___x_1480_, v___x_1482_, v___x_1484_, v___y_1449_);
v___x_1486_ = l_Lean_Syntax_node1(v___x_1463_, v___x_1465_, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node1(v___x_1463_, v___x_1477_, v___x_1486_);
v___x_1488_ = l_Lean_Syntax_node7(v___x_1463_, v___x_1467_, v___x_1469_, v___x_1471_, v___x_1471_, v___x_1471_, v___x_1474_, v___x_1476_, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node2(v___x_1463_, v___x_1466_, v___x_1488_, v___x_1471_);
v___x_1490_ = l_Lean_Syntax_node1(v___x_1463_, v___x_1465_, v___x_1489_);
v___x_1491_ = l_Lean_Syntax_node1(v___x_1463_, v___x_1464_, v___x_1490_);
v___y_1401_ = v___y_1446_;
v___y_1402_ = v___x_1454_;
v___y_1403_ = v_doElems_1455_;
v___y_1404_ = v_h_x3f_1450_;
v_x_1405_ = v_a_1460_;
v_body_1406_ = v___x_1491_;
v___y_1407_ = v___y_1451_;
v___y_1408_ = v_a_1461_;
goto v___jp_1400_;
}
else
{
lean_object* v_a_1492_; lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v___x_1454_);
lean_dec(v___x_1453_);
lean_dec(v_h_x3f_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1446_);
lean_dec(v_tk_772_);
v_a_1492_ = lean_ctor_get(v___x_1459_, 0);
v_a_1493_ = lean_ctor_get(v___x_1459_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1459_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_inc(v_a_1492_);
lean_dec(v___x_1459_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1492_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1453_, v___x_1456_, v___y_1451_, v___y_1452_);
lean_dec(v___x_1453_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v_a_1503_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
v_a_1503_ = lean_ctor_get(v___x_1501_, 1);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1501_, 2);
v___y_1401_ = v___y_1446_;
v___y_1402_ = v___x_1454_;
v___y_1403_ = v_doElems_1455_;
v___y_1404_ = v_h_x3f_1450_;
v_x_1405_ = v_a_1502_;
v_body_1406_ = v___y_1449_;
v___y_1407_ = v___y_1451_;
v___y_1408_ = v_a_1503_;
goto v___jp_1400_;
}
else
{
lean_object* v_a_1504_; lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v___x_1454_);
lean_dec(v_h_x3f_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1446_);
lean_dec(v_tk_772_);
v_a_1504_ = lean_ctor_get(v___x_1501_, 0);
v_a_1505_ = lean_ctor_get(v___x_1501_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1501_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_inc(v_a_1504_);
lean_dec(v___x_1501_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1504_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
v___y_1401_ = v___y_1446_;
v___y_1402_ = v___x_1454_;
v___y_1403_ = v_doElems_1455_;
v___y_1404_ = v_h_x3f_1450_;
v_x_1405_ = v___x_1453_;
v_body_1406_ = v___y_1449_;
v___y_1407_ = v___y_1451_;
v___y_1408_ = v___y_1452_;
goto v___jp_1400_;
}
}
}
v___jp_776_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_786_ = lean_array_get_size(v___y_778_);
v___x_787_ = l_Array_toSubarray___redArg(v___y_778_, v___x_773_, v___x_786_);
lean_inc_ref(v___y_777_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___y_777_);
lean_ctor_set(v___x_788_, 1, v_body_783_);
v___x_789_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_775_, v___x_787_, v___x_788_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v_a_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_812_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
v_a_791_ = lean_ctor_get(v___x_789_, 1);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_789_, 2);
v_fst_792_ = lean_ctor_get(v_a_790_, 0);
v_snd_793_ = lean_ctor_get(v_a_790_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_812_ == 0)
{
v___x_795_ = v_a_790_;
v_isShared_796_ = v_isSharedCheck_812_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_inc(v_fst_792_);
lean_dec(v_a_790_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_812_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_ref_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v_ref_797_ = lean_ctor_get(v___y_784_, 5);
v___x_798_ = l_Lean_SourceInfo_fromRef(v_ref_797_, v___x_775_);
v___x_799_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_800_ = l_Lean_SourceInfo_fromRef(v_tk_772_, v___x_769_);
lean_dec(v_tk_772_);
v___x_801_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
if (v_isShared_796_ == 0)
{
lean_ctor_set_tag(v___x_795_, 2);
lean_ctor_set(v___x_795_, 1, v___x_801_);
lean_ctor_set(v___x_795_, 0, v___x_800_);
v___x_803_ = v___x_795_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___x_801_);
v___x_803_ = v_reuseFailAlloc_811_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_805_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_779_) == 1)
{
lean_object* v_val_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_val_806_ = lean_ctor_get(v___y_779_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v___y_779_, 1);
v___x_807_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_798_);
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_798_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Array_mkArray2___redArg(v_val_806_, v___x_808_);
v___y_738_ = v___x_803_;
v___y_739_ = v_snd_793_;
v___y_740_ = v___x_798_;
v___y_741_ = v_a_791_;
v___y_742_ = v___y_780_;
v___y_743_ = v___x_804_;
v___y_744_ = v_x_782_;
v___y_745_ = v___y_781_;
v___y_746_ = v_fst_792_;
v___y_747_ = v___x_805_;
v___y_748_ = v___x_799_;
v___y_749_ = v___x_809_;
goto v___jp_737_;
}
else
{
lean_object* v___x_810_; 
lean_dec(v___y_779_);
v___x_810_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_738_ = v___x_803_;
v___y_739_ = v_snd_793_;
v___y_740_ = v___x_798_;
v___y_741_ = v_a_791_;
v___y_742_ = v___y_780_;
v___y_743_ = v___x_804_;
v___y_744_ = v_x_782_;
v___y_745_ = v___y_781_;
v___y_746_ = v_fst_792_;
v___y_747_ = v___x_805_;
v___y_748_ = v___x_799_;
v___y_749_ = v___x_810_;
goto v___jp_737_;
}
}
}
}
else
{
lean_object* v_a_813_; lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_x_782_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v_tk_772_);
v_a_813_ = lean_ctor_get(v___x_789_, 0);
v_a_814_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_789_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_inc(v_a_813_);
lean_dec(v___x_789_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_813_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
v___jp_822_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v_doElems_833_; uint8_t v___x_834_; 
v___x_831_ = l_Lean_Syntax_getArg(v___y_824_, v___x_773_);
v___x_832_ = l_Lean_Syntax_getArg(v___y_824_, v___y_827_);
lean_dec(v___y_824_);
v_doElems_833_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_834_ = l_Lean_Syntax_isIdent(v___x_831_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_831_);
v___x_836_ = l_Lean_Syntax_isOfKind(v___x_831_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_831_, v___x_836_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v_a_839_; lean_object* v_ref_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_n(v_a_838_, 2);
v_a_839_ = lean_ctor_get(v___x_837_, 1);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_837_, 2);
v_ref_840_ = lean_ctor_get(v___y_829_, 5);
v___x_841_ = l_Lean_SourceInfo_fromRef(v_ref_840_, v___x_836_);
v___x_842_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_843_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_844_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_845_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_846_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_841_, 15);
v___x_847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_841_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_849_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_849_, 0, v___x_841_);
lean_ctor_set(v___x_849_, 1, v___x_843_);
lean_ctor_set(v___x_849_, 2, v___x_848_);
v___x_850_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_849_, 4);
v___x_851_ = l_Lean_Syntax_node2(v___x_841_, v___x_850_, v___x_849_, v_a_838_);
v___x_852_ = l_Lean_Syntax_node1(v___x_841_, v___x_843_, v___x_851_);
v___x_853_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_841_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_856_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_857_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_841_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_Syntax_node1(v___x_841_, v___x_843_, v___x_831_);
v___x_860_ = l_Lean_Syntax_node1(v___x_841_, v___x_843_, v___x_859_);
v___x_861_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_841_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_Lean_Syntax_node4(v___x_841_, v___x_856_, v___x_858_, v___x_860_, v___x_862_, v___y_823_);
v___x_864_ = l_Lean_Syntax_node1(v___x_841_, v___x_843_, v___x_863_);
v___x_865_ = l_Lean_Syntax_node1(v___x_841_, v___x_855_, v___x_864_);
v___x_866_ = l_Lean_Syntax_node7(v___x_841_, v___x_845_, v___x_847_, v___x_849_, v___x_849_, v___x_849_, v___x_852_, v___x_854_, v___x_865_);
v___x_867_ = l_Lean_Syntax_node2(v___x_841_, v___x_844_, v___x_866_, v___x_849_);
v___x_868_ = l_Lean_Syntax_node1(v___x_841_, v___x_843_, v___x_867_);
v___x_869_ = l_Lean_Syntax_node1(v___x_841_, v___x_842_, v___x_868_);
v___y_777_ = v_doElems_833_;
v___y_778_ = v___y_825_;
v___y_779_ = v_h_x3f_828_;
v___y_780_ = v___x_832_;
v___y_781_ = v___y_826_;
v_x_782_ = v_a_838_;
v_body_783_ = v___x_869_;
v___y_784_ = v___y_829_;
v___y_785_ = v_a_839_;
goto v___jp_776_;
}
else
{
lean_object* v_a_870_; lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_dec(v___x_832_);
lean_dec(v___x_831_);
lean_dec(v_h_x3f_828_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_823_);
lean_dec(v_tk_772_);
v_a_870_ = lean_ctor_get(v___x_837_, 0);
v_a_871_ = lean_ctor_get(v___x_837_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_837_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_inc(v_a_870_);
lean_dec(v___x_837_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_870_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_831_, v___x_834_, v___y_829_, v___y_830_);
lean_dec(v___x_831_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v_a_881_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
v_a_881_ = lean_ctor_get(v___x_879_, 1);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_879_, 2);
v___y_777_ = v_doElems_833_;
v___y_778_ = v___y_825_;
v___y_779_ = v_h_x3f_828_;
v___y_780_ = v___x_832_;
v___y_781_ = v___y_826_;
v_x_782_ = v_a_880_;
v_body_783_ = v___y_823_;
v___y_784_ = v___y_829_;
v___y_785_ = v_a_881_;
goto v___jp_776_;
}
else
{
lean_object* v_a_882_; lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v___x_832_);
lean_dec(v_h_x3f_828_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_823_);
lean_dec(v_tk_772_);
v_a_882_ = lean_ctor_get(v___x_879_, 0);
v_a_883_ = lean_ctor_get(v___x_879_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_879_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_inc(v_a_882_);
lean_dec(v___x_879_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_882_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
else
{
v___y_777_ = v_doElems_833_;
v___y_778_ = v___y_825_;
v___y_779_ = v_h_x3f_828_;
v___y_780_ = v___x_832_;
v___y_781_ = v___y_826_;
v_x_782_ = v___x_831_;
v_body_783_ = v___y_823_;
v___y_784_ = v___y_829_;
v___y_785_ = v___y_830_;
goto v___jp_776_;
}
}
}
v___jp_737_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_inc_ref_n(v___y_747_, 3);
v___x_750_ = l_Array_append___redArg(v___y_747_, v___y_749_);
lean_dec_ref(v___y_749_);
lean_inc_n(v___y_743_, 4);
lean_inc_n(v___y_740_, 10);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___y_740_);
lean_ctor_set(v___x_751_, 1, v___y_743_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
v___x_752_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___y_740_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
lean_inc(v___y_745_);
v___x_754_ = l_Lean_Syntax_node4(v___y_740_, v___y_745_, v___x_751_, v___y_744_, v___x_753_, v___y_742_);
v___x_755_ = l_Lean_Syntax_node1(v___y_740_, v___y_743_, v___x_754_);
v___x_756_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_756_, 0, v___y_740_);
lean_ctor_set(v___x_756_, 1, v___y_743_);
lean_ctor_set(v___x_756_, 2, v___y_747_);
v___x_757_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_758_, 0, v___y_740_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
lean_inc_ref(v___x_758_);
lean_inc_ref(v___x_756_);
v___x_759_ = l_Lean_Syntax_node5(v___y_740_, v___x_736_, v___y_738_, v___x_755_, v___x_756_, v___x_758_, v___y_739_);
lean_inc(v___y_748_);
v___x_760_ = l_Lean_Syntax_node2(v___y_740_, v___y_748_, v___x_759_, v___x_756_);
v___x_761_ = lean_array_push(v___y_746_, v___x_760_);
v___x_762_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_763_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_764_ = l_Array_append___redArg(v___y_747_, v___x_761_);
lean_dec_ref(v___x_761_);
v___x_765_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_765_, 0, v___y_740_);
lean_ctor_set(v___x_765_, 1, v___y_743_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___y_740_, v___x_763_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node2(v___y_740_, v___x_762_, v___x_758_, v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v___y_741_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object* v_stx_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Elab_Do_expandDoFor(v_stx_1727_, v_a_1728_, v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_1731_, lean_object* v_inst_1732_, lean_object* v_R_1733_, lean_object* v_a_1734_, lean_object* v_b_1735_, lean_object* v_c_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1731_, v_a_1734_, v_b_1735_, v___y_1737_, v___y_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_1740_, lean_object* v_inst_1741_, lean_object* v_R_1742_, lean_object* v_a_1743_, lean_object* v_b_1744_, lean_object* v_c_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
uint8_t v___x_195737__boxed_1748_; lean_object* v_res_1749_; 
v___x_195737__boxed_1748_ = lean_unbox(v___x_1740_);
v_res_1749_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_195737__boxed_1748_, v_inst_1741_, v_R_1742_, v_a_1743_, v_b_1744_, v_c_1745_, v___y_1746_, v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(uint8_t v___x_1750_, lean_object* v_inst_1751_, lean_object* v_R_1752_, lean_object* v_a_1753_, lean_object* v_b_1754_, lean_object* v_c_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v___x_1750_, v_a_1753_, v_b_1754_, v___y_1756_, v___y_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___boxed(lean_object* v___x_1759_, lean_object* v_inst_1760_, lean_object* v_R_1761_, lean_object* v_a_1762_, lean_object* v_b_1763_, lean_object* v_c_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
uint8_t v___x_195751__boxed_1767_; lean_object* v_res_1768_; 
v___x_195751__boxed_1767_ = lean_unbox(v___x_1759_);
v_res_1768_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(v___x_195751__boxed_1767_, v_inst_1760_, v_R_1761_, v_a_1762_, v_b_1763_, v_c_1764_, v___y_1765_, v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1776_ = l_Lean_Elab_macroAttribute;
v___x_1777_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_1778_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_1779_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor___boxed), 3, 0);
v___x_1780_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1776_, v___x_1777_, v___x_1778_, v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_1782_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_box(0);
v___x_1784_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1783_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg(){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0);
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___boxed(lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0(lean_object* v_00_u03b1_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___boxed(lean_object* v_00_u03b1_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0(v_00_u03b1_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(lean_object* v_____do__lift_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = 0;
v___x_1821_ = l_Lean_SourceInfo_fromRef(v_____do__lift_1811_, v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0___boxed(lean_object* v_____do__lift_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_____do__lift_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v_____do__lift_1823_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(lean_object* v_msgData_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v_env_1840_; lean_object* v___x_1841_; lean_object* v_mctx_1842_; lean_object* v_lctx_1843_; lean_object* v_options_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1839_ = lean_st_ref_get(v___y_1837_);
v_env_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc_ref(v_env_1840_);
lean_dec(v___x_1839_);
v___x_1841_ = lean_st_ref_get(v___y_1835_);
v_mctx_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc_ref(v_mctx_1842_);
lean_dec(v___x_1841_);
v_lctx_1843_ = lean_ctor_get(v___y_1834_, 2);
v_options_1844_ = lean_ctor_get(v___y_1836_, 2);
lean_inc_ref(v_options_1844_);
lean_inc_ref(v_lctx_1843_);
v___x_1845_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1845_, 0, v_env_1840_);
lean_ctor_set(v___x_1845_, 1, v_mctx_1842_);
lean_ctor_set(v___x_1845_, 2, v_lctx_1843_);
lean_ctor_set(v___x_1845_, 3, v_options_1844_);
v___x_1846_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_msgData_1833_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(v_msgData_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(lean_object* v_msg_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_ref_1861_; lean_object* v___x_1862_; lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1871_; 
v_ref_1861_ = lean_ctor_get(v___y_1858_, 5);
v___x_1862_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(v_msg_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1865_ = v___x_1862_;
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1871_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_inc(v_ref_1861_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_ref_1861_);
lean_ctor_set(v___x_1867_, 1, v_a_1863_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 1);
lean_ctor_set(v___x_1865_, 0, v___x_1867_);
v___x_1869_ = v___x_1865_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(v_msg_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(lean_object* v_ref_1879_, lean_object* v_msg_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_fileName_1889_; lean_object* v_fileMap_1890_; lean_object* v_options_1891_; lean_object* v_currRecDepth_1892_; lean_object* v_maxRecDepth_1893_; lean_object* v_ref_1894_; lean_object* v_currNamespace_1895_; lean_object* v_openDecls_1896_; lean_object* v_initHeartbeats_1897_; lean_object* v_maxHeartbeats_1898_; lean_object* v_quotContext_1899_; lean_object* v_currMacroScope_1900_; uint8_t v_diag_1901_; lean_object* v_cancelTk_x3f_1902_; uint8_t v_suppressElabErrors_1903_; lean_object* v_inheritedTraceOptions_1904_; lean_object* v_ref_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v_fileName_1889_ = lean_ctor_get(v___y_1886_, 0);
v_fileMap_1890_ = lean_ctor_get(v___y_1886_, 1);
v_options_1891_ = lean_ctor_get(v___y_1886_, 2);
v_currRecDepth_1892_ = lean_ctor_get(v___y_1886_, 3);
v_maxRecDepth_1893_ = lean_ctor_get(v___y_1886_, 4);
v_ref_1894_ = lean_ctor_get(v___y_1886_, 5);
v_currNamespace_1895_ = lean_ctor_get(v___y_1886_, 6);
v_openDecls_1896_ = lean_ctor_get(v___y_1886_, 7);
v_initHeartbeats_1897_ = lean_ctor_get(v___y_1886_, 8);
v_maxHeartbeats_1898_ = lean_ctor_get(v___y_1886_, 9);
v_quotContext_1899_ = lean_ctor_get(v___y_1886_, 10);
v_currMacroScope_1900_ = lean_ctor_get(v___y_1886_, 11);
v_diag_1901_ = lean_ctor_get_uint8(v___y_1886_, sizeof(void*)*14);
v_cancelTk_x3f_1902_ = lean_ctor_get(v___y_1886_, 12);
v_suppressElabErrors_1903_ = lean_ctor_get_uint8(v___y_1886_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1904_ = lean_ctor_get(v___y_1886_, 13);
v_ref_1905_ = l_Lean_replaceRef(v_ref_1879_, v_ref_1894_);
lean_inc_ref(v_inheritedTraceOptions_1904_);
lean_inc(v_cancelTk_x3f_1902_);
lean_inc(v_currMacroScope_1900_);
lean_inc(v_quotContext_1899_);
lean_inc(v_maxHeartbeats_1898_);
lean_inc(v_initHeartbeats_1897_);
lean_inc(v_openDecls_1896_);
lean_inc(v_currNamespace_1895_);
lean_inc(v_maxRecDepth_1893_);
lean_inc(v_currRecDepth_1892_);
lean_inc_ref(v_options_1891_);
lean_inc_ref(v_fileMap_1890_);
lean_inc_ref(v_fileName_1889_);
v___x_1906_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1906_, 0, v_fileName_1889_);
lean_ctor_set(v___x_1906_, 1, v_fileMap_1890_);
lean_ctor_set(v___x_1906_, 2, v_options_1891_);
lean_ctor_set(v___x_1906_, 3, v_currRecDepth_1892_);
lean_ctor_set(v___x_1906_, 4, v_maxRecDepth_1893_);
lean_ctor_set(v___x_1906_, 5, v_ref_1905_);
lean_ctor_set(v___x_1906_, 6, v_currNamespace_1895_);
lean_ctor_set(v___x_1906_, 7, v_openDecls_1896_);
lean_ctor_set(v___x_1906_, 8, v_initHeartbeats_1897_);
lean_ctor_set(v___x_1906_, 9, v_maxHeartbeats_1898_);
lean_ctor_set(v___x_1906_, 10, v_quotContext_1899_);
lean_ctor_set(v___x_1906_, 11, v_currMacroScope_1900_);
lean_ctor_set(v___x_1906_, 12, v_cancelTk_x3f_1902_);
lean_ctor_set(v___x_1906_, 13, v_inheritedTraceOptions_1904_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*14, v_diag_1901_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*14 + 1, v_suppressElabErrors_1903_);
v___x_1907_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(v_msg_1880_, v___y_1884_, v___y_1885_, v___x_1906_, v___y_1887_);
lean_dec_ref_known(v___x_1906_, 14);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg___boxed(lean_object* v_ref_1908_, lean_object* v_msg_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_ref_1908_, v_msg_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v_ref_1908_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(lean_object* v_as_1919_, size_t v_sz_1920_, size_t v_i_1921_, lean_object* v_b_1922_){
_start:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_lt(v_i_1921_, v_sz_1920_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_b_1922_);
return v___x_1925_;
}
else
{
lean_object* v_a_1926_; lean_object* v_ident_1927_; lean_object* v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; 
v_a_1926_ = lean_array_uget_borrowed(v_as_1919_, v_i_1921_);
v_ident_1927_ = lean_ctor_get(v_a_1926_, 0);
lean_inc(v_ident_1927_);
v___x_1928_ = lean_array_push(v_b_1922_, v_ident_1927_);
v___x_1929_ = ((size_t)1ULL);
v___x_1930_ = lean_usize_add(v_i_1921_, v___x_1929_);
v_i_1921_ = v___x_1930_;
v_b_1922_ = v___x_1928_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg___boxed(lean_object* v_as_1932_, lean_object* v_sz_1933_, lean_object* v_i_1934_, lean_object* v_b_1935_, lean_object* v___y_1936_){
_start:
{
size_t v_sz_boxed_1937_; size_t v_i_boxed_1938_; lean_object* v_res_1939_; 
v_sz_boxed_1937_ = lean_unbox_usize(v_sz_1933_);
lean_dec(v_sz_1933_);
v_i_boxed_1938_ = lean_unbox_usize(v_i_1934_);
lean_dec(v_i_1934_);
v_res_1939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(v_as_1932_, v_sz_boxed_1937_, v_i_boxed_1938_, v_b_1935_);
lean_dec_ref(v_as_1932_);
return v_res_1939_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__3));
v___x_1953_ = l_Lean_stringToMessageData(v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(lean_object* v_invClause_1990_, lean_object* v_h_x3f_1991_, lean_object* v_xs_1992_, lean_object* v_preS_1993_, lean_object* v_body_1994_, lean_object* v_00_u03c3_1995_, lean_object* v_loopMutVars_1996_, uint8_t v_returnsEarly_1997_, lean_object* v_mi_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_invClause_1990_);
v___x_2008_ = l_Lean_Syntax_isOfKind(v_invClause_1990_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
lean_dec_ref(v_body_1994_);
lean_dec_ref(v_preS_1993_);
lean_dec_ref(v_xs_1992_);
lean_dec(v_invClause_1990_);
v___x_2009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = l_Lean_Syntax_getArg(v_invClause_1990_, v___x_2010_);
v___x_2012_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1));
lean_inc(v___x_2011_);
v___x_2013_ = l_Lean_Syntax_isOfKind(v___x_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
lean_dec(v___x_2011_);
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
lean_dec_ref(v_body_1994_);
lean_dec_ref(v_preS_1993_);
lean_dec_ref(v_xs_1992_);
lean_dec(v_invClause_1990_);
v___x_2014_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2014_;
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; uint8_t v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; 
v___x_2015_ = lean_unsigned_to_nat(0u);
v___x_2016_ = l_Lean_Syntax_getArg(v___x_2011_, v___x_2010_);
v___x_2017_ = l_Lean_Syntax_matchesNull(v___x_2016_, v___x_2015_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2107_; 
lean_dec(v___x_2011_);
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
lean_dec_ref(v_body_1994_);
lean_dec_ref(v_preS_1993_);
lean_dec_ref(v_xs_1992_);
lean_dec(v_invClause_1990_);
v___x_2107_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2107_;
}
else
{
lean_object* v_ref_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_cursorBinders_2114_; lean_object* v_statePat_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v_binders_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v_binders_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___x_2236_; 
v_ref_2108_ = lean_ctor_get(v_a_2004_, 5);
v___x_2109_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2108_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc_n(v_a_2110_, 2);
lean_dec_ref(v___x_2109_);
v___x_2111_ = l_Lean_Syntax_getArg(v___x_2011_, v___x_2015_);
v___x_2112_ = lean_unsigned_to_nat(3u);
v___x_2113_ = l_Lean_Syntax_getArg(v___x_2011_, v___x_2112_);
lean_dec(v___x_2011_);
v_cursorBinders_2114_ = l_Lean_Syntax_getArgs(v___x_2111_);
lean_dec(v___x_2111_);
v___x_2207_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_2208_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_2209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_a_2110_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_Lean_Syntax_node1(v_a_2110_, v___x_2207_, v___x_2209_);
v___x_2236_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
if (v_returnsEarly_1997_ == 0)
{
v_binders_2212_ = v___x_2236_;
v___y_2213_ = v_a_1999_;
v___y_2214_ = v_a_2000_;
v___y_2215_ = v_a_2001_;
v___y_2216_ = v_a_2002_;
v___y_2217_ = v_a_2003_;
v___y_2218_ = v_a_2004_;
v___y_2219_ = v_a_2005_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2237_; 
lean_inc(v___x_2210_);
v___x_2237_ = lean_array_push(v___x_2236_, v___x_2210_);
v_binders_2212_ = v___x_2237_;
v___y_2213_ = v_a_1999_;
v___y_2214_ = v_a_2000_;
v___y_2215_ = v_a_2001_;
v___y_2216_ = v_a_2002_;
v___y_2217_ = v_a_2003_;
v___y_2218_ = v_a_2004_;
v___y_2219_ = v_a_2005_;
goto v___jp_2211_;
}
v___jp_2115_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_2125_ = l_Lean_Core_mkFreshUserName(v___x_2124_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v_ref_2127_; lean_object* v___x_2128_; lean_object* v_a_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v_ref_2127_ = lean_ctor_get(v___y_2122_, 5);
v___x_2128_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2127_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc_n(v_a_2129_, 17);
lean_dec_ref(v___x_2128_);
v___x_2130_ = 0;
v___x_2131_ = l_Lean_mkIdentFrom(v_invClause_1990_, v_a_2126_, v___x_2130_);
v___x_2132_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9));
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10));
v___x_2134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2134_, 0, v_a_2129_);
lean_ctor_set(v___x_2134_, 1, v___x_2132_);
v___x_2135_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2136_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2137_ = l_Array_append___redArg(v___x_2136_, v_cursorBinders_2114_);
lean_dec_ref(v_cursorBinders_2114_);
lean_inc(v___x_2131_);
v___x_2138_ = lean_array_push(v___x_2137_, v___x_2131_);
v___x_2139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2139_, 0, v_a_2129_);
lean_ctor_set(v___x_2139_, 1, v___x_2135_);
lean_ctor_set(v___x_2139_, 2, v___x_2138_);
v___x_2140_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2140_, 0, v_a_2129_);
lean_ctor_set(v___x_2140_, 1, v___x_2135_);
lean_ctor_set(v___x_2140_, 2, v___x_2136_);
v___x_2141_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2142_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2142_, 0, v_a_2129_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11));
v___x_2145_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2145_, 0, v_a_2129_);
lean_ctor_set(v___x_2145_, 1, v___x_2143_);
v___x_2146_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_2140_, 3);
v___x_2147_ = l_Lean_Syntax_node2(v_a_2129_, v___x_2146_, v___x_2140_, v___x_2131_);
v___x_2148_ = l_Lean_Syntax_node1(v_a_2129_, v___x_2135_, v___x_2147_);
v___x_2149_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_2150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_a_2129_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_2152_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_2153_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_2154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_a_2129_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_Syntax_node1(v_a_2129_, v___x_2135_, v_statePat_2116_);
v___x_2156_ = l_Lean_Syntax_node1(v_a_2129_, v___x_2135_, v___x_2155_);
lean_inc_ref(v___x_2142_);
v___x_2157_ = l_Lean_Syntax_node4(v_a_2129_, v___x_2152_, v___x_2154_, v___x_2156_, v___x_2142_, v___x_2113_);
v___x_2158_ = l_Lean_Syntax_node1(v_a_2129_, v___x_2135_, v___x_2157_);
v___x_2159_ = l_Lean_Syntax_node1(v_a_2129_, v___x_2151_, v___x_2158_);
v___x_2160_ = l_Lean_Syntax_node6(v_a_2129_, v___x_2144_, v___x_2145_, v___x_2140_, v___x_2140_, v___x_2148_, v___x_2150_, v___x_2159_);
v___x_2161_ = l_Lean_Syntax_node4(v_a_2129_, v___x_2012_, v___x_2139_, v___x_2140_, v___x_2142_, v___x_2160_);
v___x_2162_ = l_Lean_Syntax_node2(v_a_2129_, v___x_2133_, v___x_2134_, v___x_2161_);
if (lean_obj_tag(v_h_x3f_1991_) == 0)
{
v___y_2096_ = v___x_2135_;
v___y_2097_ = v___y_2123_;
v___y_2098_ = v___y_2117_;
v___y_2099_ = v___y_2118_;
v___y_2100_ = v___y_2119_;
v___y_2101_ = v___y_2121_;
v___y_2102_ = v___x_2162_;
v___y_2103_ = v___y_2120_;
v___y_2104_ = v___y_2122_;
v___y_2105_ = v___x_2130_;
goto v___jp_2095_;
}
else
{
if (v___x_2017_ == 0)
{
v___y_2096_ = v___x_2135_;
v___y_2097_ = v___y_2123_;
v___y_2098_ = v___y_2117_;
v___y_2099_ = v___y_2118_;
v___y_2100_ = v___y_2119_;
v___y_2101_ = v___y_2121_;
v___y_2102_ = v___x_2162_;
v___y_2103_ = v___y_2120_;
v___y_2104_ = v___y_2122_;
v___y_2105_ = v___x_2130_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14));
v___y_2071_ = v___x_2135_;
v___y_2072_ = v___y_2123_;
v___y_2073_ = v___y_2119_;
v___y_2074_ = v___y_2118_;
v___y_2075_ = v___y_2117_;
v___y_2076_ = v___y_2121_;
v___y_2077_ = v___y_2120_;
v___y_2078_ = v___x_2162_;
v___y_2079_ = v___y_2122_;
v___y_2080_ = v___x_2130_;
v___y_2081_ = v___x_2163_;
goto v___jp_2070_;
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_statePat_2116_);
lean_dec_ref(v_cursorBinders_2114_);
lean_dec(v___x_2113_);
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
lean_dec_ref(v_body_1994_);
lean_dec_ref(v_preS_1993_);
lean_dec_ref(v_xs_1992_);
lean_dec(v_invClause_1990_);
v_a_2164_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2125_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2125_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
v___jp_2172_:
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_array_get_size(v_binders_2173_);
v___x_2182_ = lean_nat_dec_eq(v___x_2181_, v___x_2015_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_nat_dec_eq(v___x_2181_, v___x_2010_);
if (v___x_2183_ == 0)
{
lean_object* v_ref_2184_; lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_ref_2184_ = lean_ctor_get(v___y_2179_, 5);
v___x_2185_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2184_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc_n(v_a_2186_, 4);
lean_dec_ref(v___x_2185_);
v___x_2187_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16));
v___x_2188_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17));
v___x_2189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2189_, 0, v_a_2186_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2191_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_2193_ = l_Lean_Syntax_SepArray_ofElems(v___x_2192_, v_binders_2173_);
lean_dec_ref(v_binders_2173_);
v___x_2194_ = l_Array_append___redArg(v___x_2191_, v___x_2193_);
lean_dec_ref(v___x_2193_);
v___x_2195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2195_, 0, v_a_2186_);
lean_ctor_set(v___x_2195_, 1, v___x_2190_);
lean_ctor_set(v___x_2195_, 2, v___x_2194_);
v___x_2196_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__18));
v___x_2197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_a_2186_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Lean_Syntax_node3(v_a_2186_, v___x_2187_, v___x_2189_, v___x_2195_, v___x_2197_);
v_statePat_2116_ = v___x_2198_;
v___y_2117_ = v___y_2174_;
v___y_2118_ = v___y_2175_;
v___y_2119_ = v___y_2176_;
v___y_2120_ = v___y_2177_;
v___y_2121_ = v___y_2178_;
v___y_2122_ = v___y_2179_;
v___y_2123_ = v___y_2180_;
goto v___jp_2115_;
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_array_fget(v_binders_2173_, v___x_2015_);
lean_dec_ref(v_binders_2173_);
v_statePat_2116_ = v___x_2199_;
v___y_2117_ = v___y_2174_;
v___y_2118_ = v___y_2175_;
v___y_2119_ = v___y_2176_;
v___y_2120_ = v___y_2177_;
v___y_2121_ = v___y_2178_;
v___y_2122_ = v___y_2179_;
v___y_2123_ = v___y_2180_;
goto v___jp_2115_;
}
}
else
{
lean_object* v_ref_2200_; lean_object* v___x_2201_; lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v_binders_2173_);
v_ref_2200_ = lean_ctor_get(v___y_2179_, 5);
v___x_2201_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2200_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc_n(v_a_2202_, 2);
lean_dec_ref(v___x_2201_);
v___x_2203_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_2204_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_2205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_a_2202_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = l_Lean_Syntax_node1(v_a_2202_, v___x_2203_, v___x_2205_);
v_statePat_2116_ = v___x_2206_;
v___y_2117_ = v___y_2174_;
v___y_2118_ = v___y_2175_;
v___y_2119_ = v___y_2176_;
v___y_2120_ = v___y_2177_;
v___y_2121_ = v___y_2178_;
v___y_2122_ = v___y_2179_;
v___y_2123_ = v___y_2180_;
goto v___jp_2115_;
}
}
v___jp_2211_:
{
size_t v_sz_2220_; size_t v___x_2221_; lean_object* v___x_2222_; 
v_sz_2220_ = lean_array_size(v_loopMutVars_1996_);
v___x_2221_ = ((size_t)0ULL);
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(v_loopMutVars_1996_, v_sz_2220_, v___x_2221_, v_binders_2212_);
if (lean_obj_tag(v___x_2222_) == 0)
{
if (v_returnsEarly_1997_ == 0)
{
lean_object* v_a_2223_; 
lean_dec(v___x_2210_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2222_, 1);
v_binders_2173_ = v_a_2223_;
v___y_2174_ = v___y_2213_;
v___y_2175_ = v___y_2214_;
v___y_2176_ = v___y_2215_;
v___y_2177_ = v___y_2216_;
v___y_2178_ = v___y_2217_;
v___y_2179_ = v___y_2218_;
v___y_2180_ = v___y_2219_;
goto v___jp_2172_;
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v_a_2224_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2222_, 1);
v___x_2225_ = lean_array_get_size(v_loopMutVars_1996_);
v___x_2226_ = lean_nat_dec_eq(v___x_2225_, v___x_2015_);
if (v___x_2226_ == 0)
{
lean_dec(v___x_2210_);
v_binders_2173_ = v_a_2224_;
v___y_2174_ = v___y_2213_;
v___y_2175_ = v___y_2214_;
v___y_2176_ = v___y_2215_;
v___y_2177_ = v___y_2216_;
v___y_2178_ = v___y_2217_;
v___y_2179_ = v___y_2218_;
v___y_2180_ = v___y_2219_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_array_push(v_a_2224_, v___x_2210_);
v_binders_2173_ = v___x_2227_;
v___y_2174_ = v___y_2213_;
v___y_2175_ = v___y_2214_;
v___y_2176_ = v___y_2215_;
v___y_2177_ = v___y_2216_;
v___y_2178_ = v___y_2217_;
v___y_2179_ = v___y_2218_;
v___y_2180_ = v___y_2219_;
goto v___jp_2172_;
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec(v___x_2210_);
lean_dec_ref(v_cursorBinders_2114_);
lean_dec(v___x_2113_);
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
lean_dec_ref(v_body_1994_);
lean_dec_ref(v_preS_1993_);
lean_dec_ref(v_xs_1992_);
lean_dec(v_invClause_1990_);
v_a_2228_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2222_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2222_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
v___jp_2018_:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Elab_Term_exprToSyntax(v_xs_1992_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = l_Lean_Elab_Term_exprToSyntax(v_preS_1993_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = l_Lean_Elab_Term_exprToSyntax(v_body_1994_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v_ref_2035_; lean_object* v_m_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v_ref_2035_ = lean_ctor_get(v___y_2027_, 5);
v_m_2036_ = lean_ctor_get(v_mi_1998_, 0);
lean_inc_ref(v_m_2036_);
lean_dec_ref(v_mi_1998_);
v___x_2037_ = l_Lean_SourceInfo_fromRef(v_ref_2035_, v___y_2022_);
lean_inc(v___x_2037_);
v___x_2038_ = l_Lean_Syntax_node4(v___x_2037_, v___y_2019_, v_a_2030_, v_a_2032_, v_a_2034_, v___y_2021_);
v___x_2039_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2));
lean_inc(v___y_2020_);
v___x_2040_ = l_Lean_mkIdent(v___y_2020_);
v___x_2041_ = l_Lean_Syntax_node2(v___x_2037_, v___x_2039_, v___x_2040_, v___x_2038_);
v___x_2042_ = l_Lean_Expr_app___override(v_m_2036_, v_00_u03c3_1995_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
v___x_2044_ = lean_box(0);
v___x_2045_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2041_, v___x_2043_, v___x_2017_, v___x_2017_, v___x_2044_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
return v___x_2045_;
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v_a_2032_);
lean_dec(v_a_2030_);
lean_dec(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
v_a_2046_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2033_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2033_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_a_2030_);
lean_dec(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
lean_dec_ref(v_body_1994_);
v_a_2054_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2031_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2031_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
lean_dec_ref(v_body_1994_);
lean_dec_ref(v_preS_1993_);
v_a_2062_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2029_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2029_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
v___jp_2070_:
{
lean_object* v___x_2082_; lean_object* v_env_2083_; uint8_t v___x_2084_; 
v___x_2082_ = lean_st_ref_get(v___y_2072_);
v_env_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc_ref(v_env_2083_);
lean_dec(v___x_2082_);
lean_inc(v___y_2081_);
v___x_2084_ = l_Lean_Environment_contains(v_env_2083_, v___y_2081_, v___x_2017_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec(v___y_2078_);
lean_dec(v___y_2071_);
lean_dec_ref(v_mi_1998_);
lean_dec_ref(v_00_u03c3_1995_);
lean_dec_ref(v_body_1994_);
lean_dec_ref(v_preS_1993_);
lean_dec_ref(v_xs_1992_);
v___x_2085_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4);
v___x_2086_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_invClause_1990_, v___x_2085_, v___y_2075_, v___y_2074_, v___y_2073_, v___y_2077_, v___y_2076_, v___y_2079_, v___y_2072_);
lean_dec(v_invClause_1990_);
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_dec(v_invClause_1990_);
v___y_2019_ = v___y_2071_;
v___y_2020_ = v___y_2081_;
v___y_2021_ = v___y_2078_;
v___y_2022_ = v___y_2080_;
v___y_2023_ = v___y_2074_;
v___y_2024_ = v___y_2073_;
v___y_2025_ = v___y_2077_;
v___y_2026_ = v___y_2076_;
v___y_2027_ = v___y_2079_;
v___y_2028_ = v___y_2072_;
goto v___jp_2018_;
}
}
v___jp_2095_:
{
lean_object* v___x_2106_; 
v___x_2106_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8));
v___y_2071_ = v___y_2096_;
v___y_2072_ = v___y_2097_;
v___y_2073_ = v___y_2100_;
v___y_2074_ = v___y_2099_;
v___y_2075_ = v___y_2098_;
v___y_2076_ = v___y_2101_;
v___y_2077_ = v___y_2103_;
v___y_2078_ = v___y_2102_;
v___y_2079_ = v___y_2104_;
v___y_2080_ = v___y_2105_;
v___y_2081_ = v___x_2106_;
goto v___jp_2070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___boxed(lean_object** _args){
lean_object* v_invClause_2238_ = _args[0];
lean_object* v_h_x3f_2239_ = _args[1];
lean_object* v_xs_2240_ = _args[2];
lean_object* v_preS_2241_ = _args[3];
lean_object* v_body_2242_ = _args[4];
lean_object* v_00_u03c3_2243_ = _args[5];
lean_object* v_loopMutVars_2244_ = _args[6];
lean_object* v_returnsEarly_2245_ = _args[7];
lean_object* v_mi_2246_ = _args[8];
lean_object* v_a_2247_ = _args[9];
lean_object* v_a_2248_ = _args[10];
lean_object* v_a_2249_ = _args[11];
lean_object* v_a_2250_ = _args[12];
lean_object* v_a_2251_ = _args[13];
lean_object* v_a_2252_ = _args[14];
lean_object* v_a_2253_ = _args[15];
lean_object* v_a_2254_ = _args[16];
_start:
{
uint8_t v_returnsEarly_boxed_2255_; lean_object* v_res_2256_; 
v_returnsEarly_boxed_2255_ = lean_unbox(v_returnsEarly_2245_);
v_res_2256_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(v_invClause_2238_, v_h_x3f_2239_, v_xs_2240_, v_preS_2241_, v_body_2242_, v_00_u03c3_2243_, v_loopMutVars_2244_, v_returnsEarly_boxed_2255_, v_mi_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec_ref(v_loopMutVars_2244_);
lean_dec(v_h_x3f_2239_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1(lean_object* v_00_u03b1_2257_, lean_object* v_ref_2258_, lean_object* v_msg_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_ref_2258_, v_msg_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_ref_2270_, lean_object* v_msg_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1(v_00_u03b1_2269_, v_ref_2270_, v_msg_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v_ref_2270_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2(lean_object* v_as_2281_, size_t v_sz_2282_, size_t v_i_2283_, lean_object* v_b_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(v_as_2281_, v_sz_2282_, v_i_2283_, v_b_2284_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___boxed(lean_object* v_as_2294_, lean_object* v_sz_2295_, lean_object* v_i_2296_, lean_object* v_b_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
size_t v_sz_boxed_2306_; size_t v_i_boxed_2307_; lean_object* v_res_2308_; 
v_sz_boxed_2306_ = lean_unbox_usize(v_sz_2295_);
lean_dec(v_sz_2295_);
v_i_boxed_2307_ = lean_unbox_usize(v_i_2296_);
lean_dec(v_i_2296_);
v_res_2308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2(v_as_2294_, v_sz_boxed_2306_, v_i_boxed_2307_, v_b_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v_as_2294_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1(lean_object* v_00_u03b1_2309_, lean_object* v_msg_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(v_msg_2310_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2320_, lean_object* v_msg_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1(v_00_u03b1_2320_, v_msg_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v_b_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
lean_inc(v___y_2339_);
lean_inc_ref(v___y_2338_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc_ref(v___y_2332_);
v___x_2341_ = lean_apply_9(v_k_2331_, v_b_2335_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, lean_box(0));
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v_b_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v_b_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_2353_, uint8_t v_bi_2354_, lean_object* v_type_2355_, lean_object* v_k_2356_, uint8_t v_kind_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___f_2366_; lean_object* v___x_2367_; 
lean_inc(v___y_2360_);
lean_inc_ref(v___y_2359_);
lean_inc_ref(v___y_2358_);
v___f_2366_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2366_, 0, v_k_2356_);
lean_closure_set(v___f_2366_, 1, v___y_2358_);
lean_closure_set(v___f_2366_, 2, v___y_2359_);
lean_closure_set(v___f_2366_, 3, v___y_2360_);
v___x_2367_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2353_, v_bi_2354_, v_type_2355_, v___f_2366_, v_kind_2357_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2367_) == 0)
{
return v___x_2367_;
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_2376_, lean_object* v_bi_2377_, lean_object* v_type_2378_, lean_object* v_k_2379_, lean_object* v_kind_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
uint8_t v_bi_boxed_2389_; uint8_t v_kind_boxed_2390_; lean_object* v_res_2391_; 
v_bi_boxed_2389_ = lean_unbox(v_bi_2377_);
v_kind_boxed_2390_ = lean_unbox(v_kind_2380_);
v_res_2391_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2376_, v_bi_boxed_2389_, v_type_2378_, v_k_2379_, v_kind_boxed_2390_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec_ref(v___y_2381_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_2392_, lean_object* v_name_2393_, uint8_t v_bi_2394_, lean_object* v_type_2395_, lean_object* v_k_2396_, uint8_t v_kind_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2393_, v_bi_2394_, v_type_2395_, v_k_2396_, v_kind_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_2407_, lean_object* v_name_2408_, lean_object* v_bi_2409_, lean_object* v_type_2410_, lean_object* v_k_2411_, lean_object* v_kind_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
uint8_t v_bi_boxed_2421_; uint8_t v_kind_boxed_2422_; lean_object* v_res_2423_; 
v_bi_boxed_2421_ = lean_unbox(v_bi_2409_);
v_kind_boxed_2422_ = lean_unbox(v_kind_2412_);
v_res_2423_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_2407_, v_name_2408_, v_bi_boxed_2421_, v_type_2410_, v_k_2411_, v_kind_boxed_2422_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_a_2424_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_2435_, v_x_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec_ref(v_x_2436_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v_x_2446_, lean_object* v___f_2447_, lean_object* v___x_2448_, lean_object* v_x_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2451_ = l_Lean_TSyntax_getId(v_x_2446_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v___f_2447_);
v___x_2453_ = lean_mk_empty_array_with_capacity(v___x_2448_);
v___x_2454_ = lean_array_push(v___x_2453_, v___x_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v_x_2455_, lean_object* v___f_2456_, lean_object* v___x_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_Elab_Do_elabDoFor___lam__2(v_x_2455_, v___f_2456_, v___x_2457_, v_x_2458_, v_x_2459_);
lean_dec(v_x_2459_);
lean_dec(v_x_2458_);
lean_dec(v___x_2457_);
lean_dec(v_x_2455_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_a_2461_, lean_object* v___x_2462_, uint8_t v___x_2463_, lean_object* v_r_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_k_2473_; lean_object* v___x_2474_; 
v_k_2473_ = lean_ctor_get(v_a_2461_, 1);
lean_inc_ref(v_k_2473_);
lean_dec_ref(v_a_2461_);
lean_inc(v___y_2471_);
lean_inc_ref(v___y_2470_);
lean_inc(v___y_2469_);
lean_inc_ref(v___y_2468_);
lean_inc(v___y_2467_);
lean_inc_ref(v___y_2466_);
lean_inc_ref(v___y_2465_);
lean_inc_ref(v_r_2464_);
v___x_2474_ = lean_apply_9(v_k_2473_, v_r_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, lean_box(0));
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = lean_mk_empty_array_with_capacity(v___x_2462_);
v___x_2477_ = lean_array_push(v___x_2476_, v_r_2464_);
v___x_2478_ = 0;
v___x_2479_ = 1;
v___x_2480_ = l_Lean_Meta_mkLambdaFVars(v___x_2477_, v_a_2475_, v___x_2478_, v___x_2463_, v___x_2478_, v___x_2463_, v___x_2479_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec_ref(v___x_2477_);
return v___x_2480_;
}
else
{
lean_dec_ref(v_r_2464_);
return v___x_2474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_a_2481_, lean_object* v___x_2482_, lean_object* v___x_2483_, lean_object* v_r_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
uint8_t v___x_73958__boxed_2493_; lean_object* v_res_2494_; 
v___x_73958__boxed_2493_ = lean_unbox(v___x_2483_);
v_res_2494_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_a_2481_, v___x_2482_, v___x_73958__boxed_2493_, v_r_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___x_2482_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v___x_2495_, lean_object* v_as_2496_, size_t v_sz_2497_, size_t v_i_2498_, lean_object* v_b_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_usize_dec_lt(v_i_2498_, v_sz_2497_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; 
lean_dec_ref(v___x_2495_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_b_2499_);
return v___x_2508_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_a_2509_ = lean_array_uget_borrowed(v_as_2496_, v_i_2498_);
v___x_2510_ = l_Lean_Elab_Do_MutVar_getId(v_a_2509_);
v___x_2511_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_2510_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v_ident_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc_n(v_a_2512_, 2);
lean_dec_ref_known(v___x_2511_, 1);
v_ident_2513_ = lean_ctor_get(v_a_2509_, 0);
v___x_2514_ = l_Lean_LocalDecl_toExpr(v_a_2512_);
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_box(0);
v___x_2517_ = 0;
lean_inc_ref(v___x_2514_);
lean_inc(v_ident_2513_);
v___x_2518_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_2513_, v___x_2514_, v___x_2515_, v___x_2515_, v___x_2516_, v___x_2517_, v___x_2517_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec_ref_known(v___x_2518_, 1);
v___x_2519_ = l_Lean_LocalDecl_type(v_a_2512_);
lean_dec(v_a_2512_);
v___x_2520_ = l_Lean_Meta_getDecLevel(v___x_2519_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v_u_2522_; lean_object* v___x_2523_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v_u_2522_ = lean_ctor_get(v___x_2495_, 1);
lean_inc(v_u_2522_);
v___x_2523_ = l_Lean_Meta_isLevelDefEq(v_a_2521_, v_u_2522_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2524_; size_t v___x_2525_; size_t v___x_2526_; 
lean_dec_ref_known(v___x_2523_, 1);
v___x_2524_ = lean_array_push(v_b_2499_, v___x_2514_);
v___x_2525_ = ((size_t)1ULL);
v___x_2526_ = lean_usize_add(v_i_2498_, v___x_2525_);
v_i_2498_ = v___x_2526_;
v_b_2499_ = v___x_2524_;
goto _start;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v___x_2514_);
lean_dec_ref(v_b_2499_);
lean_dec_ref(v___x_2495_);
v_a_2528_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2523_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2523_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v___x_2514_);
lean_dec_ref(v_b_2499_);
lean_dec_ref(v___x_2495_);
v_a_2536_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2520_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2520_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v___x_2514_);
lean_dec(v_a_2512_);
lean_dec_ref(v_b_2499_);
lean_dec_ref(v___x_2495_);
v_a_2544_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2518_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2518_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v_b_2499_);
lean_dec_ref(v___x_2495_);
v_a_2552_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2511_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2511_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v___x_2560_, lean_object* v_as_2561_, lean_object* v_sz_2562_, lean_object* v_i_2563_, lean_object* v_b_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
size_t v_sz_boxed_2572_; size_t v_i_boxed_2573_; lean_object* v_res_2574_; 
v_sz_boxed_2572_ = lean_unbox_usize(v_sz_2562_);
lean_dec(v_sz_2562_);
v_i_boxed_2573_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_res_2574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v___x_2560_, v_as_2561_, v_sz_boxed_2572_, v_i_boxed_2573_, v_b_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec_ref(v_as_2561_);
return v_res_2574_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = lean_box(1);
v___x_2576_ = l_Lean_MessageData_ofFormat(v___x_2575_);
return v___x_2576_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2));
v___x_2581_ = l_Lean_MessageData_ofFormat(v___x_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(lean_object* v_x_2582_, lean_object* v_x_2583_){
_start:
{
if (lean_obj_tag(v_x_2583_) == 0)
{
return v_x_2582_;
}
else
{
lean_object* v_head_2584_; lean_object* v_tail_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2607_; 
v_head_2584_ = lean_ctor_get(v_x_2583_, 0);
v_tail_2585_ = lean_ctor_get(v_x_2583_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_x_2583_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2587_ = v_x_2583_;
v_isShared_2588_ = v_isSharedCheck_2607_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_tail_2585_);
lean_inc(v_head_2584_);
lean_dec(v_x_2583_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2607_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v_before_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2605_; 
v_before_2589_ = lean_ctor_get(v_head_2584_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_head_2584_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v_head_2584_, 1);
lean_dec(v_unused_2606_);
v___x_2591_ = v_head_2584_;
v_isShared_2592_ = v_isSharedCheck_2605_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_before_2589_);
lean_dec(v_head_2584_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2605_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2592_ == 0)
{
lean_ctor_set_tag(v___x_2591_, 7);
lean_ctor_set(v___x_2591_, 1, v___x_2593_);
lean_ctor_set(v___x_2591_, 0, v_x_2582_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_x_2582_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 7);
lean_ctor_set(v___x_2587_, 1, v___x_2596_);
lean_ctor_set(v___x_2587_, 0, v___x_2595_);
v___x_2598_ = v___x_2587_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = l_Lean_MessageData_ofSyntax(v_before_2589_);
v___x_2600_ = l_Lean_indentD(v___x_2599_);
v___x_2601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2598_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
v_x_2582_ = v___x_2601_;
v_x_2583_ = v_tail_2585_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(lean_object* v_opts_2608_, lean_object* v_opt_2609_){
_start:
{
lean_object* v_name_2610_; lean_object* v_defValue_2611_; lean_object* v_map_2612_; lean_object* v___x_2613_; 
v_name_2610_ = lean_ctor_get(v_opt_2609_, 0);
v_defValue_2611_ = lean_ctor_get(v_opt_2609_, 1);
v_map_2612_ = lean_ctor_get(v_opts_2608_, 0);
v___x_2613_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2612_, v_name_2610_);
if (lean_obj_tag(v___x_2613_) == 0)
{
uint8_t v___x_2614_; 
v___x_2614_ = lean_unbox(v_defValue_2611_);
return v___x_2614_;
}
else
{
lean_object* v_val_2615_; 
v_val_2615_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_val_2615_);
lean_dec_ref_known(v___x_2613_, 1);
if (lean_obj_tag(v_val_2615_) == 1)
{
uint8_t v_v_2616_; 
v_v_2616_ = lean_ctor_get_uint8(v_val_2615_, 0);
lean_dec_ref_known(v_val_2615_, 0);
return v_v_2616_;
}
else
{
uint8_t v___x_2617_; 
lean_dec(v_val_2615_);
v___x_2617_ = lean_unbox(v_defValue_2611_);
return v___x_2617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_2618_, lean_object* v_opt_2619_){
_start:
{
uint8_t v_res_2620_; lean_object* v_r_2621_; 
v_res_2620_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_opts_2618_, v_opt_2619_);
lean_dec_ref(v_opt_2619_);
lean_dec_ref(v_opts_2618_);
v_r_2621_ = lean_box(v_res_2620_);
return v_r_2621_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1));
v___x_2626_ = l_Lean_MessageData_ofFormat(v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(lean_object* v_msgData_2627_, lean_object* v_macroStack_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_options_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v_options_2631_ = lean_ctor_get(v___y_2629_, 2);
v___x_2632_ = l_Lean_Elab_pp_macroStack;
v___x_2633_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_options_2631_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
lean_dec(v_macroStack_2628_);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_msgData_2627_);
return v___x_2634_;
}
else
{
if (lean_obj_tag(v_macroStack_2628_) == 0)
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_msgData_2627_);
return v___x_2635_;
}
else
{
lean_object* v_head_2636_; lean_object* v_after_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2652_; 
v_head_2636_ = lean_ctor_get(v_macroStack_2628_, 0);
lean_inc(v_head_2636_);
v_after_2637_ = lean_ctor_get(v_head_2636_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_head_2636_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v_head_2636_, 0);
lean_dec(v_unused_2653_);
v___x_2639_ = v_head_2636_;
v_isShared_2640_ = v_isSharedCheck_2652_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_after_2637_);
lean_dec(v_head_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2652_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2641_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2640_ == 0)
{
lean_ctor_set_tag(v___x_2639_, 7);
lean_ctor_set(v___x_2639_, 1, v___x_2641_);
lean_ctor_set(v___x_2639_, 0, v_msgData_2627_);
v___x_2643_ = v___x_2639_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_msgData_2627_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_msgData_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2644_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = l_Lean_MessageData_ofSyntax(v_after_2637_);
v___x_2647_ = l_Lean_indentD(v___x_2646_);
v_msgData_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2648_, 0, v___x_2645_);
lean_ctor_set(v_msgData_2648_, 1, v___x_2647_);
v___x_2649_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(v_msgData_2648_, v_macroStack_2628_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
return v___x_2650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2654_, lean_object* v_macroStack_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_2654_, v_macroStack_2655_, v___y_2656_);
lean_dec_ref(v___y_2656_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(lean_object* v_msg_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_ref_2667_; lean_object* v___x_2668_; lean_object* v_a_2669_; lean_object* v_macroStack_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2681_; 
v_ref_2667_ = lean_ctor_get(v___y_2664_, 5);
v___x_2668_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(v_msg_2659_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2668_);
v_macroStack_2670_ = lean_ctor_get(v___y_2660_, 1);
v___x_2671_ = l_Lean_Elab_getBetterRef(v_ref_2667_, v_macroStack_2670_);
lean_inc(v_macroStack_2670_);
v___x_2672_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_a_2669_, v_macroStack_2670_, v___y_2664_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2681_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2681_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2671_);
lean_ctor_set(v___x_2677_, 1, v_a_2673_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set_tag(v___x_2675_, 1);
lean_ctor_set(v___x_2675_, 0, v___x_2677_);
v___x_2679_ = v___x_2675_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg___boxed(lean_object* v_msg_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v_res_2690_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_box(0);
v___x_2697_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2));
v___x_2698_ = l_Lean_mkConst(v___x_2697_, v___x_2696_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4));
v___x_2701_ = l_Lean_stringToMessageData(v___x_2700_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6));
v___x_2704_ = l_Lean_stringToMessageData(v___x_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9));
v___x_2709_ = l_Lean_MessageData_ofFormat(v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v___y_2710_, lean_object* v_monadInfo_2711_, uint8_t v_returnsEarly_2712_, lean_object* v___x_2713_, lean_object* v_a_2714_, uint8_t v___x_2715_, lean_object* v_e_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_defs_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___x_2748_; lean_object* v_returnVar_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2783_; lean_object* v___y_2784_; 
v___x_2748_ = lean_mk_empty_array_with_capacity(v___x_2713_);
if (lean_obj_tag(v_e_2716_) == 0)
{
if (v___x_2715_ == 0)
{
goto v___jp_2797_;
}
else
{
goto v___jp_2758_;
}
}
else
{
goto v___jp_2797_;
}
v___jp_2724_:
{
size_t v_sz_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v_sz_2732_ = lean_array_size(v___y_2710_);
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v_monadInfo_2711_, v___y_2710_, v_sz_2732_, v___x_2733_, v_defs_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2734_) == 0)
{
if (v_returnsEarly_2712_ == 0)
{
return v___x_2734_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
v___x_2736_ = lean_array_get_size(v___y_2710_);
v___x_2737_ = lean_nat_dec_eq(v___x_2736_, v___x_2713_);
if (v___x_2737_ == 0)
{
lean_dec(v_a_2735_);
return v___x_2734_;
}
else
{
lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2746_; 
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; 
v_unused_2747_ = lean_ctor_get(v___x_2734_, 0);
lean_dec(v_unused_2747_);
v___x_2739_ = v___x_2734_;
v_isShared_2740_ = v_isSharedCheck_2746_;
goto v_resetjp_2738_;
}
else
{
lean_dec(v___x_2734_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2746_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2741_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3);
v___x_2742_ = lean_array_push(v_a_2735_, v___x_2741_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2742_);
v___x_2744_ = v___x_2739_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
}
else
{
return v___x_2734_;
}
}
v___jp_2749_:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_array_push(v___x_2748_, v_returnVar_2750_);
v_defs_2725_ = v___x_2757_;
v___y_2726_ = v___y_2751_;
v___y_2727_ = v___y_2752_;
v___y_2728_ = v___y_2753_;
v___y_2729_ = v___y_2754_;
v___y_2730_ = v___y_2755_;
v___y_2731_ = v___y_2756_;
goto v___jp_2724_;
}
v___jp_2758_:
{
if (v_returnsEarly_2712_ == 0)
{
lean_dec(v_e_2716_);
lean_dec_ref(v_a_2714_);
v_defs_2725_ = v___x_2748_;
v___y_2726_ = v___y_2717_;
v___y_2727_ = v___y_2718_;
v___y_2728_ = v___y_2719_;
v___y_2729_ = v___y_2720_;
v___y_2730_ = v___y_2721_;
v___y_2731_ = v___y_2722_;
goto v___jp_2724_;
}
else
{
if (lean_obj_tag(v_e_2716_) == 0)
{
lean_object* v_resultType_2759_; lean_object* v___x_2760_; 
v_resultType_2759_ = lean_ctor_get(v_a_2714_, 0);
lean_inc_ref(v_resultType_2759_);
lean_dec_ref(v_a_2714_);
v___x_2760_ = l_Lean_Meta_mkNone(v_resultType_2759_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v_returnVar_2750_ = v_a_2761_;
v___y_2751_ = v___y_2717_;
v___y_2752_ = v___y_2718_;
v___y_2753_ = v___y_2719_;
v___y_2754_ = v___y_2720_;
v___y_2755_ = v___y_2721_;
v___y_2756_ = v___y_2722_;
goto v___jp_2749_;
}
else
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec_ref(v___x_2748_);
lean_dec_ref(v_monadInfo_2711_);
v_a_2762_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2760_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2760_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
}
else
{
lean_object* v_val_2770_; lean_object* v_resultType_2771_; lean_object* v___x_2772_; 
v_val_2770_ = lean_ctor_get(v_e_2716_, 0);
lean_inc(v_val_2770_);
lean_dec_ref_known(v_e_2716_, 1);
v_resultType_2771_ = lean_ctor_get(v_a_2714_, 0);
lean_inc_ref(v_resultType_2771_);
lean_dec_ref(v_a_2714_);
v___x_2772_ = l_Lean_Meta_mkSome(v_resultType_2771_, v_val_2770_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v_returnVar_2750_ = v_a_2773_;
v___y_2751_ = v___y_2717_;
v___y_2752_ = v___y_2718_;
v___y_2753_ = v___y_2719_;
v___y_2754_ = v___y_2720_;
v___y_2755_ = v___y_2721_;
v___y_2756_ = v___y_2722_;
goto v___jp_2749_;
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref(v___x_2748_);
lean_dec_ref(v_monadInfo_2711_);
v_a_2774_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2772_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2772_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
v___jp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_inc_ref(v___y_2783_);
v___x_2785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___y_2783_);
lean_ctor_set(v___x_2785_, 1, v___y_2784_);
v___x_2786_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5);
v___x_2787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2785_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v___x_2787_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
v___jp_2797_:
{
if (v_returnsEarly_2712_ == 0)
{
lean_object* v___x_2798_; 
lean_dec_ref(v___x_2748_);
lean_dec_ref(v_a_2714_);
lean_dec_ref(v_monadInfo_2711_);
v___x_2798_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7);
if (lean_obj_tag(v_e_2716_) == 0)
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10);
v___y_2783_ = v___x_2798_;
v___y_2784_ = v___x_2799_;
goto v___jp_2782_;
}
else
{
lean_object* v_val_2800_; lean_object* v___x_2801_; 
v_val_2800_ = lean_ctor_get(v_e_2716_, 0);
lean_inc(v_val_2800_);
lean_dec_ref_known(v_e_2716_, 1);
v___x_2801_ = l_Lean_MessageData_ofExpr(v_val_2800_);
v___y_2783_ = v___x_2798_;
v___y_2784_ = v___x_2801_;
goto v___jp_2782_;
}
}
else
{
goto v___jp_2758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v___y_2802_, lean_object* v_monadInfo_2803_, lean_object* v_returnsEarly_2804_, lean_object* v___x_2805_, lean_object* v_a_2806_, lean_object* v___x_2807_, lean_object* v_e_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
uint8_t v_returnsEarly_boxed_2816_; uint8_t v___x_74364__boxed_2817_; lean_object* v_res_2818_; 
v_returnsEarly_boxed_2816_ = lean_unbox(v_returnsEarly_2804_);
v___x_74364__boxed_2817_ = lean_unbox(v___x_2807_);
v_res_2818_ = l_Lean_Elab_Do_elabDoFor___lam__3(v___y_2802_, v_monadInfo_2803_, v_returnsEarly_boxed_2816_, v___x_2805_, v_a_2806_, v___x_74364__boxed_2817_, v_e_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___x_2805_);
lean_dec_ref(v___y_2802_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_name_2819_, lean_object* v_type_2820_, lean_object* v_k_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
uint8_t v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; 
v___x_2830_ = 0;
v___x_2831_ = 0;
v___x_2832_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2819_, v___x_2830_, v_type_2820_, v_k_2821_, v___x_2831_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_name_2833_, lean_object* v_type_2834_, lean_object* v_k_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_2833_, v_type_2834_, v_k_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(uint8_t v_returnsEarly_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_doBlockResultType_2865_, lean_object* v_a_2866_, lean_object* v_v_2867_, lean_object* v_u_2868_, lean_object* v___f_2869_, lean_object* v___y_2870_, lean_object* v___x_2871_, lean_object* v___x_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_ret_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; 
if (v_returnsEarly_2862_ == 0)
{
lean_object* v___x_2936_; 
lean_dec_ref(v___f_2869_);
lean_dec(v_u_2868_);
lean_dec(v_v_2867_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v_doBlockResultType_2865_);
lean_dec(v_a_2864_);
v___x_2936_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_2863_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_Meta_getFVarFromUserName(v_a_2864_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2939_ = lean_array_get_size(v___y_2870_);
v___x_2940_ = lean_nat_dec_eq(v___x_2939_, v___x_2871_);
if (v___x_2940_ == 0)
{
v_ret_2882_ = v_a_2938_;
v___y_2883_ = v___y_2873_;
v___y_2884_ = v___y_2874_;
v___y_2885_ = v___y_2875_;
v___y_2886_ = v___y_2876_;
v___y_2887_ = v___y_2877_;
v___y_2888_ = v___y_2878_;
v___y_2889_ = v___y_2879_;
goto v___jp_2881_;
}
else
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2941_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__9));
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2872_);
v___x_2943_ = lean_array_push(v___x_2942_, v_a_2938_);
v___x_2944_ = l_Lean_Meta_mkAppM(v___x_2941_, v___x_2943_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
v_ret_2882_ = v_a_2945_;
v___y_2883_ = v___y_2873_;
v___y_2884_ = v___y_2874_;
v___y_2885_ = v___y_2875_;
v___y_2886_ = v___y_2876_;
v___y_2887_ = v___y_2877_;
v___y_2888_ = v___y_2878_;
v___y_2889_ = v___y_2879_;
goto v___jp_2881_;
}
else
{
lean_dec_ref(v___f_2869_);
lean_dec(v_u_2868_);
lean_dec(v_v_2867_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v_doBlockResultType_2865_);
lean_dec_ref(v_a_2863_);
return v___x_2944_;
}
}
}
else
{
lean_dec_ref(v___f_2869_);
lean_dec(v_u_2868_);
lean_dec(v_v_2867_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v_doBlockResultType_2865_);
lean_dec_ref(v_a_2863_);
return v___x_2937_;
}
}
v___jp_2881_:
{
lean_object* v___x_2890_; 
lean_inc(v___y_2889_);
lean_inc_ref(v___y_2888_);
lean_inc(v___y_2887_);
lean_inc_ref(v___y_2886_);
lean_inc_ref(v_ret_2882_);
v___x_2890_ = lean_infer_type(v_ret_2882_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2865_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_2863_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__1));
v___x_2897_ = l_Lean_Core_mkFreshUserName(v___x_2896_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v_resultType_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2926_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
v_resultType_2899_ = lean_ctor_get(v_a_2866_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v_a_2866_, 1);
lean_dec(v_unused_2927_);
v___x_2901_ = v_a_2866_;
v_isShared_2902_ = v_isSharedCheck_2926_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_resultType_2899_);
lean_dec(v_a_2866_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2926_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2903_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__2));
v___x_2904_ = 0;
v___x_2905_ = l_Lean_mkLambda(v___x_2903_, v___x_2904_, v_a_2891_, v_a_2893_);
v___x_2906_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__6));
v___x_2907_ = l_Lean_Level_succ___override(v_v_2867_);
v___x_2908_ = lean_box(0);
if (v_isShared_2902_ == 0)
{
lean_ctor_set_tag(v___x_2901_, 1);
lean_ctor_set(v___x_2901_, 1, v___x_2908_);
lean_ctor_set(v___x_2901_, 0, v___x_2907_);
v___x_2910_ = v___x_2901_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2911_, 0, v_u_2868_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = l_Lean_mkConst(v___x_2906_, v___x_2911_);
lean_inc_ref(v_resultType_2899_);
v___x_2913_ = l_Lean_mkApp3(v___x_2912_, v_resultType_2899_, v___x_2905_, v_ret_2882_);
v___x_2914_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_a_2898_, v_resultType_2899_, v___f_2869_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2924_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2924_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2924_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2919_ = l_Lean_mkSimpleThunk(v_a_2895_);
v___x_2920_ = l_Lean_mkAppB(v___x_2913_, v_a_2915_, v___x_2919_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2920_);
v___x_2922_ = v___x_2917_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
else
{
lean_dec_ref(v___x_2913_);
lean_dec(v_a_2895_);
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec(v_a_2895_);
lean_dec(v_a_2893_);
lean_dec(v_a_2891_);
lean_dec_ref(v_ret_2882_);
lean_dec_ref(v___f_2869_);
lean_dec(v_u_2868_);
lean_dec(v_v_2867_);
lean_dec_ref(v_a_2866_);
v_a_2928_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2897_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2897_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_dec(v_a_2893_);
lean_dec(v_a_2891_);
lean_dec_ref(v_ret_2882_);
lean_dec_ref(v___f_2869_);
lean_dec(v_u_2868_);
lean_dec(v_v_2867_);
lean_dec_ref(v_a_2866_);
return v___x_2894_;
}
}
else
{
lean_dec(v_a_2891_);
lean_dec_ref(v_ret_2882_);
lean_dec_ref(v___f_2869_);
lean_dec(v_u_2868_);
lean_dec(v_v_2867_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v_a_2863_);
return v___x_2892_;
}
}
else
{
lean_dec_ref(v_ret_2882_);
lean_dec_ref(v___f_2869_);
lean_dec(v_u_2868_);
lean_dec(v_v_2867_);
lean_dec_ref(v_a_2866_);
lean_dec_ref(v_doBlockResultType_2865_);
lean_dec_ref(v_a_2863_);
return v___x_2890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object** _args){
lean_object* v_returnsEarly_2946_ = _args[0];
lean_object* v_a_2947_ = _args[1];
lean_object* v_a_2948_ = _args[2];
lean_object* v_doBlockResultType_2949_ = _args[3];
lean_object* v_a_2950_ = _args[4];
lean_object* v_v_2951_ = _args[5];
lean_object* v_u_2952_ = _args[6];
lean_object* v___f_2953_ = _args[7];
lean_object* v___y_2954_ = _args[8];
lean_object* v___x_2955_ = _args[9];
lean_object* v___x_2956_ = _args[10];
lean_object* v___y_2957_ = _args[11];
lean_object* v___y_2958_ = _args[12];
lean_object* v___y_2959_ = _args[13];
lean_object* v___y_2960_ = _args[14];
lean_object* v___y_2961_ = _args[15];
lean_object* v___y_2962_ = _args[16];
lean_object* v___y_2963_ = _args[17];
lean_object* v___y_2964_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_2965_; lean_object* v_res_2966_; 
v_returnsEarly_boxed_2965_ = lean_unbox(v_returnsEarly_2946_);
v_res_2966_ = l_Lean_Elab_Do_elabDoFor___lam__4(v_returnsEarly_boxed_2965_, v_a_2947_, v_a_2948_, v_doBlockResultType_2949_, v_a_2950_, v_v_2951_, v_u_2952_, v___f_2953_, v___y_2954_, v___x_2955_, v___x_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v___y_2954_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___x_2969_, uint8_t v___x_2970_, lean_object* v_postS_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = l_Lean_Expr_fvarId_x21(v_postS_2971_);
v___x_2981_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2967_, v___x_2980_, v___y_2968_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
v___x_2983_ = lean_mk_empty_array_with_capacity(v___x_2969_);
v___x_2984_ = lean_array_push(v___x_2983_, v_postS_2971_);
v___x_2985_ = 0;
v___x_2986_ = 1;
v___x_2987_ = l_Lean_Meta_mkLambdaFVars(v___x_2984_, v_a_2982_, v___x_2985_, v___x_2970_, v___x_2985_, v___x_2970_, v___x_2986_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec_ref(v___x_2984_);
return v___x_2987_;
}
else
{
lean_dec_ref(v_postS_2971_);
return v___x_2981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___x_2990_, lean_object* v___x_2991_, lean_object* v_postS_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
uint8_t v___x_74824__boxed_3001_; lean_object* v_res_3002_; 
v___x_74824__boxed_3001_ = lean_unbox(v___x_2991_);
v_res_3002_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___y_2988_, v___y_2989_, v___x_2990_, v___x_74824__boxed_3001_, v_postS_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___x_2990_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_3004_, lean_object* v_u_3005_, lean_object* v___x_3006_, lean_object* v___x_3007_, lean_object* v_snd_3008_, lean_object* v___x_3009_, lean_object* v_e_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_e_3010_);
lean_inc(v___y_3017_);
lean_inc_ref(v___y_3016_);
lean_inc(v___y_3015_);
lean_inc_ref(v___y_3014_);
lean_inc(v___y_3013_);
lean_inc_ref(v___y_3012_);
v___x_3020_ = lean_apply_8(v___f_3004_, v___x_3019_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, lean_box(0));
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = l_Lean_Meta_mkProdMkN(v_a_3021_, v_u_3005_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v_fst_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v_fst_3024_ = lean_ctor_get(v_a_3023_, 0);
lean_inc(v_fst_3024_);
lean_dec(v_a_3023_);
v___x_3025_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_3026_ = l_Lean_Name_mkStr2(v___x_3006_, v___x_3025_);
v___x_3027_ = l_Lean_mkConst(v___x_3026_, v___x_3007_);
v___x_3028_ = l_Lean_mkAppB(v___x_3027_, v_snd_3008_, v_fst_3024_);
v___x_3029_ = l_Lean_Elab_Do_mkPureApp(v___x_3009_, v___x_3028_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3029_;
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec_ref(v___x_3009_);
lean_dec_ref(v_snd_3008_);
lean_dec(v___x_3007_);
lean_dec_ref(v___x_3006_);
v_a_3030_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3022_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3022_);
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
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___x_3009_);
lean_dec_ref(v_snd_3008_);
lean_dec(v___x_3007_);
lean_dec_ref(v___x_3006_);
lean_dec(v_u_3005_);
v_a_3038_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3020_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3020_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_3046_, lean_object* v_u_3047_, lean_object* v___x_3048_, lean_object* v___x_3049_, lean_object* v_snd_3050_, lean_object* v___x_3051_, lean_object* v_e_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_3046_, v_u_3047_, v___x_3048_, v___x_3049_, v_snd_3050_, v___x_3051_, v_e_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v___y_3053_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___f_3063_, lean_object* v___x_3064_, lean_object* v_u_3065_, lean_object* v___x_3066_, lean_object* v___x_3067_, lean_object* v_snd_3068_, lean_object* v___x_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3078_; 
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc(v___y_3074_);
lean_inc_ref(v___y_3073_);
lean_inc(v___y_3072_);
lean_inc_ref(v___y_3071_);
v___x_3078_ = lean_apply_8(v___f_3063_, v___x_3064_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, lean_box(0));
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3080_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref_known(v___x_3078_, 1);
v___x_3080_ = l_Lean_Meta_mkProdMkN(v_a_3079_, v_u_3065_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v_fst_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v_fst_3082_ = lean_ctor_get(v_a_3081_, 0);
lean_inc(v_fst_3082_);
lean_dec(v_a_3081_);
v___x_3083_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__7___closed__0));
v___x_3084_ = l_Lean_Name_mkStr2(v___x_3066_, v___x_3083_);
v___x_3085_ = l_Lean_mkConst(v___x_3084_, v___x_3067_);
v___x_3086_ = l_Lean_mkAppB(v___x_3085_, v_snd_3068_, v_fst_3082_);
v___x_3087_ = l_Lean_Elab_Do_mkPureApp(v___x_3069_, v___x_3086_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
return v___x_3087_;
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_snd_3068_);
lean_dec(v___x_3067_);
lean_dec_ref(v___x_3066_);
v_a_3088_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3080_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3080_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_snd_3068_);
lean_dec(v___x_3067_);
lean_dec_ref(v___x_3066_);
lean_dec(v_u_3065_);
v_a_3096_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3078_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3078_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___f_3104_, lean_object* v___x_3105_, lean_object* v_u_3106_, lean_object* v___x_3107_, lean_object* v___x_3108_, lean_object* v_snd_3109_, lean_object* v___x_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___f_3104_, v___x_3105_, v_u_3106_, v___x_3107_, v___x_3108_, v_snd_3109_, v___x_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3111_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v___f_3120_, lean_object* v___x_3121_, lean_object* v_u_3122_, lean_object* v___x_3123_, lean_object* v___x_3124_, lean_object* v_snd_3125_, lean_object* v___x_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___x_3135_; 
lean_inc(v___y_3133_);
lean_inc_ref(v___y_3132_);
lean_inc(v___y_3131_);
lean_inc_ref(v___y_3130_);
lean_inc(v___y_3129_);
lean_inc_ref(v___y_3128_);
v___x_3135_ = lean_apply_8(v___f_3120_, v___x_3121_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, lean_box(0));
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3135_, 1);
v___x_3137_ = l_Lean_Meta_mkProdMkN(v_a_3136_, v_u_3122_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v_fst_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v_fst_3139_ = lean_ctor_get(v_a_3138_, 0);
lean_inc(v_fst_3139_);
lean_dec(v_a_3138_);
v___x_3140_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_3141_ = l_Lean_Name_mkStr2(v___x_3123_, v___x_3140_);
v___x_3142_ = l_Lean_mkConst(v___x_3141_, v___x_3124_);
v___x_3143_ = l_Lean_mkAppB(v___x_3142_, v_snd_3125_, v_fst_3139_);
v___x_3144_ = l_Lean_Elab_Do_mkPureApp(v___x_3126_, v___x_3143_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
return v___x_3144_;
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v___x_3126_);
lean_dec_ref(v_snd_3125_);
lean_dec(v___x_3124_);
lean_dec_ref(v___x_3123_);
v_a_3145_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3137_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3137_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v___x_3126_);
lean_dec_ref(v_snd_3125_);
lean_dec(v___x_3124_);
lean_dec_ref(v___x_3123_);
lean_dec(v_u_3122_);
v_a_3153_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3135_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3135_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object* v___f_3161_, lean_object* v___x_3162_, lean_object* v_u_3163_, lean_object* v___x_3164_, lean_object* v___x_3165_, lean_object* v_snd_3166_, lean_object* v___x_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_Elab_Do_elabDoFor___lam__8(v___f_3161_, v___x_3162_, v_u_3163_, v___x_3164_, v___x_3165_, v_snd_3166_, v___x_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec_ref(v___y_3168_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v___x_3177_, lean_object* v___f_3178_, lean_object* v___f_3179_, lean_object* v___x_3180_, lean_object* v___x_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_monadInfo_3190_; lean_object* v_mutVars_3191_; lean_object* v_mutVarDefs_3192_; lean_object* v_contInfo_3193_; uint8_t v_deadCode_3194_; lean_object* v_ops_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3203_; 
v_monadInfo_3190_ = lean_ctor_get(v___y_3182_, 0);
v_mutVars_3191_ = lean_ctor_get(v___y_3182_, 1);
v_mutVarDefs_3192_ = lean_ctor_get(v___y_3182_, 2);
v_contInfo_3193_ = lean_ctor_get(v___y_3182_, 4);
v_deadCode_3194_ = lean_ctor_get_uint8(v___y_3182_, sizeof(void*)*6);
v_ops_3195_ = lean_ctor_get(v___y_3182_, 5);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___y_3182_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v___y_3182_, 3);
lean_dec(v_unused_3204_);
v___x_3197_ = v___y_3182_;
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_ops_3195_);
lean_inc(v_contInfo_3193_);
lean_inc(v_mutVarDefs_3192_);
lean_inc(v_mutVars_3191_);
lean_inc(v_monadInfo_3190_);
lean_dec(v___y_3182_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 3, v___x_3177_);
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_monadInfo_3190_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_mutVars_3191_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_mutVarDefs_3192_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3202_, 4, v_contInfo_3193_);
lean_ctor_set(v_reuseFailAlloc_3202_, 5, v_ops_3195_);
lean_ctor_set_uint8(v_reuseFailAlloc_3202_, sizeof(void*)*6, v_deadCode_3194_);
v___x_3200_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_3178_, v___f_3179_, v___x_3180_, v___x_3181_, v___x_3200_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec_ref(v___x_3200_);
return v___x_3201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object* v___x_3205_, lean_object* v___f_3206_, lean_object* v___f_3207_, lean_object* v___x_3208_, lean_object* v___x_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Elab_Do_elabDoFor___lam__9(v___x_3205_, v___f_3206_, v___f_3207_, v___x_3208_, v___x_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_u_3224_, lean_object* v_snd_3225_, lean_object* v___f_3226_, lean_object* v___x_3227_, lean_object* v_body_3228_, uint8_t v___x_3229_, lean_object* v___y_3230_, lean_object* v_xh_3231_, lean_object* v_loopS_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_resultType_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3278_; 
v_resultType_3241_ = lean_ctor_get(v_a_3222_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_a_3222_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; 
v_unused_3279_ = lean_ctor_get(v_a_3222_, 1);
lean_dec(v_unused_3279_);
v___x_3243_ = v_a_3222_;
v_isShared_3244_ = v_isSharedCheck_3278_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_resultType_3241_);
lean_dec(v_a_3222_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3278_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v_resultName_3245_; lean_object* v_resultType_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3276_; 
v_resultName_3245_ = lean_ctor_get(v_a_3223_, 0);
v_resultType_3246_ = lean_ctor_get(v_a_3223_, 1);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_a_3223_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v_a_3223_, 2);
lean_dec(v_unused_3277_);
v___x_3248_ = v_a_3223_;
v_isShared_3249_ = v_isSharedCheck_3276_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_resultType_3246_);
lean_inc(v_resultName_3245_);
lean_dec(v_a_3223_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3276_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___f_3257_; lean_object* v___f_3258_; lean_object* v___f_3259_; lean_object* v___x_3261_; 
v___x_3250_ = l_Lean_Expr_fvarId_x21(v_loopS_3232_);
v___x_3251_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0));
v___x_3252_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_3253_ = lean_box(0);
lean_inc_n(v_u_3224_, 3);
v___x_3254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3254_, 0, v_u_3224_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
lean_inc_ref_n(v___x_3254_, 3);
v___x_3255_ = l_Lean_mkConst(v___x_3252_, v___x_3254_);
lean_inc_ref_n(v_snd_3225_, 3);
v___x_3256_ = l_Lean_Expr_app___override(v___x_3255_, v_snd_3225_);
lean_inc_ref_n(v___x_3256_, 3);
lean_inc_ref_n(v___f_3226_, 2);
v___f_3257_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 6);
lean_closure_set(v___f_3257_, 0, v___f_3226_);
lean_closure_set(v___f_3257_, 1, v_u_3224_);
lean_closure_set(v___f_3257_, 2, v___x_3251_);
lean_closure_set(v___f_3257_, 3, v___x_3254_);
lean_closure_set(v___f_3257_, 4, v_snd_3225_);
lean_closure_set(v___f_3257_, 5, v___x_3256_);
lean_inc(v___x_3227_);
v___f_3258_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 15, 7);
lean_closure_set(v___f_3258_, 0, v___f_3226_);
lean_closure_set(v___f_3258_, 1, v___x_3227_);
lean_closure_set(v___f_3258_, 2, v_u_3224_);
lean_closure_set(v___f_3258_, 3, v___x_3251_);
lean_closure_set(v___f_3258_, 4, v___x_3254_);
lean_closure_set(v___f_3258_, 5, v_snd_3225_);
lean_closure_set(v___f_3258_, 6, v___x_3256_);
v___f_3259_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 15, 7);
lean_closure_set(v___f_3259_, 0, v___f_3226_);
lean_closure_set(v___f_3259_, 1, v___x_3227_);
lean_closure_set(v___f_3259_, 2, v_u_3224_);
lean_closure_set(v___f_3259_, 3, v___x_3251_);
lean_closure_set(v___f_3259_, 4, v___x_3254_);
lean_closure_set(v___f_3259_, 5, v_snd_3225_);
lean_closure_set(v___f_3259_, 6, v___x_3256_);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 1, v___f_3257_);
v___x_3261_ = v___x_3243_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_resultType_3241_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v___f_3257_);
v___x_3261_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
uint8_t v___x_3262_; lean_object* v___x_3264_; 
v___x_3262_ = 1;
lean_inc_ref(v___f_3258_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 2, v___f_3258_);
v___x_3264_ = v___x_3248_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_resultName_3245_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_resultType_3246_);
lean_ctor_set(v_reuseFailAlloc_3274_, 2, v___f_3258_);
v___x_3264_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___f_3267_; lean_object* v___x_3268_; 
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*3, v___x_3262_);
v___x_3265_ = lean_box(v___x_3229_);
v___x_3266_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_3266_, 0, v_body_3228_);
lean_closure_set(v___x_3266_, 1, v___x_3264_);
lean_closure_set(v___x_3266_, 2, v___x_3265_);
v___f_3267_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 13, 5);
lean_closure_set(v___f_3267_, 0, v___x_3256_);
lean_closure_set(v___f_3267_, 1, v___f_3259_);
lean_closure_set(v___f_3267_, 2, v___f_3258_);
lean_closure_set(v___f_3267_, 3, v___x_3261_);
lean_closure_set(v___f_3267_, 4, v___x_3266_);
v___x_3268_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_3230_, v___x_3250_, v___f_3267_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; uint8_t v___x_3272_; lean_object* v___x_3273_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = lean_array_push(v_xh_3231_, v_loopS_3232_);
v___x_3271_ = 0;
v___x_3272_ = 1;
v___x_3273_ = l_Lean_Meta_mkLambdaFVars(v___x_3270_, v_a_3269_, v___x_3271_, v___x_3229_, v___x_3271_, v___x_3229_, v___x_3272_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec_ref(v___x_3270_);
return v___x_3273_;
}
else
{
lean_dec_ref(v_loopS_3232_);
lean_dec_ref(v_xh_3231_);
return v___x_3268_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_a_3280_ = _args[0];
lean_object* v_a_3281_ = _args[1];
lean_object* v_u_3282_ = _args[2];
lean_object* v_snd_3283_ = _args[3];
lean_object* v___f_3284_ = _args[4];
lean_object* v___x_3285_ = _args[5];
lean_object* v_body_3286_ = _args[6];
lean_object* v___x_3287_ = _args[7];
lean_object* v___y_3288_ = _args[8];
lean_object* v_xh_3289_ = _args[9];
lean_object* v_loopS_3290_ = _args[10];
lean_object* v___y_3291_ = _args[11];
lean_object* v___y_3292_ = _args[12];
lean_object* v___y_3293_ = _args[13];
lean_object* v___y_3294_ = _args[14];
lean_object* v___y_3295_ = _args[15];
lean_object* v___y_3296_ = _args[16];
lean_object* v___y_3297_ = _args[17];
lean_object* v___y_3298_ = _args[18];
_start:
{
uint8_t v___x_75233__boxed_3299_; lean_object* v_res_3300_; 
v___x_75233__boxed_3299_ = lean_unbox(v___x_3287_);
v_res_3300_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_a_3280_, v_a_3281_, v_u_3282_, v_snd_3283_, v___f_3284_, v___x_3285_, v_body_3286_, v___x_75233__boxed_3299_, v___y_3288_, v_xh_3289_, v_loopS_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___x_3301_, lean_object* v___x_3302_, lean_object* v_x_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_u_3306_, lean_object* v_snd_3307_, lean_object* v___f_3308_, lean_object* v___x_3309_, lean_object* v_body_3310_, uint8_t v___x_3311_, lean_object* v___y_3312_, lean_object* v_a_3313_, lean_object* v_h_x3f_3314_, lean_object* v___x_3315_, lean_object* v_xh_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_array_get_borrowed(v___x_3301_, v_xh_3316_, v___x_3302_);
lean_inc(v___x_3325_);
v___x_3326_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_3303_, v___x_3325_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v___x_3327_; lean_object* v___f_3328_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; 
lean_dec_ref_known(v___x_3326_, 1);
v___x_3327_ = lean_box(v___x_3311_);
lean_inc_ref(v_xh_3316_);
lean_inc_ref(v_snd_3307_);
v___f_3328_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 10);
lean_closure_set(v___f_3328_, 0, v_a_3304_);
lean_closure_set(v___f_3328_, 1, v_a_3305_);
lean_closure_set(v___f_3328_, 2, v_u_3306_);
lean_closure_set(v___f_3328_, 3, v_snd_3307_);
lean_closure_set(v___f_3328_, 4, v___f_3308_);
lean_closure_set(v___f_3328_, 5, v___x_3309_);
lean_closure_set(v___f_3328_, 6, v_body_3310_);
lean_closure_set(v___f_3328_, 7, v___x_3327_);
lean_closure_set(v___f_3328_, 8, v___y_3312_);
lean_closure_set(v___f_3328_, 9, v_xh_3316_);
if (lean_obj_tag(v_h_x3f_3314_) == 1)
{
lean_object* v_val_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_val_3340_ = lean_ctor_get(v_h_x3f_3314_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v_h_x3f_3314_, 1);
v___x_3341_ = lean_array_get(v___x_3301_, v_xh_3316_, v___x_3315_);
lean_dec_ref(v_xh_3316_);
v___x_3342_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_3340_, v___x_3341_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_dec_ref_known(v___x_3342_, 1);
v___y_3330_ = v___y_3317_;
v___y_3331_ = v___y_3318_;
v___y_3332_ = v___y_3319_;
v___y_3333_ = v___y_3320_;
v___y_3334_ = v___y_3321_;
v___y_3335_ = v___y_3322_;
v___y_3336_ = v___y_3323_;
goto v___jp_3329_;
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec_ref(v___f_3328_);
lean_dec(v_a_3313_);
lean_dec_ref(v_snd_3307_);
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_dec_ref(v_xh_3316_);
lean_dec(v_h_x3f_3314_);
v___y_3330_ = v___y_3317_;
v___y_3331_ = v___y_3318_;
v___y_3332_ = v___y_3319_;
v___y_3333_ = v___y_3320_;
v___y_3334_ = v___y_3321_;
v___y_3335_ = v___y_3322_;
v___y_3336_ = v___y_3323_;
goto v___jp_3329_;
}
v___jp_3329_:
{
uint8_t v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = 0;
v___x_3338_ = 1;
v___x_3339_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_3313_, v___x_3337_, v_snd_3307_, v___f_3328_, v___x_3338_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
return v___x_3339_;
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec_ref(v_xh_3316_);
lean_dec(v_h_x3f_3314_);
lean_dec(v_a_3313_);
lean_dec(v___y_3312_);
lean_dec(v_body_3310_);
lean_dec(v___x_3309_);
lean_dec_ref(v___f_3308_);
lean_dec_ref(v_snd_3307_);
lean_dec(v_u_3306_);
lean_dec_ref(v_a_3305_);
lean_dec_ref(v_a_3304_);
v_a_3351_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3326_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3326_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object** _args){
lean_object* v___x_3359_ = _args[0];
lean_object* v___x_3360_ = _args[1];
lean_object* v_x_3361_ = _args[2];
lean_object* v_a_3362_ = _args[3];
lean_object* v_a_3363_ = _args[4];
lean_object* v_u_3364_ = _args[5];
lean_object* v_snd_3365_ = _args[6];
lean_object* v___f_3366_ = _args[7];
lean_object* v___x_3367_ = _args[8];
lean_object* v_body_3368_ = _args[9];
lean_object* v___x_3369_ = _args[10];
lean_object* v___y_3370_ = _args[11];
lean_object* v_a_3371_ = _args[12];
lean_object* v_h_x3f_3372_ = _args[13];
lean_object* v___x_3373_ = _args[14];
lean_object* v_xh_3374_ = _args[15];
lean_object* v___y_3375_ = _args[16];
lean_object* v___y_3376_ = _args[17];
lean_object* v___y_3377_ = _args[18];
lean_object* v___y_3378_ = _args[19];
lean_object* v___y_3379_ = _args[20];
lean_object* v___y_3380_ = _args[21];
lean_object* v___y_3381_ = _args[22];
lean_object* v___y_3382_ = _args[23];
_start:
{
uint8_t v___x_75356__boxed_3383_; lean_object* v_res_3384_; 
v___x_75356__boxed_3383_ = lean_unbox(v___x_3369_);
v_res_3384_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___x_3359_, v___x_3360_, v_x_3361_, v_a_3362_, v_a_3363_, v_u_3364_, v_snd_3365_, v___f_3366_, v___x_3367_, v_body_3368_, v___x_75356__boxed_3383_, v___y_3370_, v_a_3371_, v_h_x3f_3372_, v___x_3373_, v_xh_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___x_3373_);
lean_dec(v___x_3360_);
lean_dec_ref(v___x_3359_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v___x_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_val_3395_, lean_object* v_a_3396_, lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3406_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_3407_ = lean_box(0);
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v_a_3390_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3409_, 0, v_a_3391_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = l_Lean_mkConst(v___x_3406_, v___x_3409_);
v___x_3411_ = l_Lean_instInhabitedExpr;
v___x_3412_ = lean_array_get_borrowed(v___x_3411_, v_x_3397_, v___x_3392_);
lean_inc(v___x_3412_);
v___x_3413_ = l_Lean_mkApp5(v___x_3410_, v_a_3393_, v_a_3394_, v_val_3395_, v_a_3396_, v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v___x_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_val_3420_, lean_object* v_a_3421_, lean_object* v_x_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_3415_, v_a_3416_, v___x_3417_, v_a_3418_, v_a_3419_, v_val_3420_, v_a_3421_, v_x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec_ref(v_x_3422_);
lean_dec(v___x_3417_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(size_t v_sz_3432_, size_t v_i_3433_, lean_object* v_bs_3434_){
_start:
{
uint8_t v___x_3435_; 
v___x_3435_ = lean_usize_dec_lt(v_i_3433_, v_sz_3432_);
if (v___x_3435_ == 0)
{
return v_bs_3434_;
}
else
{
lean_object* v_v_3436_; lean_object* v___x_3437_; lean_object* v_bs_x27_3438_; lean_object* v___x_3439_; size_t v___x_3440_; size_t v___x_3441_; lean_object* v___x_3442_; 
v_v_3436_ = lean_array_uget(v_bs_3434_, v_i_3433_);
v___x_3437_ = lean_unsigned_to_nat(0u);
v_bs_x27_3438_ = lean_array_uset(v_bs_3434_, v_i_3433_, v___x_3437_);
v___x_3439_ = l_Lean_Elab_Do_MutVar_getId(v_v_3436_);
lean_dec(v_v_3436_);
v___x_3440_ = ((size_t)1ULL);
v___x_3441_ = lean_usize_add(v_i_3433_, v___x_3440_);
v___x_3442_ = lean_array_uset(v_bs_x27_3438_, v_i_3433_, v___x_3439_);
v_i_3433_ = v___x_3441_;
v_bs_3434_ = v___x_3442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_sz_3444_, lean_object* v_i_3445_, lean_object* v_bs_3446_){
_start:
{
size_t v_sz_boxed_3447_; size_t v_i_boxed_3448_; lean_object* v_res_3449_; 
v_sz_boxed_3447_ = lean_unbox_usize(v_sz_3444_);
lean_dec(v_sz_3444_);
v_i_boxed_3448_ = lean_unbox_usize(v_i_3445_);
lean_dec(v_i_3445_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_boxed_3447_, v_i_boxed_3448_, v_bs_3446_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_a_3450_, lean_object* v_as_3451_, size_t v_i_3452_, size_t v_stop_3453_, lean_object* v_b_3454_){
_start:
{
lean_object* v___y_3456_; uint8_t v___x_3460_; 
v___x_3460_ = lean_usize_dec_eq(v_i_3452_, v_stop_3453_);
if (v___x_3460_ == 0)
{
lean_object* v_reassigns_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v_reassigns_3461_ = lean_ctor_get(v_a_3450_, 1);
v___x_3462_ = lean_array_uget_borrowed(v_as_3451_, v_i_3452_);
v___x_3463_ = l_Lean_Elab_Do_MutVar_getId(v___x_3462_);
v___x_3464_ = l_Lean_NameSet_contains(v_reassigns_3461_, v___x_3463_);
lean_dec(v___x_3463_);
if (v___x_3464_ == 0)
{
v___y_3456_ = v_b_3454_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3465_; 
lean_inc(v___x_3462_);
v___x_3465_ = lean_array_push(v_b_3454_, v___x_3462_);
v___y_3456_ = v___x_3465_;
goto v___jp_3455_;
}
}
else
{
return v_b_3454_;
}
v___jp_3455_:
{
size_t v___x_3457_; size_t v___x_3458_; 
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_add(v_i_3452_, v___x_3457_);
v_i_3452_ = v___x_3458_;
v_b_3454_ = v___y_3456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_a_3466_, lean_object* v_as_3467_, lean_object* v_i_3468_, lean_object* v_stop_3469_, lean_object* v_b_3470_){
_start:
{
size_t v_i_boxed_3471_; size_t v_stop_boxed_3472_; lean_object* v_res_3473_; 
v_i_boxed_3471_ = lean_unbox_usize(v_i_3468_);
lean_dec(v_i_3468_);
v_stop_boxed_3472_ = lean_unbox_usize(v_stop_3469_);
lean_dec(v_stop_3469_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_3466_, v_as_3467_, v_i_boxed_3471_, v_stop_boxed_3472_, v_b_3470_);
lean_dec_ref(v_as_3467_);
lean_dec_ref(v_a_3466_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(lean_object* v___x_3474_, lean_object* v_a_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; lean_object* v___x_73796__overap_3485_; lean_object* v___x_3486_; 
v___x_3484_ = l_Lean_instInhabitedExpr;
v___x_73796__overap_3485_ = l_instInhabitedOfMonad___redArg(v___x_3474_, v___x_3484_);
lean_inc(v___y_3482_);
lean_inc_ref(v___y_3481_);
lean_inc(v___y_3480_);
lean_inc_ref(v___y_3479_);
lean_inc(v___y_3478_);
lean_inc_ref(v___y_3477_);
lean_inc_ref(v___y_3476_);
v___x_3486_ = lean_apply_8(v___x_73796__overap_3485_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, lean_box(0));
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed(lean_object* v___x_3487_, lean_object* v_a_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(v___x_3487_, v_a_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec_ref(v_a_3488_);
return v_res_3497_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_instMonadEIO(lean_box(0));
return v___x_3498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0);
v___x_3500_ = l_StateRefT_x27_instMonad___redArg(v___x_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed(lean_object* v_acc_3507_, lean_object* v_declInfos_3508_, lean_object* v_k_3509_, lean_object* v_kind_3510_, lean_object* v_x_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
uint8_t v_kind_boxed_3520_; lean_object* v_res_3521_; 
v_kind_boxed_3520_ = lean_unbox(v_kind_3510_);
v_res_3521_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(v_acc_3507_, v_declInfos_3508_, v_k_3509_, v_kind_boxed_3520_, v_x_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v___y_3512_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(lean_object* v_declInfos_3522_, lean_object* v_k_3523_, uint8_t v_kind_3524_, lean_object* v_acc_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; lean_object* v_toApplicative_3535_; lean_object* v_toFunctor_3536_; lean_object* v_toSeq_3537_; lean_object* v_toSeqLeft_3538_; lean_object* v_toSeqRight_3539_; lean_object* v___f_3540_; lean_object* v___f_3541_; lean_object* v___f_3542_; lean_object* v___f_3543_; lean_object* v___x_3544_; lean_object* v___f_3545_; lean_object* v___f_3546_; lean_object* v___f_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v_toApplicative_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3631_; 
v___x_3534_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1);
v_toApplicative_3535_ = lean_ctor_get(v___x_3534_, 0);
v_toFunctor_3536_ = lean_ctor_get(v_toApplicative_3535_, 0);
v_toSeq_3537_ = lean_ctor_get(v_toApplicative_3535_, 2);
v_toSeqLeft_3538_ = lean_ctor_get(v_toApplicative_3535_, 3);
v_toSeqRight_3539_ = lean_ctor_get(v_toApplicative_3535_, 4);
v___f_3540_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2));
v___f_3541_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3536_, 2);
v___f_3542_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3542_, 0, v_toFunctor_3536_);
v___f_3543_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3543_, 0, v_toFunctor_3536_);
v___x_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___f_3542_);
lean_ctor_set(v___x_3544_, 1, v___f_3543_);
lean_inc(v_toSeqRight_3539_);
v___f_3545_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3545_, 0, v_toSeqRight_3539_);
lean_inc(v_toSeqLeft_3538_);
v___f_3546_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3546_, 0, v_toSeqLeft_3538_);
lean_inc(v_toSeq_3537_);
v___f_3547_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3547_, 0, v_toSeq_3537_);
v___x_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3544_);
lean_ctor_set(v___x_3548_, 1, v___f_3540_);
lean_ctor_set(v___x_3548_, 2, v___f_3547_);
lean_ctor_set(v___x_3548_, 3, v___f_3546_);
lean_ctor_set(v___x_3548_, 4, v___f_3545_);
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___f_3541_);
v___x_3550_ = l_StateRefT_x27_instMonad___redArg(v___x_3549_);
v_toApplicative_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v___x_3550_, 1);
lean_dec(v_unused_3632_);
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3631_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_toApplicative_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3631_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v_toFunctor_3555_; lean_object* v_toSeq_3556_; lean_object* v_toSeqLeft_3557_; lean_object* v_toSeqRight_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3629_; 
v_toFunctor_3555_ = lean_ctor_get(v_toApplicative_3551_, 0);
v_toSeq_3556_ = lean_ctor_get(v_toApplicative_3551_, 2);
v_toSeqLeft_3557_ = lean_ctor_get(v_toApplicative_3551_, 3);
v_toSeqRight_3558_ = lean_ctor_get(v_toApplicative_3551_, 4);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_toApplicative_3551_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_toApplicative_3551_, 1);
lean_dec(v_unused_3630_);
v___x_3560_ = v_toApplicative_3551_;
v_isShared_3561_ = v_isSharedCheck_3629_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_toSeqRight_3558_);
lean_inc(v_toSeqLeft_3557_);
lean_inc(v_toSeq_3556_);
lean_inc(v_toFunctor_3555_);
lean_dec(v_toApplicative_3551_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3629_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___f_3562_; lean_object* v___f_3563_; lean_object* v___f_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; lean_object* v___f_3567_; lean_object* v___f_3568_; lean_object* v___f_3569_; lean_object* v___x_3571_; 
v___f_3562_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4));
v___f_3563_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3555_);
v___f_3564_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3564_, 0, v_toFunctor_3555_);
v___f_3565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3565_, 0, v_toFunctor_3555_);
v___x_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___f_3564_);
lean_ctor_set(v___x_3566_, 1, v___f_3565_);
v___f_3567_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3567_, 0, v_toSeqRight_3558_);
v___f_3568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3568_, 0, v_toSeqLeft_3557_);
v___f_3569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3569_, 0, v_toSeq_3556_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 4, v___f_3567_);
lean_ctor_set(v___x_3560_, 3, v___f_3568_);
lean_ctor_set(v___x_3560_, 2, v___f_3569_);
lean_ctor_set(v___x_3560_, 1, v___f_3562_);
lean_ctor_set(v___x_3560_, 0, v___x_3566_);
v___x_3571_ = v___x_3560_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v___f_3562_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v___f_3569_);
lean_ctor_set(v_reuseFailAlloc_3628_, 3, v___f_3568_);
lean_ctor_set(v_reuseFailAlloc_3628_, 4, v___f_3567_);
v___x_3571_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3573_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 1, v___f_3563_);
lean_ctor_set(v___x_3553_, 0, v___x_3571_);
v___x_3573_ = v___x_3553_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___f_3563_);
v___x_3573_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
lean_object* v___x_3574_; lean_object* v_toApplicative_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3625_; 
v___x_3574_ = l_StateRefT_x27_instMonad___redArg(v___x_3573_);
v_toApplicative_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; 
v_unused_3626_ = lean_ctor_get(v___x_3574_, 1);
lean_dec(v_unused_3626_);
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3625_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_toApplicative_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3625_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v_toFunctor_3579_; lean_object* v_toSeq_3580_; lean_object* v_toSeqLeft_3581_; lean_object* v_toSeqRight_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3623_; 
v_toFunctor_3579_ = lean_ctor_get(v_toApplicative_3575_, 0);
v_toSeq_3580_ = lean_ctor_get(v_toApplicative_3575_, 2);
v_toSeqLeft_3581_ = lean_ctor_get(v_toApplicative_3575_, 3);
v_toSeqRight_3582_ = lean_ctor_get(v_toApplicative_3575_, 4);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_toApplicative_3575_);
if (v_isSharedCheck_3623_ == 0)
{
lean_object* v_unused_3624_; 
v_unused_3624_ = lean_ctor_get(v_toApplicative_3575_, 1);
lean_dec(v_unused_3624_);
v___x_3584_ = v_toApplicative_3575_;
v_isShared_3585_ = v_isSharedCheck_3623_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_toSeqRight_3582_);
lean_inc(v_toSeqLeft_3581_);
lean_inc(v_toSeq_3580_);
lean_inc(v_toFunctor_3579_);
lean_dec(v_toApplicative_3575_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3623_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___x_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3595_; 
v___f_3586_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6));
v___f_3587_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7));
lean_inc_ref(v_toFunctor_3579_);
v___f_3588_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3588_, 0, v_toFunctor_3579_);
v___f_3589_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3589_, 0, v_toFunctor_3579_);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___f_3588_);
lean_ctor_set(v___x_3590_, 1, v___f_3589_);
v___f_3591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3591_, 0, v_toSeqRight_3582_);
v___f_3592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3592_, 0, v_toSeqLeft_3581_);
v___f_3593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3593_, 0, v_toSeq_3580_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 4, v___f_3591_);
lean_ctor_set(v___x_3584_, 3, v___f_3592_);
lean_ctor_set(v___x_3584_, 2, v___f_3593_);
lean_ctor_set(v___x_3584_, 1, v___f_3586_);
lean_ctor_set(v___x_3584_, 0, v___x_3590_);
v___x_3595_ = v___x_3584_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v___f_3586_);
lean_ctor_set(v_reuseFailAlloc_3622_, 2, v___f_3593_);
lean_ctor_set(v_reuseFailAlloc_3622_, 3, v___f_3592_);
lean_ctor_set(v_reuseFailAlloc_3622_, 4, v___f_3591_);
v___x_3595_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v___f_3587_);
lean_ctor_set(v___x_3577_, 0, v___x_3595_);
v___x_3597_ = v___x_3577_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___f_3587_);
v___x_3597_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3598_ = l_ReaderT_instMonad___redArg(v___x_3597_);
v___x_3599_ = lean_array_get_size(v_acc_3525_);
v___x_3600_ = lean_array_get_size(v_declInfos_3522_);
v___x_3601_ = lean_nat_dec_lt(v___x_3599_, v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; 
lean_dec_ref(v___x_3598_);
lean_dec_ref(v_declInfos_3522_);
lean_inc(v___y_3532_);
lean_inc_ref(v___y_3531_);
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3529_);
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
lean_inc_ref(v___y_3526_);
v___x_3602_ = lean_apply_9(v_k_3523_, v_acc_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, lean_box(0));
return v___x_3602_;
}
else
{
lean_object* v___f_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v_snd_3611_; lean_object* v_fst_3612_; lean_object* v_fst_3613_; lean_object* v_snd_3614_; lean_object* v___x_3615_; 
v___f_3603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3603_, 0, v___x_3598_);
v___x_3604_ = lean_box(0);
v___x_3605_ = 0;
v___f_3606_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3606_, 0, v___f_3603_);
v___x_3607_ = lean_box(v___x_3605_);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v___f_3606_);
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3604_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_array_get(v___x_3609_, v_declInfos_3522_, v___x_3599_);
lean_dec_ref_known(v___x_3609_, 2);
v_snd_3611_ = lean_ctor_get(v___x_3610_, 1);
lean_inc(v_snd_3611_);
v_fst_3612_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_fst_3612_);
lean_dec(v___x_3610_);
v_fst_3613_ = lean_ctor_get(v_snd_3611_, 0);
lean_inc(v_fst_3613_);
v_snd_3614_ = lean_ctor_get(v_snd_3611_, 1);
lean_inc(v_snd_3614_);
lean_dec(v_snd_3611_);
lean_inc(v___y_3532_);
lean_inc_ref(v___y_3531_);
lean_inc(v___y_3530_);
lean_inc_ref(v___y_3529_);
lean_inc(v___y_3528_);
lean_inc_ref(v___y_3527_);
lean_inc_ref(v___y_3526_);
lean_inc_ref(v_acc_3525_);
v___x_3615_ = lean_apply_9(v_snd_3614_, v_acc_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, lean_box(0));
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3617_; lean_object* v___f_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v___x_3617_ = lean_box(v_kind_3524_);
v___f_3618_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3618_, 0, v_acc_3525_);
lean_closure_set(v___f_3618_, 1, v_declInfos_3522_);
lean_closure_set(v___f_3618_, 2, v_k_3523_);
lean_closure_set(v___f_3618_, 3, v___x_3617_);
v___x_3619_ = lean_unbox(v_fst_3613_);
lean_dec(v_fst_3613_);
v___x_3620_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_3612_, v___x_3619_, v_a_3616_, v___f_3618_, v_kind_3524_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
return v___x_3620_;
}
else
{
lean_dec(v_fst_3613_);
lean_dec(v_fst_3612_);
lean_dec_ref(v_acc_3525_);
lean_dec_ref(v_k_3523_);
lean_dec_ref(v_declInfos_3522_);
return v___x_3615_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(lean_object* v_acc_3633_, lean_object* v_declInfos_3634_, lean_object* v_k_3635_, uint8_t v_kind_3636_, lean_object* v_x_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_array_push(v_acc_3633_, v_x_3637_);
v___x_3647_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_3634_, v_k_3635_, v_kind_3636_, v___x_3646_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___boxed(lean_object* v_declInfos_3648_, lean_object* v_k_3649_, lean_object* v_kind_3650_, lean_object* v_acc_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
uint8_t v_kind_boxed_3660_; lean_object* v_res_3661_; 
v_kind_boxed_3660_ = lean_unbox(v_kind_3650_);
v_res_3661_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_3648_, v_k_3649_, v_kind_boxed_3660_, v_acc_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec_ref(v___y_3652_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(lean_object* v_declInfos_3664_, lean_object* v_k_3665_, uint8_t v_kind_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0));
v___x_3676_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_3664_, v_k_3665_, v_kind_3666_, v___x_3675_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_declInfos_3677_, lean_object* v_k_3678_, lean_object* v_kind_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
uint8_t v_kind_boxed_3688_; lean_object* v_res_3689_; 
v_kind_boxed_3688_ = lean_unbox(v_kind_3679_);
v_res_3689_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_declInfos_3677_, v_k_3678_, v_kind_boxed_3688_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec_ref(v___y_3680_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(size_t v_sz_3690_, size_t v_i_3691_, lean_object* v_bs_3692_){
_start:
{
uint8_t v___x_3693_; 
v___x_3693_ = lean_usize_dec_lt(v_i_3691_, v_sz_3690_);
if (v___x_3693_ == 0)
{
return v_bs_3692_;
}
else
{
lean_object* v_v_3694_; lean_object* v_fst_3695_; lean_object* v_snd_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3712_; 
v_v_3694_ = lean_array_uget(v_bs_3692_, v_i_3691_);
v_fst_3695_ = lean_ctor_get(v_v_3694_, 0);
v_snd_3696_ = lean_ctor_get(v_v_3694_, 1);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_v_3694_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3698_ = v_v_3694_;
v_isShared_3699_ = v_isSharedCheck_3712_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_snd_3696_);
lean_inc(v_fst_3695_);
lean_dec(v_v_3694_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3712_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v_bs_x27_3701_; uint8_t v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3700_ = lean_unsigned_to_nat(0u);
v_bs_x27_3701_ = lean_array_uset(v_bs_3692_, v_i_3691_, v___x_3700_);
v___x_3702_ = 0;
v___x_3703_ = lean_box(v___x_3702_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3703_);
v___x_3705_ = v___x_3698_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_snd_3696_);
v___x_3705_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; size_t v___x_3707_; size_t v___x_3708_; lean_object* v___x_3709_; 
v___x_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3706_, 0, v_fst_3695_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = ((size_t)1ULL);
v___x_3708_ = lean_usize_add(v_i_3691_, v___x_3707_);
v___x_3709_ = lean_array_uset(v_bs_x27_3701_, v_i_3691_, v___x_3706_);
v_i_3691_ = v___x_3708_;
v_bs_3692_ = v___x_3709_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5___boxed(lean_object* v_sz_3713_, lean_object* v_i_3714_, lean_object* v_bs_3715_){
_start:
{
size_t v_sz_boxed_3716_; size_t v_i_boxed_3717_; lean_object* v_res_3718_; 
v_sz_boxed_3716_ = lean_unbox_usize(v_sz_3713_);
lean_dec(v_sz_3713_);
v_i_boxed_3717_ = lean_unbox_usize(v_i_3714_);
lean_dec(v_i_3714_);
v_res_3718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_boxed_3716_, v_i_boxed_3717_, v_bs_3715_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_3719_, lean_object* v_k_3720_, uint8_t v_kind_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
size_t v_sz_3730_; size_t v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v_sz_3730_ = lean_array_size(v_declInfos_3719_);
v___x_3731_ = ((size_t)0ULL);
v___x_3732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_3730_, v___x_3731_, v_declInfos_3719_);
v___x_3733_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v___x_3732_, v_k_3720_, v_kind_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_3734_, lean_object* v_k_3735_, lean_object* v_kind_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
uint8_t v_kind_boxed_3745_; lean_object* v_res_3746_; 
v_kind_boxed_3745_ = lean_unbox(v_kind_3736_);
v_res_3746_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_3734_, v_k_3735_, v_kind_boxed_3745_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec_ref(v___y_3737_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_3775_, lean_object* v_dec_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3785_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_3775_);
v___x_3786_ = l_Lean_Syntax_isOfKind(v_stx_3775_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; 
lean_dec_ref(v_dec_3776_);
lean_dec(v_stx_3775_);
v___x_3787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_3787_;
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v___x_3788_ = lean_unsigned_to_nat(1u);
v___x_3789_ = l_Lean_Syntax_getArg(v_stx_3775_, v___x_3788_);
lean_inc(v___x_3789_);
v___x_3790_ = l_Lean_Syntax_matchesNull(v___x_3789_, v___x_3788_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_dec(v___x_3789_);
lean_dec_ref(v_dec_3776_);
lean_dec(v_stx_3775_);
v___x_3791_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_3791_;
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; uint8_t v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v_forIn_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; uint8_t v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; uint8_t v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; uint8_t v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; uint8_t v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; uint8_t v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; uint8_t v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v_fst_3939_; lean_object* v_snd_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; uint8_t v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; uint8_t v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; uint8_t v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; uint8_t v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; 
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = l_Lean_Syntax_getArg(v___x_3789_, v___x_3792_);
lean_dec(v___x_3789_);
v___x_3794_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_3793_);
v___x_3795_ = l_Lean_Syntax_isOfKind(v___x_3793_, v___x_3794_);
if (v___x_3795_ == 0)
{
lean_object* v___x_4143_; 
lean_dec(v___x_3793_);
lean_dec_ref(v_dec_3776_);
lean_dec(v_stx_3775_);
v___x_4143_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4143_;
}
else
{
lean_object* v_tk_4144_; lean_object* v___y_4146_; uint8_t v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v_inv_x3f_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v_h_x3f_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v_tk_4144_ = l_Lean_Syntax_getArg(v_stx_3775_, v___x_3792_);
v___x_4306_ = l_Lean_Syntax_getArg(v___x_3793_, v___x_3792_);
v___x_4307_ = l_Lean_Syntax_isNone(v___x_4306_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4308_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4306_);
v___x_4309_ = l_Lean_Syntax_matchesNull(v___x_4306_, v___x_4308_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4310_; 
lean_dec(v___x_4306_);
lean_dec(v_tk_4144_);
lean_dec(v___x_3793_);
lean_dec_ref(v_dec_3776_);
lean_dec(v_stx_3775_);
v___x_4310_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4310_;
}
else
{
lean_object* v_h_x3f_4311_; lean_object* v___x_4312_; 
v_h_x3f_4311_ = l_Lean_Syntax_getArg(v___x_4306_, v___x_3792_);
lean_dec(v___x_4306_);
v___x_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4312_, 0, v_h_x3f_4311_);
v_h_x3f_4281_ = v___x_4312_;
v___y_4282_ = v_a_3777_;
v___y_4283_ = v_a_3778_;
v___y_4284_ = v_a_3779_;
v___y_4285_ = v_a_3780_;
v___y_4286_ = v_a_3781_;
v___y_4287_ = v_a_3782_;
v___y_4288_ = v_a_3783_;
goto v___jp_4280_;
}
}
else
{
lean_object* v___x_4313_; 
lean_dec(v___x_4306_);
v___x_4313_ = lean_box(0);
v_h_x3f_4281_ = v___x_4313_;
v___y_4282_ = v_a_3777_;
v___y_4283_ = v_a_3778_;
v___y_4284_ = v_a_3779_;
v___y_4285_ = v_a_3780_;
v___y_4286_ = v_a_3781_;
v___y_4287_ = v_a_3782_;
v___y_4288_ = v_a_3783_;
goto v___jp_4280_;
}
v___jp_4145_:
{
lean_object* v___x_4161_; 
v___x_4161_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3776_, v_tk_4144_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec(v_tk_4144_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4161_, 1);
v___x_4163_ = lean_mk_empty_array_with_capacity(v___x_3788_);
lean_inc(v___y_4152_);
v___x_4164_ = lean_array_push(v___x_4163_, v___y_4152_);
v___x_4165_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_4164_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec_ref(v___x_4164_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v___x_4166_; 
lean_dec_ref_known(v___x_4165_, 1);
v___x_4166_ = l_Lean_Meta_mkFreshLevelMVar(v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = l_Lean_Meta_mkFreshLevelMVar(v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4168_, 1);
lean_inc(v_a_4167_);
v___x_4170_ = l_Lean_Level_succ___override(v_a_4167_);
v___x_4171_ = l_Lean_mkSort(v___x_4170_);
v___x_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
v___x_4173_ = 0;
v___x_4174_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_4175_ = l_Lean_Meta_mkFreshExprMVar(v___x_4172_, v___x_4173_, v___x_4174_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4247_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4247_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4247_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
lean_inc(v_a_4169_);
v___x_4180_ = l_Lean_Level_succ___override(v_a_4169_);
v___x_4181_ = l_Lean_mkSort(v___x_4180_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set_tag(v___x_4178_, 1);
lean_ctor_set(v___x_4178_, 0, v___x_4181_);
v___x_4183_ = v___x_4178_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4184_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__12));
v___x_4185_ = l_Lean_Meta_mkFreshExprMVar(v___x_4183_, v___x_4173_, v___x_4184_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4245_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4245_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4245_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
lean_inc(v_a_4186_);
if (v_isShared_4189_ == 0)
{
lean_ctor_set_tag(v___x_4188_, 1);
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = lean_box(0);
v___x_4193_ = l_Lean_Elab_Term_elabTermEnsuringType(v___y_4151_, v___x_4191_, v___x_3795_, v___x_3795_, v___x_4192_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4195_; lean_object* v_body_4196_; lean_object* v___x_4197_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref_known(v___x_4193_, 1);
v___x_4195_ = lean_unsigned_to_nat(4u);
v_body_4196_ = l_Lean_Syntax_getArg(v_stx_3775_, v___x_4195_);
lean_dec(v_stx_3775_);
lean_inc(v_body_4196_);
v___x_4197_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_4196_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
v___x_4199_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_4154_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__14));
v___x_4202_ = l_Lean_Core_mkFreshUserName(v___x_4201_, v___y_4159_, v___y_4160_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v_monadInfo_4204_; lean_object* v_mutVars_4205_; lean_object* v___f_4206_; lean_object* v___f_4207_; lean_object* v___x_4208_; lean_object* v___f_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v_monadInfo_4204_ = lean_ctor_get(v___y_4154_, 0);
v_mutVars_4205_ = lean_ctor_get(v___y_4154_, 1);
lean_inc(v_a_4176_);
v___f_4206_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4206_, 0, v_a_4176_);
lean_inc_ref(v___f_4206_);
lean_inc(v___y_4148_);
v___f_4207_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4207_, 0, v___y_4148_);
lean_closure_set(v___f_4207_, 1, v___f_4206_);
lean_closure_set(v___f_4207_, 2, v___x_3788_);
v___x_4208_ = lean_box(v___x_3795_);
lean_inc(v_a_4200_);
v___f_4209_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 12, 3);
lean_closure_set(v___f_4209_, 0, v_a_4200_);
lean_closure_set(v___f_4209_, 1, v___x_3788_);
lean_closure_set(v___f_4209_, 2, v___x_4208_);
v___x_4210_ = lean_array_get_size(v_mutVars_4205_);
v___x_4211_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__15));
v___x_4212_ = lean_nat_dec_lt(v___x_3792_, v___x_4210_);
if (v___x_4212_ == 0)
{
lean_inc(v_a_4194_);
lean_inc(v_a_4169_);
lean_inc(v_a_4203_);
lean_inc(v_a_4186_);
lean_inc(v_a_4176_);
lean_inc(v_a_4167_);
v___y_4094_ = v_a_4167_;
v___y_4095_ = v___y_4146_;
v___y_4096_ = v_a_4176_;
v___y_4097_ = v_a_4186_;
v___y_4098_ = v___f_4207_;
v___y_4099_ = v_a_4203_;
v___y_4100_ = v_a_4200_;
v___y_4101_ = v_monadInfo_4204_;
v___y_4102_ = v___f_4209_;
v___y_4103_ = v_a_4169_;
v___y_4104_ = v___y_4147_;
v___y_4105_ = v_body_4196_;
v___y_4106_ = v___y_4148_;
v___y_4107_ = v_a_4194_;
v___y_4108_ = v_a_4162_;
v___y_4109_ = v___f_4206_;
v___y_4110_ = v_a_4167_;
v___y_4111_ = v___y_4156_;
v___y_4112_ = v___y_4149_;
v___y_4113_ = v_a_4176_;
v___y_4114_ = v___y_4157_;
v___y_4115_ = v___y_4159_;
v___y_4116_ = v___y_4155_;
v___y_4117_ = v___y_4154_;
v___y_4118_ = v_a_4186_;
v___y_4119_ = v___y_4158_;
v___y_4120_ = v_a_4203_;
v___y_4121_ = v_a_4169_;
v___y_4122_ = v___y_4152_;
v___y_4123_ = v___y_4150_;
v___y_4124_ = v_a_4198_;
v___y_4125_ = v___y_4160_;
v___y_4126_ = v_a_4194_;
v___y_4127_ = v___x_4173_;
v___y_4128_ = v_inv_x3f_4153_;
v___y_4129_ = v___x_4211_;
goto v___jp_4093_;
}
else
{
uint8_t v___x_4213_; 
v___x_4213_ = lean_nat_dec_le(v___x_4210_, v___x_4210_);
if (v___x_4213_ == 0)
{
if (v___x_4212_ == 0)
{
lean_inc(v_a_4194_);
lean_inc(v_a_4169_);
lean_inc(v_a_4203_);
lean_inc(v_a_4186_);
lean_inc(v_a_4176_);
lean_inc(v_a_4167_);
v___y_4094_ = v_a_4167_;
v___y_4095_ = v___y_4146_;
v___y_4096_ = v_a_4176_;
v___y_4097_ = v_a_4186_;
v___y_4098_ = v___f_4207_;
v___y_4099_ = v_a_4203_;
v___y_4100_ = v_a_4200_;
v___y_4101_ = v_monadInfo_4204_;
v___y_4102_ = v___f_4209_;
v___y_4103_ = v_a_4169_;
v___y_4104_ = v___y_4147_;
v___y_4105_ = v_body_4196_;
v___y_4106_ = v___y_4148_;
v___y_4107_ = v_a_4194_;
v___y_4108_ = v_a_4162_;
v___y_4109_ = v___f_4206_;
v___y_4110_ = v_a_4167_;
v___y_4111_ = v___y_4156_;
v___y_4112_ = v___y_4149_;
v___y_4113_ = v_a_4176_;
v___y_4114_ = v___y_4157_;
v___y_4115_ = v___y_4159_;
v___y_4116_ = v___y_4155_;
v___y_4117_ = v___y_4154_;
v___y_4118_ = v_a_4186_;
v___y_4119_ = v___y_4158_;
v___y_4120_ = v_a_4203_;
v___y_4121_ = v_a_4169_;
v___y_4122_ = v___y_4152_;
v___y_4123_ = v___y_4150_;
v___y_4124_ = v_a_4198_;
v___y_4125_ = v___y_4160_;
v___y_4126_ = v_a_4194_;
v___y_4127_ = v___x_4173_;
v___y_4128_ = v_inv_x3f_4153_;
v___y_4129_ = v___x_4211_;
goto v___jp_4093_;
}
else
{
size_t v___x_4214_; size_t v___x_4215_; lean_object* v___x_4216_; 
v___x_4214_ = ((size_t)0ULL);
v___x_4215_ = lean_usize_of_nat(v___x_4210_);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_4198_, v_mutVars_4205_, v___x_4214_, v___x_4215_, v___x_4211_);
lean_inc(v_a_4194_);
lean_inc(v_a_4169_);
lean_inc(v_a_4203_);
lean_inc(v_a_4186_);
lean_inc(v_a_4176_);
lean_inc(v_a_4167_);
v___y_4094_ = v_a_4167_;
v___y_4095_ = v___y_4146_;
v___y_4096_ = v_a_4176_;
v___y_4097_ = v_a_4186_;
v___y_4098_ = v___f_4207_;
v___y_4099_ = v_a_4203_;
v___y_4100_ = v_a_4200_;
v___y_4101_ = v_monadInfo_4204_;
v___y_4102_ = v___f_4209_;
v___y_4103_ = v_a_4169_;
v___y_4104_ = v___y_4147_;
v___y_4105_ = v_body_4196_;
v___y_4106_ = v___y_4148_;
v___y_4107_ = v_a_4194_;
v___y_4108_ = v_a_4162_;
v___y_4109_ = v___f_4206_;
v___y_4110_ = v_a_4167_;
v___y_4111_ = v___y_4156_;
v___y_4112_ = v___y_4149_;
v___y_4113_ = v_a_4176_;
v___y_4114_ = v___y_4157_;
v___y_4115_ = v___y_4159_;
v___y_4116_ = v___y_4155_;
v___y_4117_ = v___y_4154_;
v___y_4118_ = v_a_4186_;
v___y_4119_ = v___y_4158_;
v___y_4120_ = v_a_4203_;
v___y_4121_ = v_a_4169_;
v___y_4122_ = v___y_4152_;
v___y_4123_ = v___y_4150_;
v___y_4124_ = v_a_4198_;
v___y_4125_ = v___y_4160_;
v___y_4126_ = v_a_4194_;
v___y_4127_ = v___x_4173_;
v___y_4128_ = v_inv_x3f_4153_;
v___y_4129_ = v___x_4216_;
goto v___jp_4093_;
}
}
else
{
size_t v___x_4217_; size_t v___x_4218_; lean_object* v___x_4219_; 
v___x_4217_ = ((size_t)0ULL);
v___x_4218_ = lean_usize_of_nat(v___x_4210_);
v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_4198_, v_mutVars_4205_, v___x_4217_, v___x_4218_, v___x_4211_);
lean_inc(v_a_4194_);
lean_inc(v_a_4169_);
lean_inc(v_a_4203_);
lean_inc(v_a_4186_);
lean_inc(v_a_4176_);
lean_inc(v_a_4167_);
v___y_4094_ = v_a_4167_;
v___y_4095_ = v___y_4146_;
v___y_4096_ = v_a_4176_;
v___y_4097_ = v_a_4186_;
v___y_4098_ = v___f_4207_;
v___y_4099_ = v_a_4203_;
v___y_4100_ = v_a_4200_;
v___y_4101_ = v_monadInfo_4204_;
v___y_4102_ = v___f_4209_;
v___y_4103_ = v_a_4169_;
v___y_4104_ = v___y_4147_;
v___y_4105_ = v_body_4196_;
v___y_4106_ = v___y_4148_;
v___y_4107_ = v_a_4194_;
v___y_4108_ = v_a_4162_;
v___y_4109_ = v___f_4206_;
v___y_4110_ = v_a_4167_;
v___y_4111_ = v___y_4156_;
v___y_4112_ = v___y_4149_;
v___y_4113_ = v_a_4176_;
v___y_4114_ = v___y_4157_;
v___y_4115_ = v___y_4159_;
v___y_4116_ = v___y_4155_;
v___y_4117_ = v___y_4154_;
v___y_4118_ = v_a_4186_;
v___y_4119_ = v___y_4158_;
v___y_4120_ = v_a_4203_;
v___y_4121_ = v_a_4169_;
v___y_4122_ = v___y_4152_;
v___y_4123_ = v___y_4150_;
v___y_4124_ = v_a_4198_;
v___y_4125_ = v___y_4160_;
v___y_4126_ = v_a_4194_;
v___y_4127_ = v___x_4173_;
v___y_4128_ = v_inv_x3f_4153_;
v___y_4129_ = v___x_4219_;
goto v___jp_4093_;
}
}
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
lean_dec(v_a_4200_);
lean_dec(v_a_4198_);
lean_dec(v_body_4196_);
lean_dec(v_a_4194_);
lean_dec(v_a_4186_);
lean_dec(v_a_4176_);
lean_dec(v_a_4169_);
lean_dec(v_a_4167_);
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
v_a_4220_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4202_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4202_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec(v_a_4198_);
lean_dec(v_body_4196_);
lean_dec(v_a_4194_);
lean_dec(v_a_4186_);
lean_dec(v_a_4176_);
lean_dec(v_a_4169_);
lean_dec(v_a_4167_);
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
v_a_4228_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4199_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4199_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec(v_body_4196_);
lean_dec(v_a_4194_);
lean_dec(v_a_4186_);
lean_dec(v_a_4176_);
lean_dec(v_a_4169_);
lean_dec(v_a_4167_);
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
v_a_4236_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4197_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4197_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
else
{
lean_dec(v_a_4186_);
lean_dec(v_a_4176_);
lean_dec(v_a_4169_);
lean_dec(v_a_4167_);
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
lean_dec(v_stx_3775_);
return v___x_4193_;
}
}
}
}
else
{
lean_dec(v_a_4176_);
lean_dec(v_a_4169_);
lean_dec(v_a_4167_);
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
lean_dec(v_stx_3775_);
return v___x_4185_;
}
}
}
}
else
{
lean_dec(v_a_4169_);
lean_dec(v_a_4167_);
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
lean_dec(v_stx_3775_);
return v___x_4175_;
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec(v_a_4167_);
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
lean_dec(v_stx_3775_);
v_a_4248_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4168_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4168_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
lean_dec(v_stx_3775_);
v_a_4256_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4166_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4166_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec(v_a_4162_);
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
lean_dec(v_stx_3775_);
v_a_4264_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4165_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4165_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v_inv_x3f_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec(v___y_4146_);
lean_dec(v_stx_3775_);
v_a_4272_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4161_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4161_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
v___jp_4280_:
{
lean_object* v_x_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v_x_4289_ = l_Lean_Syntax_getArg(v___x_3793_, v___x_3788_);
v___x_4290_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_x_4289_);
v___x_4291_ = l_Lean_Syntax_isOfKind(v_x_4289_, v___x_4290_);
if (v___x_4291_ == 0)
{
lean_object* v___x_4292_; 
lean_dec(v_x_4289_);
lean_dec(v_h_x3f_4281_);
lean_dec(v_tk_4144_);
lean_dec(v___x_3793_);
lean_dec_ref(v_dec_3776_);
lean_dec(v_stx_3775_);
v___x_4292_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4292_;
}
else
{
lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4293_ = lean_unsigned_to_nat(2u);
v___x_4294_ = lean_unsigned_to_nat(3u);
v___x_4295_ = l_Lean_Syntax_getArg(v___x_3793_, v___x_4294_);
lean_dec(v___x_3793_);
v___x_4296_ = l_Lean_Syntax_getArg(v_stx_3775_, v___x_4293_);
v___x_4297_ = l_Lean_Syntax_isNone(v___x_4296_);
if (v___x_4297_ == 0)
{
uint8_t v___x_4298_; 
lean_inc(v___x_4296_);
v___x_4298_ = l_Lean_Syntax_matchesNull(v___x_4296_, v___x_3788_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; 
lean_dec(v___x_4296_);
lean_dec(v___x_4295_);
lean_dec(v_x_4289_);
lean_dec(v_h_x3f_4281_);
lean_dec(v_tk_4144_);
lean_dec_ref(v_dec_3776_);
lean_dec(v_stx_3775_);
v___x_4299_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4299_;
}
else
{
lean_object* v_inv_x3f_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; 
v_inv_x3f_4300_ = l_Lean_Syntax_getArg(v___x_4296_, v___x_3792_);
lean_dec(v___x_4296_);
v___x_4301_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_x3f_4300_);
v___x_4302_ = l_Lean_Syntax_isOfKind(v_inv_x3f_4300_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; 
lean_dec(v_inv_x3f_4300_);
lean_dec(v___x_4295_);
lean_dec(v_x_4289_);
lean_dec(v_h_x3f_4281_);
lean_dec(v_tk_4144_);
lean_dec_ref(v_dec_3776_);
lean_dec(v_stx_3775_);
v___x_4303_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4303_;
}
else
{
lean_object* v___x_4304_; 
v___x_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4304_, 0, v_inv_x3f_4300_);
lean_inc(v_x_4289_);
lean_inc(v_h_x3f_4281_);
v___y_4146_ = v_h_x3f_4281_;
v___y_4147_ = v___x_4291_;
v___y_4148_ = v_x_4289_;
v___y_4149_ = v_h_x3f_4281_;
v___y_4150_ = v___x_4293_;
v___y_4151_ = v___x_4295_;
v___y_4152_ = v_x_4289_;
v_inv_x3f_4153_ = v___x_4304_;
v___y_4154_ = v___y_4282_;
v___y_4155_ = v___y_4283_;
v___y_4156_ = v___y_4284_;
v___y_4157_ = v___y_4285_;
v___y_4158_ = v___y_4286_;
v___y_4159_ = v___y_4287_;
v___y_4160_ = v___y_4288_;
goto v___jp_4145_;
}
}
}
else
{
lean_object* v___x_4305_; 
lean_dec(v___x_4296_);
v___x_4305_ = lean_box(0);
lean_inc(v_x_4289_);
lean_inc(v_h_x3f_4281_);
v___y_4146_ = v_h_x3f_4281_;
v___y_4147_ = v___x_4291_;
v___y_4148_ = v_x_4289_;
v___y_4149_ = v_h_x3f_4281_;
v___y_4150_ = v___x_4293_;
v___y_4151_ = v___x_4295_;
v___y_4152_ = v_x_4289_;
v_inv_x3f_4153_ = v___x_4305_;
v___y_4154_ = v___y_4282_;
v___y_4155_ = v___y_4283_;
v___y_4156_ = v___y_4284_;
v___y_4157_ = v___y_4285_;
v___y_4158_ = v___y_4286_;
v___y_4159_ = v___y_4287_;
v___y_4160_ = v___y_4288_;
goto v___jp_4145_;
}
}
}
}
v___jp_3796_:
{
lean_object* v_doBlockResultType_3816_; lean_object* v___x_3817_; lean_object* v___y_3818_; lean_object* v___x_3819_; lean_object* v___f_3820_; lean_object* v___x_3821_; 
v_doBlockResultType_3816_ = lean_ctor_get(v___y_3809_, 3);
v___x_3817_ = lean_box(v___y_3804_);
lean_inc(v___y_3802_);
lean_inc_ref(v_doBlockResultType_3816_);
v___y_3818_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 19, 11);
lean_closure_set(v___y_3818_, 0, v___x_3817_);
lean_closure_set(v___y_3818_, 1, v___y_3803_);
lean_closure_set(v___y_3818_, 2, v___y_3797_);
lean_closure_set(v___y_3818_, 3, v_doBlockResultType_3816_);
lean_closure_set(v___y_3818_, 4, v___y_3799_);
lean_closure_set(v___y_3818_, 5, v___y_3802_);
lean_closure_set(v___y_3818_, 6, v___y_3798_);
lean_closure_set(v___y_3818_, 7, v___y_3801_);
lean_closure_set(v___y_3818_, 8, v___y_3805_);
lean_closure_set(v___y_3818_, 9, v___x_3792_);
lean_closure_set(v___y_3818_, 10, v___x_3788_);
v___x_3819_ = lean_box(v___x_3795_);
v___f_3820_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 13, 4);
lean_closure_set(v___f_3820_, 0, v___y_3800_);
lean_closure_set(v___f_3820_, 1, v___y_3818_);
lean_closure_set(v___f_3820_, 2, v___x_3788_);
lean_closure_set(v___f_3820_, 3, v___x_3819_);
lean_inc_ref(v___y_3807_);
v___x_3821_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___y_3806_, v___y_3807_, v___f_3820_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
lean_inc_ref(v_doBlockResultType_3816_);
v___x_3823_ = l_Lean_Elab_Do_mkBindApp(v___y_3807_, v_doBlockResultType_3816_, v_forIn_3808_, v_a_3822_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
return v___x_3823_;
}
else
{
lean_dec_ref(v_forIn_3808_);
lean_dec_ref(v___y_3807_);
return v___x_3821_;
}
}
v___jp_3824_:
{
lean_object* v___x_3851_; 
lean_inc_ref(v___y_3842_);
lean_inc_ref(v___y_3841_);
v___x_3851_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(v___y_3837_, v___y_3850_, v___y_3844_, v___y_3840_, v___y_3836_, v___y_3841_, v___y_3839_, v___y_3845_, v___y_3842_, v___y_3847_, v___y_3843_, v___y_3838_, v___y_3848_, v___y_3846_, v___y_3835_, v___y_3849_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3850_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3851_, 1);
v___y_3797_ = v___y_3825_;
v___y_3798_ = v___y_3826_;
v___y_3799_ = v___y_3827_;
v___y_3800_ = v___y_3828_;
v___y_3801_ = v___y_3830_;
v___y_3802_ = v___y_3829_;
v___y_3803_ = v___y_3832_;
v___y_3804_ = v___y_3831_;
v___y_3805_ = v___y_3833_;
v___y_3806_ = v___y_3834_;
v___y_3807_ = v___y_3841_;
v_forIn_3808_ = v_a_3852_;
v___y_3809_ = v___y_3847_;
v___y_3810_ = v___y_3843_;
v___y_3811_ = v___y_3838_;
v___y_3812_ = v___y_3848_;
v___y_3813_ = v___y_3846_;
v___y_3814_ = v___y_3835_;
v___y_3815_ = v___y_3849_;
goto v___jp_3796_;
}
else
{
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec(v___y_3825_);
return v___x_3851_;
}
}
v___jp_3853_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___f_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; 
v___x_3887_ = l_Lean_instInhabitedExpr;
v___x_3888_ = lean_box(v___x_3795_);
lean_inc(v___y_3856_);
lean_inc(v___y_3863_);
lean_inc(v___y_3855_);
lean_inc_ref(v___y_3869_);
lean_inc_ref(v___y_3861_);
v___f_3889_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 24, 15);
lean_closure_set(v___f_3889_, 0, v___x_3887_);
lean_closure_set(v___f_3889_, 1, v___x_3792_);
lean_closure_set(v___f_3889_, 2, v___y_3865_);
lean_closure_set(v___f_3889_, 3, v___y_3861_);
lean_closure_set(v___f_3889_, 4, v___y_3869_);
lean_closure_set(v___f_3889_, 5, v___y_3855_);
lean_closure_set(v___f_3889_, 6, v___y_3862_);
lean_closure_set(v___f_3889_, 7, v___y_3858_);
lean_closure_set(v___f_3889_, 8, v___y_3866_);
lean_closure_set(v___f_3889_, 9, v___y_3867_);
lean_closure_set(v___f_3889_, 10, v___x_3888_);
lean_closure_set(v___f_3889_, 11, v___y_3863_);
lean_closure_set(v___f_3889_, 12, v___y_3856_);
lean_closure_set(v___f_3889_, 13, v___y_3854_);
lean_closure_set(v___f_3889_, 14, v___x_3788_);
v___x_3890_ = 0;
v___x_3891_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_3886_, v___f_3889_, v___x_3890_, v___y_3883_, v___y_3878_, v___y_3872_, v___y_3884_, v___y_3881_, v___y_3871_, v___y_3885_);
if (lean_obj_tag(v___x_3891_) == 0)
{
if (lean_obj_tag(v___y_3882_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3893_; 
lean_dec_ref(v___y_3879_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3870_);
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v___x_3893_ = l_Lean_Expr_app___override(v___y_3877_, v_a_3892_);
v___y_3797_ = v___y_3860_;
v___y_3798_ = v___y_3855_;
v___y_3799_ = v___y_3861_;
v___y_3800_ = v___y_3863_;
v___y_3801_ = v___y_3864_;
v___y_3802_ = v___y_3857_;
v___y_3803_ = v___y_3869_;
v___y_3804_ = v___y_3868_;
v___y_3805_ = v___y_3859_;
v___y_3806_ = v___y_3856_;
v___y_3807_ = v___y_3875_;
v_forIn_3808_ = v___x_3893_;
v___y_3809_ = v___y_3883_;
v___y_3810_ = v___y_3878_;
v___y_3811_ = v___y_3872_;
v___y_3812_ = v___y_3884_;
v___y_3813_ = v___y_3881_;
v___y_3814_ = v___y_3871_;
v___y_3815_ = v___y_3885_;
goto v___jp_3796_;
}
else
{
lean_dec_ref(v___y_3877_);
if (lean_obj_tag(v___y_3870_) == 0)
{
lean_object* v_a_3894_; lean_object* v_val_3895_; lean_object* v___x_3896_; 
v_a_3894_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3891_, 1);
v_val_3895_ = lean_ctor_get(v___y_3882_, 0);
lean_inc(v_val_3895_);
lean_dec_ref_known(v___y_3882_, 1);
v___x_3896_ = lean_box(0);
v___y_3825_ = v___y_3860_;
v___y_3826_ = v___y_3855_;
v___y_3827_ = v___y_3861_;
v___y_3828_ = v___y_3863_;
v___y_3829_ = v___y_3857_;
v___y_3830_ = v___y_3864_;
v___y_3831_ = v___y_3868_;
v___y_3832_ = v___y_3869_;
v___y_3833_ = v___y_3859_;
v___y_3834_ = v___y_3856_;
v___y_3835_ = v___y_3871_;
v___y_3836_ = v_a_3894_;
v___y_3837_ = v_val_3895_;
v___y_3838_ = v___y_3872_;
v___y_3839_ = v___y_3873_;
v___y_3840_ = v___y_3874_;
v___y_3841_ = v___y_3875_;
v___y_3842_ = v___y_3876_;
v___y_3843_ = v___y_3878_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___y_3880_;
v___y_3846_ = v___y_3881_;
v___y_3847_ = v___y_3883_;
v___y_3848_ = v___y_3884_;
v___y_3849_ = v___y_3885_;
v___y_3850_ = v___x_3896_;
goto v___jp_3824_;
}
else
{
lean_object* v_a_3897_; lean_object* v_val_3898_; lean_object* v_val_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
v_a_3897_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3891_, 1);
v_val_3898_ = lean_ctor_get(v___y_3882_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v___y_3882_, 1);
v_val_3899_ = lean_ctor_get(v___y_3870_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___y_3870_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___y_3870_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_val_3899_);
lean_dec(v___y_3870_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_val_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
v___y_3825_ = v___y_3860_;
v___y_3826_ = v___y_3855_;
v___y_3827_ = v___y_3861_;
v___y_3828_ = v___y_3863_;
v___y_3829_ = v___y_3857_;
v___y_3830_ = v___y_3864_;
v___y_3831_ = v___y_3868_;
v___y_3832_ = v___y_3869_;
v___y_3833_ = v___y_3859_;
v___y_3834_ = v___y_3856_;
v___y_3835_ = v___y_3871_;
v___y_3836_ = v_a_3897_;
v___y_3837_ = v_val_3898_;
v___y_3838_ = v___y_3872_;
v___y_3839_ = v___y_3873_;
v___y_3840_ = v___y_3874_;
v___y_3841_ = v___y_3875_;
v___y_3842_ = v___y_3876_;
v___y_3843_ = v___y_3878_;
v___y_3844_ = v___y_3879_;
v___y_3845_ = v___y_3880_;
v___y_3846_ = v___y_3881_;
v___y_3847_ = v___y_3883_;
v___y_3848_ = v___y_3884_;
v___y_3849_ = v___y_3885_;
v___y_3850_ = v___x_3904_;
goto v___jp_3824_;
}
}
}
}
}
else
{
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v___y_3877_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
return v___x_3891_;
}
}
v___jp_3907_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_3949_ = l_Lean_Core_mkFreshUserName(v___x_3948_, v___y_3946_, v___y_3947_);
if (lean_obj_tag(v___x_3949_) == 0)
{
if (lean_obj_tag(v___y_3930_) == 1)
{
if (lean_obj_tag(v_snd_3940_) == 1)
{
lean_object* v_a_3950_; lean_object* v_val_3951_; lean_object* v_val_3952_; lean_object* v___f_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec_ref(v___y_3929_);
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3949_, 1);
v_val_3951_ = lean_ctor_get(v___y_3930_, 0);
v_val_3952_ = lean_ctor_get(v_snd_3940_, 0);
lean_inc(v_val_3952_);
lean_dec_ref_known(v_snd_3940_, 1);
v___f_3953_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_3953_, 0, v___y_3921_);
lean_closure_set(v___f_3953_, 1, v___y_3908_);
lean_closure_set(v___f_3953_, 2, v___x_3792_);
lean_closure_set(v___f_3953_, 3, v___y_3911_);
lean_closure_set(v___f_3953_, 4, v___y_3916_);
lean_closure_set(v___f_3953_, 5, v_val_3952_);
lean_closure_set(v___f_3953_, 6, v___y_3926_);
v___x_3954_ = l_Lean_TSyntax_getId(v___y_3933_);
lean_dec(v___y_3933_);
v___x_3955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
lean_ctor_set(v___x_3955_, 1, v___y_3937_);
v___x_3956_ = l_Lean_TSyntax_getId(v_val_3951_);
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
lean_ctor_set(v___x_3957_, 1, v___f_3953_);
v___x_3958_ = lean_mk_empty_array_with_capacity(v___y_3932_);
v___x_3959_ = lean_array_push(v___x_3958_, v___x_3955_);
v___x_3960_ = lean_array_push(v___x_3959_, v___x_3957_);
lean_inc_ref(v___y_3919_);
v___y_3854_ = v___y_3909_;
v___y_3855_ = v___y_3910_;
v___y_3856_ = v_a_3950_;
v___y_3857_ = v___y_3912_;
v___y_3858_ = v___y_3913_;
v___y_3859_ = v___y_3914_;
v___y_3860_ = v___y_3917_;
v___y_3861_ = v___y_3918_;
v___y_3862_ = v___y_3919_;
v___y_3863_ = v___y_3920_;
v___y_3864_ = v___y_3922_;
v___y_3865_ = v___y_3923_;
v___y_3866_ = v___y_3924_;
v___y_3867_ = v___y_3925_;
v___y_3868_ = v___y_3928_;
v___y_3869_ = v___y_3927_;
v___y_3870_ = v___y_3930_;
v___y_3871_ = v___y_3946_;
v___y_3872_ = v___y_3943_;
v___y_3873_ = v___y_3938_;
v___y_3874_ = v___y_3915_;
v___y_3875_ = v___y_3919_;
v___y_3876_ = v___y_3931_;
v___y_3877_ = v_fst_3939_;
v___y_3878_ = v___y_3942_;
v___y_3879_ = v___y_3934_;
v___y_3880_ = v___y_3935_;
v___y_3881_ = v___y_3945_;
v___y_3882_ = v___y_3936_;
v___y_3883_ = v___y_3941_;
v___y_3884_ = v___y_3944_;
v___y_3885_ = v___y_3947_;
v___y_3886_ = v___x_3960_;
goto v___jp_3853_;
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3962_; 
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3916_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3908_);
v_a_3961_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3949_, 1);
lean_inc_ref(v___y_3930_);
v___x_3962_ = lean_apply_2(v___y_3929_, v___y_3930_, v_snd_3940_);
lean_inc_ref(v___y_3919_);
v___y_3854_ = v___y_3909_;
v___y_3855_ = v___y_3910_;
v___y_3856_ = v_a_3961_;
v___y_3857_ = v___y_3912_;
v___y_3858_ = v___y_3913_;
v___y_3859_ = v___y_3914_;
v___y_3860_ = v___y_3917_;
v___y_3861_ = v___y_3918_;
v___y_3862_ = v___y_3919_;
v___y_3863_ = v___y_3920_;
v___y_3864_ = v___y_3922_;
v___y_3865_ = v___y_3923_;
v___y_3866_ = v___y_3924_;
v___y_3867_ = v___y_3925_;
v___y_3868_ = v___y_3928_;
v___y_3869_ = v___y_3927_;
v___y_3870_ = v___y_3930_;
v___y_3871_ = v___y_3946_;
v___y_3872_ = v___y_3943_;
v___y_3873_ = v___y_3938_;
v___y_3874_ = v___y_3915_;
v___y_3875_ = v___y_3919_;
v___y_3876_ = v___y_3931_;
v___y_3877_ = v_fst_3939_;
v___y_3878_ = v___y_3942_;
v___y_3879_ = v___y_3934_;
v___y_3880_ = v___y_3935_;
v___y_3881_ = v___y_3945_;
v___y_3882_ = v___y_3936_;
v___y_3883_ = v___y_3941_;
v___y_3884_ = v___y_3944_;
v___y_3885_ = v___y_3947_;
v___y_3886_ = v___x_3962_;
goto v___jp_3853_;
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3964_; 
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3916_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3908_);
v_a_3963_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3949_, 1);
lean_inc(v___y_3930_);
v___x_3964_ = lean_apply_2(v___y_3929_, v___y_3930_, v_snd_3940_);
lean_inc_ref(v___y_3919_);
v___y_3854_ = v___y_3909_;
v___y_3855_ = v___y_3910_;
v___y_3856_ = v_a_3963_;
v___y_3857_ = v___y_3912_;
v___y_3858_ = v___y_3913_;
v___y_3859_ = v___y_3914_;
v___y_3860_ = v___y_3917_;
v___y_3861_ = v___y_3918_;
v___y_3862_ = v___y_3919_;
v___y_3863_ = v___y_3920_;
v___y_3864_ = v___y_3922_;
v___y_3865_ = v___y_3923_;
v___y_3866_ = v___y_3924_;
v___y_3867_ = v___y_3925_;
v___y_3868_ = v___y_3928_;
v___y_3869_ = v___y_3927_;
v___y_3870_ = v___y_3930_;
v___y_3871_ = v___y_3946_;
v___y_3872_ = v___y_3943_;
v___y_3873_ = v___y_3938_;
v___y_3874_ = v___y_3915_;
v___y_3875_ = v___y_3919_;
v___y_3876_ = v___y_3931_;
v___y_3877_ = v_fst_3939_;
v___y_3878_ = v___y_3942_;
v___y_3879_ = v___y_3934_;
v___y_3880_ = v___y_3935_;
v___y_3881_ = v___y_3945_;
v___y_3882_ = v___y_3936_;
v___y_3883_ = v___y_3941_;
v___y_3884_ = v___y_3944_;
v___y_3885_ = v___y_3947_;
v___y_3886_ = v___x_3964_;
goto v___jp_3853_;
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec(v_snd_3940_);
lean_dec_ref(v_fst_3939_);
lean_dec_ref(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec_ref(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec(v___y_3908_);
v_a_3965_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3949_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3949_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
v___jp_3973_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = lean_box(0);
lean_inc_ref(v___y_3977_);
lean_inc(v___y_4007_);
lean_inc_ref(v___y_3994_);
lean_inc(v___y_3999_);
lean_inc_ref(v___y_3993_);
lean_inc(v___y_3990_);
lean_inc_ref(v___y_3995_);
v___x_4012_ = lean_apply_8(v___y_3977_, v___x_4011_, v___y_3995_, v___y_3990_, v___y_3993_, v___y_3999_, v___y_3994_, v___y_4007_, lean_box(0));
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v_m_4014_; lean_object* v_u_4015_; lean_object* v_v_4016_; lean_object* v___x_4017_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4012_, 1);
v_m_4014_ = lean_ctor_get(v___y_4001_, 0);
v_u_4015_ = lean_ctor_get(v___y_4001_, 1);
v_v_4016_ = lean_ctor_get(v___y_4001_, 2);
lean_inc(v_u_4015_);
v___x_4017_ = l_Lean_Meta_mkProdMkN(v_a_4013_, v_u_4015_, v___y_3993_, v___y_3999_, v___y_3994_, v___y_4007_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; 
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___x_4017_, 1);
if (lean_obj_tag(v___y_3991_) == 0)
{
lean_object* v_fst_4019_; lean_object* v_snd_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4039_; 
v_fst_4019_ = lean_ctor_get(v_a_4018_, 0);
v_snd_4020_ = lean_ctor_get(v_a_4018_, 1);
v_isSharedCheck_4039_ = !lean_is_exclusive(v_a_4018_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4022_ = v_a_4018_;
v_isShared_4023_ = v_isSharedCheck_4039_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_snd_4020_);
lean_inc(v_fst_4019_);
lean_dec(v_a_4018_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4039_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4024_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__0));
v___x_4025_ = lean_box(0);
lean_inc(v_v_4016_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set_tag(v___x_4022_, 1);
lean_ctor_set(v___x_4022_, 1, v___x_4025_);
lean_ctor_set(v___x_4022_, 0, v_v_4016_);
v___x_4027_ = v___x_4022_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_v_4016_);
lean_ctor_set(v_reuseFailAlloc_4038_, 1, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_inc(v_u_4015_);
v___x_4028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4028_, 0, v_u_4015_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___y_3989_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4030_, 0, v___y_4002_);
lean_ctor_set(v___x_4030_, 1, v___x_4029_);
lean_inc_ref(v___x_4030_);
v___x_4031_ = l_Lean_mkConst(v___x_4024_, v___x_4030_);
lean_inc_ref(v___y_3992_);
lean_inc_ref(v___y_3998_);
lean_inc_ref(v_m_4014_);
v___x_4032_ = l_Lean_mkApp3(v___x_4031_, v_m_4014_, v___y_3998_, v___y_3992_);
v___x_4033_ = l_Lean_Elab_Term_mkInstMVar(v___x_4032_, v___x_4011_, v___y_3995_, v___y_3990_, v___y_3993_, v___y_3999_, v___y_3994_, v___y_4007_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v___x_4035_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__2));
v___x_4036_ = l_Lean_mkConst(v___x_4035_, v___x_4030_);
lean_inc(v_fst_4019_);
lean_inc_ref(v___y_4006_);
lean_inc(v_snd_4020_);
lean_inc_ref(v_m_4014_);
v___x_4037_ = l_Lean_mkApp7(v___x_4036_, v_m_4014_, v___y_3998_, v___y_3992_, v_a_4034_, v_snd_4020_, v___y_4006_, v_fst_4019_);
lean_inc(v_u_4015_);
v___y_3908_ = v___y_3974_;
v___y_3909_ = v___y_3975_;
v___y_3910_ = v_u_4015_;
v___y_3911_ = v___y_3976_;
v___y_3912_ = v_v_4016_;
v___y_3913_ = v___y_3977_;
v___y_3914_ = v___y_3978_;
v___y_3915_ = v_fst_4019_;
v___y_3916_ = v___y_3979_;
v___y_3917_ = v___y_3980_;
v___y_3918_ = v___y_3981_;
v___y_3919_ = v_snd_4020_;
v___y_3920_ = v___y_4010_;
v___y_3921_ = v___y_3983_;
v___y_3922_ = v___y_3982_;
v___y_3923_ = v___y_3985_;
v___y_3924_ = v___x_4011_;
v___y_3925_ = v___y_3984_;
v___y_3926_ = v___y_3986_;
v___y_3927_ = v___y_3987_;
v___y_3928_ = v___y_3988_;
v___y_3929_ = v___y_4000_;
v___y_3930_ = v___y_3991_;
v___y_3931_ = v___y_4001_;
v___y_3932_ = v___y_4003_;
v___y_3933_ = v___y_4004_;
v___y_3934_ = v___y_4006_;
v___y_3935_ = v___y_3988_;
v___y_3936_ = v___y_4008_;
v___y_3937_ = v___y_4009_;
v___y_3938_ = v___y_3996_;
v_fst_3939_ = v___x_4037_;
v_snd_3940_ = v___x_4011_;
v___y_3941_ = v___y_3997_;
v___y_3942_ = v___y_3995_;
v___y_3943_ = v___y_3990_;
v___y_3944_ = v___y_3993_;
v___y_3945_ = v___y_3999_;
v___y_3946_ = v___y_3994_;
v___y_3947_ = v___y_4007_;
goto v___jp_3907_;
}
else
{
lean_dec_ref_known(v___x_4030_, 2);
lean_dec(v_snd_4020_);
lean_dec(v_fst_4019_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4000_);
lean_dec_ref(v___y_3998_);
lean_dec_ref(v___y_3996_);
lean_dec_ref(v___y_3992_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec(v___y_3974_);
return v___x_4033_;
}
}
}
}
else
{
lean_object* v_fst_4040_; lean_object* v_snd_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4076_; 
v_fst_4040_ = lean_ctor_get(v_a_4018_, 0);
v_snd_4041_ = lean_ctor_get(v_a_4018_, 1);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_a_4018_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4043_ = v_a_4018_;
v_isShared_4044_ = v_isSharedCheck_4076_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_snd_4041_);
lean_inc(v_fst_4040_);
lean_dec(v_a_4018_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4076_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4045_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_4046_ = lean_box(0);
lean_inc(v___y_4002_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set_tag(v___x_4043_, 1);
lean_ctor_set(v___x_4043_, 1, v___x_4046_);
lean_ctor_set(v___x_4043_, 0, v___y_4002_);
v___x_4048_ = v___x_4043_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___y_4002_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v___x_4046_);
v___x_4048_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_inc(v___y_3989_);
v___x_4049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___y_3989_);
lean_ctor_set(v___x_4049_, 1, v___x_4048_);
v___x_4050_ = l_Lean_mkConst(v___x_4045_, v___x_4049_);
lean_inc_ref(v___y_3998_);
lean_inc_ref(v___y_3992_);
v___x_4051_ = l_Lean_mkAppB(v___x_4050_, v___y_3992_, v___y_3998_);
v___x_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
v___x_4053_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__5));
v___x_4054_ = l_Lean_Meta_mkFreshExprMVar(v___x_4052_, v___y_4005_, v___x_4053_, v___y_3993_, v___y_3999_, v___y_3994_, v___y_4007_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc_n(v_a_4055_, 2);
lean_dec_ref_known(v___x_4054_, 1);
v___x_4056_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
lean_inc(v_v_4016_);
v___x_4057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4057_, 0, v_v_4016_);
lean_ctor_set(v___x_4057_, 1, v___x_4046_);
lean_inc(v_u_4015_);
v___x_4058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4058_, 0, v_u_4015_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
v___x_4059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___y_3989_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___y_4002_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
lean_inc_ref(v___x_4060_);
v___x_4061_ = l_Lean_mkConst(v___x_4056_, v___x_4060_);
lean_inc_ref(v___y_3992_);
lean_inc_ref(v___y_3998_);
lean_inc_ref(v_m_4014_);
v___x_4062_ = l_Lean_mkApp4(v___x_4061_, v_m_4014_, v___y_3998_, v___y_3992_, v_a_4055_);
v___x_4063_ = l_Lean_Elab_Term_mkInstMVar(v___x_4062_, v___x_4011_, v___y_3995_, v___y_3990_, v___y_3993_, v___y_3999_, v___y_3994_, v___y_4007_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4074_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4074_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4074_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
v___x_4068_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
v___x_4069_ = l_Lean_mkConst(v___x_4068_, v___x_4060_);
lean_inc(v_fst_4040_);
lean_inc_ref(v___y_4006_);
lean_inc(v_snd_4041_);
lean_inc(v_a_4055_);
lean_inc_ref(v_m_4014_);
v___x_4070_ = l_Lean_mkApp8(v___x_4069_, v_m_4014_, v___y_3998_, v___y_3992_, v_a_4055_, v_a_4064_, v_snd_4041_, v___y_4006_, v_fst_4040_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set_tag(v___x_4066_, 1);
lean_ctor_set(v___x_4066_, 0, v_a_4055_);
v___x_4072_ = v___x_4066_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4055_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_inc(v_u_4015_);
v___y_3908_ = v___y_3974_;
v___y_3909_ = v___y_3975_;
v___y_3910_ = v_u_4015_;
v___y_3911_ = v___y_3976_;
v___y_3912_ = v_v_4016_;
v___y_3913_ = v___y_3977_;
v___y_3914_ = v___y_3978_;
v___y_3915_ = v_fst_4040_;
v___y_3916_ = v___y_3979_;
v___y_3917_ = v___y_3980_;
v___y_3918_ = v___y_3981_;
v___y_3919_ = v_snd_4041_;
v___y_3920_ = v___y_4010_;
v___y_3921_ = v___y_3983_;
v___y_3922_ = v___y_3982_;
v___y_3923_ = v___y_3985_;
v___y_3924_ = v___x_4011_;
v___y_3925_ = v___y_3984_;
v___y_3926_ = v___y_3986_;
v___y_3927_ = v___y_3987_;
v___y_3928_ = v___y_3988_;
v___y_3929_ = v___y_4000_;
v___y_3930_ = v___y_3991_;
v___y_3931_ = v___y_4001_;
v___y_3932_ = v___y_4003_;
v___y_3933_ = v___y_4004_;
v___y_3934_ = v___y_4006_;
v___y_3935_ = v___y_3988_;
v___y_3936_ = v___y_4008_;
v___y_3937_ = v___y_4009_;
v___y_3938_ = v___y_3996_;
v_fst_3939_ = v___x_4070_;
v_snd_3940_ = v___x_4072_;
v___y_3941_ = v___y_3997_;
v___y_3942_ = v___y_3995_;
v___y_3943_ = v___y_3990_;
v___y_3944_ = v___y_3993_;
v___y_3945_ = v___y_3999_;
v___y_3946_ = v___y_3994_;
v___y_3947_ = v___y_4007_;
goto v___jp_3907_;
}
}
}
else
{
lean_dec_ref_known(v___x_4060_, 2);
lean_dec(v_a_4055_);
lean_dec(v_snd_4041_);
lean_dec(v_fst_4040_);
lean_dec_ref_known(v___y_3991_, 1);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4000_);
lean_dec_ref(v___y_3998_);
lean_dec_ref(v___y_3996_);
lean_dec_ref(v___y_3992_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec(v___y_3974_);
return v___x_4063_;
}
}
else
{
lean_dec(v_snd_4041_);
lean_dec_ref_known(v___y_3991_, 1);
lean_dec(v_fst_4040_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4004_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4000_);
lean_dec_ref(v___y_3998_);
lean_dec_ref(v___y_3996_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec(v___y_3974_);
return v___x_4054_;
}
}
}
}
}
else
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4084_; 
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4004_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4000_);
lean_dec_ref(v___y_3998_);
lean_dec_ref(v___y_3996_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec(v___y_3974_);
v_a_4077_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4079_ = v___x_4017_;
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4017_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4004_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4000_);
lean_dec_ref(v___y_3998_);
lean_dec_ref(v___y_3996_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec(v___y_3974_);
v_a_4085_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4012_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4012_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
v___jp_4093_:
{
uint8_t v_returnsEarly_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___f_4133_; 
v_returnsEarly_4130_ = lean_ctor_get_uint8(v___y_4124_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_4124_);
v___x_4131_ = lean_box(v_returnsEarly_4130_);
v___x_4132_ = lean_box(v___y_4104_);
lean_inc_ref(v___y_4100_);
lean_inc_ref(v___y_4101_);
lean_inc_ref(v___y_4129_);
v___f_4133_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 14, 6);
lean_closure_set(v___f_4133_, 0, v___y_4129_);
lean_closure_set(v___f_4133_, 1, v___y_4101_);
lean_closure_set(v___f_4133_, 2, v___x_4131_);
lean_closure_set(v___f_4133_, 3, v___x_3792_);
lean_closure_set(v___f_4133_, 4, v___y_4100_);
lean_closure_set(v___f_4133_, 5, v___x_4132_);
if (v_returnsEarly_4130_ == 0)
{
size_t v_sz_4134_; size_t v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
lean_dec(v___y_4120_);
v_sz_4134_ = lean_array_size(v___y_4129_);
v___x_4135_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_4129_, 2);
v___x_4136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_4134_, v___x_4135_, v___y_4129_);
v___x_4137_ = lean_array_to_list(v___x_4136_);
v___y_3974_ = v___y_4094_;
v___y_3975_ = v___y_4095_;
v___y_3976_ = v___y_4096_;
v___y_3977_ = v___f_4133_;
v___y_3978_ = v___y_4129_;
v___y_3979_ = v___y_4097_;
v___y_3980_ = v___y_4099_;
v___y_3981_ = v___y_4100_;
v___y_3982_ = v___y_4102_;
v___y_3983_ = v___y_4103_;
v___y_3984_ = v___y_4105_;
v___y_3985_ = v___y_4106_;
v___y_3986_ = v___y_4107_;
v___y_3987_ = v___y_4108_;
v___y_3988_ = v_returnsEarly_4130_;
v___y_3989_ = v___y_4110_;
v___y_3990_ = v___y_4111_;
v___y_3991_ = v___y_4112_;
v___y_3992_ = v___y_4113_;
v___y_3993_ = v___y_4114_;
v___y_3994_ = v___y_4115_;
v___y_3995_ = v___y_4116_;
v___y_3996_ = v___y_4129_;
v___y_3997_ = v___y_4117_;
v___y_3998_ = v___y_4118_;
v___y_3999_ = v___y_4119_;
v___y_4000_ = v___y_4098_;
v___y_4001_ = v___y_4101_;
v___y_4002_ = v___y_4121_;
v___y_4003_ = v___y_4123_;
v___y_4004_ = v___y_4122_;
v___y_4005_ = v___y_4127_;
v___y_4006_ = v___y_4126_;
v___y_4007_ = v___y_4125_;
v___y_4008_ = v___y_4128_;
v___y_4009_ = v___y_4109_;
v___y_4010_ = v___x_4137_;
goto v___jp_3973_;
}
else
{
size_t v_sz_4138_; size_t v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v_sz_4138_ = lean_array_size(v___y_4129_);
v___x_4139_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_4129_, 2);
v___x_4140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_4138_, v___x_4139_, v___y_4129_);
v___x_4141_ = lean_array_to_list(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___y_4120_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___y_3974_ = v___y_4094_;
v___y_3975_ = v___y_4095_;
v___y_3976_ = v___y_4096_;
v___y_3977_ = v___f_4133_;
v___y_3978_ = v___y_4129_;
v___y_3979_ = v___y_4097_;
v___y_3980_ = v___y_4099_;
v___y_3981_ = v___y_4100_;
v___y_3982_ = v___y_4102_;
v___y_3983_ = v___y_4103_;
v___y_3984_ = v___y_4105_;
v___y_3985_ = v___y_4106_;
v___y_3986_ = v___y_4107_;
v___y_3987_ = v___y_4108_;
v___y_3988_ = v_returnsEarly_4130_;
v___y_3989_ = v___y_4110_;
v___y_3990_ = v___y_4111_;
v___y_3991_ = v___y_4112_;
v___y_3992_ = v___y_4113_;
v___y_3993_ = v___y_4114_;
v___y_3994_ = v___y_4115_;
v___y_3995_ = v___y_4116_;
v___y_3996_ = v___y_4129_;
v___y_3997_ = v___y_4117_;
v___y_3998_ = v___y_4118_;
v___y_3999_ = v___y_4119_;
v___y_4000_ = v___y_4098_;
v___y_4001_ = v___y_4101_;
v___y_4002_ = v___y_4121_;
v___y_4003_ = v___y_4123_;
v___y_4004_ = v___y_4122_;
v___y_4005_ = v___y_4127_;
v___y_4006_ = v___y_4126_;
v___y_4007_ = v___y_4125_;
v___y_4008_ = v___y_4128_;
v___y_4009_ = v___y_4109_;
v___y_4010_ = v___x_4142_;
goto v___jp_3973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_4314_, lean_object* v_dec_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l_Lean_Elab_Do_elabDoFor(v_stx_4314_, v_dec_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec_ref(v_a_4316_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v_00_u03b1_4325_, lean_object* v_msg_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v_00_u03b1_4335_, lean_object* v_msg_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(v_00_u03b1_4335_, v_msg_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_4345_, lean_object* v_name_4346_, lean_object* v_type_4347_, lean_object* v_k_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_4346_, v_type_4347_, v_k_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_4358_, lean_object* v_name_4359_, lean_object* v_type_4360_, lean_object* v_k_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_4358_, v_name_4359_, v_type_4360_, v_k_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec_ref(v___y_4362_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(lean_object* v_msgData_4371_, lean_object* v_macroStack_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v___x_4380_; 
v___x_4380_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_4371_, v_macroStack_4372_, v___y_4377_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___boxed(lean_object* v_msgData_4381_, lean_object* v_macroStack_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(v_msgData_4381_, v_macroStack_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4398_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4399_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_4400_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_4401_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_4402_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4398_, v___x_4399_, v___x_4400_, v___x_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_4404_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ProdN(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
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
lean_object* initialize_Init_While(uint8_t builtin);
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
res = initialize_Init_While(builtin);
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
