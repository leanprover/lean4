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
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "The `invariant` clause takes at least two binders: the elements consumed so far and the elements remaining."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__20;
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
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__20(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(lean_object* v_invClause_1993_, lean_object* v_h_x3f_1994_, lean_object* v_xs_1995_, lean_object* v_preS_1996_, lean_object* v_body_1997_, lean_object* v_00_u03c3_1998_, lean_object* v_loopMutVars_1999_, uint8_t v_returnsEarly_2000_, lean_object* v_mi_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_invClause_1993_);
v___x_2011_ = l_Lean_Syntax_isOfKind(v_invClause_1993_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_preS_1996_);
lean_dec_ref(v_xs_1995_);
lean_dec(v_invClause_1993_);
v___x_2012_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2012_;
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2013_ = lean_unsigned_to_nat(1u);
v___x_2014_ = l_Lean_Syntax_getArg(v_invClause_1993_, v___x_2013_);
v___x_2015_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1));
lean_inc(v___x_2014_);
v___x_2016_ = l_Lean_Syntax_isOfKind(v___x_2014_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; 
lean_dec(v___x_2014_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_preS_1996_);
lean_dec_ref(v_xs_1995_);
lean_dec(v_invClause_1993_);
v___x_2017_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2017_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; uint8_t v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2099_; uint8_t v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; 
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = l_Lean_Syntax_getArg(v___x_2014_, v___x_2013_);
v___x_2020_ = l_Lean_Syntax_matchesNull(v___x_2019_, v___x_2018_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2110_; 
lean_dec(v___x_2014_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_preS_1996_);
lean_dec_ref(v_xs_1995_);
lean_dec(v_invClause_1993_);
v___x_2110_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2110_;
}
else
{
lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v_mutTuplePat_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v_mutBinders_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v_mutBinders_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2236_; lean_object* v_invBody_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v_ref_2244_; lean_object* v___y_2245_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v_invBody_2257_; lean_object* v_binders_2258_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2254_ = l_Lean_Syntax_getArg(v___x_2014_, v___x_2018_);
v___x_2255_ = lean_unsigned_to_nat(2u);
v___x_2256_ = lean_unsigned_to_nat(3u);
v_invBody_2257_ = l_Lean_Syntax_getArg(v___x_2014_, v___x_2256_);
lean_dec(v___x_2014_);
v_binders_2258_ = l_Lean_Syntax_getArgs(v___x_2254_);
lean_dec(v___x_2254_);
v___x_2287_ = lean_array_get_size(v_binders_2258_);
v___x_2288_ = lean_nat_dec_le(v___x_2255_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_binders_2258_);
lean_dec(v_invBody_2257_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_preS_1996_);
lean_dec_ref(v_xs_1995_);
v___x_2289_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__20, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__20_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__20);
v___x_2290_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_invClause_1993_, v___x_2289_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec(v_invClause_1993_);
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
v___y_2260_ = v_a_2002_;
v___y_2261_ = v_a_2003_;
v___y_2262_ = v_a_2004_;
v___y_2263_ = v_a_2005_;
v___y_2264_ = v_a_2006_;
v___y_2265_ = v_a_2007_;
v___y_2266_ = v_a_2008_;
goto v___jp_2259_;
}
v___jp_2111_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_2123_ = l_Lean_Core_mkFreshUserName(v___x_2122_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v_ref_2125_; lean_object* v___x_2126_; lean_object* v_a_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v_ref_2125_ = lean_ctor_get(v___y_2120_, 5);
v___x_2126_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2125_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc_n(v_a_2127_, 17);
lean_dec_ref(v___x_2126_);
v___x_2128_ = 0;
v___x_2129_ = l_Lean_mkIdentFrom(v_invClause_1993_, v_a_2124_, v___x_2128_);
v___x_2130_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9));
v___x_2131_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10));
v___x_2132_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2132_, 0, v_a_2127_);
lean_ctor_set(v___x_2132_, 1, v___x_2130_);
v___x_2133_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2134_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2135_ = l_Array_append___redArg(v___x_2134_, v___y_2112_);
lean_dec_ref(v___y_2112_);
lean_inc(v___x_2129_);
v___x_2136_ = lean_array_push(v___x_2135_, v___x_2129_);
v___x_2137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2137_, 0, v_a_2127_);
lean_ctor_set(v___x_2137_, 1, v___x_2133_);
lean_ctor_set(v___x_2137_, 2, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2138_, 0, v_a_2127_);
lean_ctor_set(v___x_2138_, 1, v___x_2133_);
lean_ctor_set(v___x_2138_, 2, v___x_2134_);
v___x_2139_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_a_2127_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
v___x_2142_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11));
v___x_2143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2143_, 0, v_a_2127_);
lean_ctor_set(v___x_2143_, 1, v___x_2141_);
v___x_2144_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_2138_, 3);
v___x_2145_ = l_Lean_Syntax_node2(v_a_2127_, v___x_2144_, v___x_2138_, v___x_2129_);
v___x_2146_ = l_Lean_Syntax_node1(v_a_2127_, v___x_2133_, v___x_2145_);
v___x_2147_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_2148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_a_2127_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_2150_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_2151_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_2152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_a_2127_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_Syntax_node1(v_a_2127_, v___x_2133_, v_mutTuplePat_2114_);
v___x_2154_ = l_Lean_Syntax_node1(v_a_2127_, v___x_2133_, v___x_2153_);
lean_inc_ref(v___x_2140_);
v___x_2155_ = l_Lean_Syntax_node4(v_a_2127_, v___x_2150_, v___x_2152_, v___x_2154_, v___x_2140_, v___y_2113_);
v___x_2156_ = l_Lean_Syntax_node1(v_a_2127_, v___x_2133_, v___x_2155_);
v___x_2157_ = l_Lean_Syntax_node1(v_a_2127_, v___x_2149_, v___x_2156_);
v___x_2158_ = l_Lean_Syntax_node6(v_a_2127_, v___x_2142_, v___x_2143_, v___x_2138_, v___x_2138_, v___x_2146_, v___x_2148_, v___x_2157_);
v___x_2159_ = l_Lean_Syntax_node4(v_a_2127_, v___x_2015_, v___x_2137_, v___x_2138_, v___x_2140_, v___x_2158_);
v___x_2160_ = l_Lean_Syntax_node2(v_a_2127_, v___x_2131_, v___x_2132_, v___x_2159_);
if (lean_obj_tag(v_h_x3f_1994_) == 0)
{
v___y_2099_ = v___y_2119_;
v___y_2100_ = v___x_2128_;
v___y_2101_ = v___y_2117_;
v___y_2102_ = v___y_2121_;
v___y_2103_ = v___x_2133_;
v___y_2104_ = v___y_2115_;
v___y_2105_ = v___y_2120_;
v___y_2106_ = v___y_2116_;
v___y_2107_ = v___y_2118_;
v___y_2108_ = v___x_2160_;
goto v___jp_2098_;
}
else
{
if (v___x_2020_ == 0)
{
v___y_2099_ = v___y_2119_;
v___y_2100_ = v___x_2128_;
v___y_2101_ = v___y_2117_;
v___y_2102_ = v___y_2121_;
v___y_2103_ = v___x_2133_;
v___y_2104_ = v___y_2115_;
v___y_2105_ = v___y_2120_;
v___y_2106_ = v___y_2116_;
v___y_2107_ = v___y_2118_;
v___y_2108_ = v___x_2160_;
goto v___jp_2098_;
}
else
{
lean_object* v___x_2161_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14));
v___y_2074_ = v___y_2119_;
v___y_2075_ = v___x_2128_;
v___y_2076_ = v___y_2117_;
v___y_2077_ = v___y_2121_;
v___y_2078_ = v___x_2133_;
v___y_2079_ = v___y_2120_;
v___y_2080_ = v___y_2115_;
v___y_2081_ = v___y_2118_;
v___y_2082_ = v___y_2116_;
v___y_2083_ = v___x_2160_;
v___y_2084_ = v___x_2161_;
goto v___jp_2073_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_mutTuplePat_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_preS_1996_);
lean_dec_ref(v_xs_1995_);
lean_dec(v_invClause_1993_);
v_a_2162_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2123_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2123_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
v___jp_2170_:
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = lean_array_get_size(v_mutBinders_2173_);
v___x_2182_ = lean_nat_dec_eq(v___x_2181_, v___x_2018_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_nat_dec_eq(v___x_2181_, v___x_2013_);
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
v___x_2193_ = l_Lean_Syntax_SepArray_ofElems(v___x_2192_, v_mutBinders_2173_);
lean_dec_ref(v_mutBinders_2173_);
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
v___y_2112_ = v___y_2171_;
v___y_2113_ = v___y_2172_;
v_mutTuplePat_2114_ = v___x_2198_;
v___y_2115_ = v___y_2174_;
v___y_2116_ = v___y_2175_;
v___y_2117_ = v___y_2176_;
v___y_2118_ = v___y_2177_;
v___y_2119_ = v___y_2178_;
v___y_2120_ = v___y_2179_;
v___y_2121_ = v___y_2180_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_array_fget(v_mutBinders_2173_, v___x_2018_);
lean_dec_ref(v_mutBinders_2173_);
v___y_2112_ = v___y_2171_;
v___y_2113_ = v___y_2172_;
v_mutTuplePat_2114_ = v___x_2199_;
v___y_2115_ = v___y_2174_;
v___y_2116_ = v___y_2175_;
v___y_2117_ = v___y_2176_;
v___y_2118_ = v___y_2177_;
v___y_2119_ = v___y_2178_;
v___y_2120_ = v___y_2179_;
v___y_2121_ = v___y_2180_;
goto v___jp_2111_;
}
}
else
{
lean_object* v_ref_2200_; lean_object* v___x_2201_; lean_object* v_a_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v_mutBinders_2173_);
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
v___y_2112_ = v___y_2171_;
v___y_2113_ = v___y_2172_;
v_mutTuplePat_2114_ = v___x_2206_;
v___y_2115_ = v___y_2174_;
v___y_2116_ = v___y_2175_;
v___y_2117_ = v___y_2176_;
v___y_2118_ = v___y_2177_;
v___y_2119_ = v___y_2178_;
v___y_2120_ = v___y_2179_;
v___y_2121_ = v___y_2180_;
goto v___jp_2111_;
}
}
v___jp_2207_:
{
size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v_sz_2219_ = lean_array_size(v_loopMutVars_1999_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(v_loopMutVars_1999_, v_sz_2219_, v___x_2220_, v_mutBinders_2211_);
if (lean_obj_tag(v___x_2221_) == 0)
{
if (v_returnsEarly_2000_ == 0)
{
lean_object* v_a_2222_; 
lean_dec(v___y_2210_);
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v___y_2171_ = v___y_2208_;
v___y_2172_ = v___y_2209_;
v_mutBinders_2173_ = v_a_2222_;
v___y_2174_ = v___y_2212_;
v___y_2175_ = v___y_2213_;
v___y_2176_ = v___y_2214_;
v___y_2177_ = v___y_2215_;
v___y_2178_ = v___y_2216_;
v___y_2179_ = v___y_2217_;
v___y_2180_ = v___y_2218_;
goto v___jp_2170_;
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v_a_2223_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2224_ = lean_array_get_size(v_loopMutVars_1999_);
v___x_2225_ = lean_nat_dec_eq(v___x_2224_, v___x_2018_);
if (v___x_2225_ == 0)
{
lean_dec(v___y_2210_);
v___y_2171_ = v___y_2208_;
v___y_2172_ = v___y_2209_;
v_mutBinders_2173_ = v_a_2223_;
v___y_2174_ = v___y_2212_;
v___y_2175_ = v___y_2213_;
v___y_2176_ = v___y_2214_;
v___y_2177_ = v___y_2215_;
v___y_2178_ = v___y_2216_;
v___y_2179_ = v___y_2217_;
v___y_2180_ = v___y_2218_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_array_push(v_a_2223_, v___y_2210_);
v___y_2171_ = v___y_2208_;
v___y_2172_ = v___y_2209_;
v_mutBinders_2173_ = v___x_2226_;
v___y_2174_ = v___y_2212_;
v___y_2175_ = v___y_2213_;
v___y_2176_ = v___y_2214_;
v___y_2177_ = v___y_2215_;
v___y_2178_ = v___y_2216_;
v___y_2179_ = v___y_2217_;
v___y_2180_ = v___y_2218_;
goto v___jp_2170_;
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_preS_1996_);
lean_dec_ref(v_xs_1995_);
lean_dec(v_invClause_1993_);
v_a_2227_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2221_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2221_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
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
v___jp_2235_:
{
lean_object* v___x_2246_; lean_object* v_a_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2246_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2244_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2245_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc_n(v_a_2247_, 2);
lean_dec_ref(v___x_2246_);
v___x_2248_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_2249_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_2250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2250_, 0, v_a_2247_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = l_Lean_Syntax_node1(v_a_2247_, v___x_2248_, v___x_2250_);
v___x_2252_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
if (v_returnsEarly_2000_ == 0)
{
v___y_2208_ = v___y_2236_;
v___y_2209_ = v_invBody_2237_;
v___y_2210_ = v___x_2251_;
v_mutBinders_2211_ = v___x_2252_;
v___y_2212_ = v___y_2238_;
v___y_2213_ = v___y_2239_;
v___y_2214_ = v___y_2240_;
v___y_2215_ = v___y_2241_;
v___y_2216_ = v___y_2242_;
v___y_2217_ = v___y_2243_;
v___y_2218_ = v___y_2245_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2253_; 
lean_inc(v___x_2251_);
v___x_2253_ = lean_array_push(v___x_2252_, v___x_2251_);
v___y_2208_ = v___y_2236_;
v___y_2209_ = v_invBody_2237_;
v___y_2210_ = v___x_2251_;
v_mutBinders_2211_ = v___x_2253_;
v___y_2212_ = v___y_2238_;
v___y_2213_ = v___y_2239_;
v___y_2214_ = v___y_2240_;
v___y_2215_ = v___y_2241_;
v___y_2216_ = v___y_2242_;
v___y_2217_ = v___y_2243_;
v___y_2218_ = v___y_2245_;
goto v___jp_2207_;
}
}
v___jp_2259_:
{
lean_object* v_loopBinders_2267_; lean_object* v___x_2268_; lean_object* v_assertionBinders_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v_loopBinders_2267_ = l_Array_extract___redArg(v_binders_2258_, v___x_2018_, v___x_2255_);
v___x_2268_ = lean_array_get_size(v_binders_2258_);
v_assertionBinders_2269_ = l_Array_extract___redArg(v_binders_2258_, v___x_2255_, v___x_2268_);
lean_dec_ref(v_binders_2258_);
v___x_2270_ = lean_array_get_size(v_assertionBinders_2269_);
v___x_2271_ = lean_nat_dec_eq(v___x_2270_, v___x_2018_);
if (v___x_2271_ == 0)
{
lean_object* v_ref_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_ref_2272_ = lean_ctor_get(v___y_2265_, 5);
v___x_2273_ = l_Lean_SourceInfo_fromRef(v_ref_2272_, v___x_2271_);
v___x_2274_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9));
v___x_2275_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10));
lean_inc_n(v___x_2273_, 5);
v___x_2276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___x_2274_);
v___x_2277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2278_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2279_ = l_Array_append___redArg(v___x_2278_, v_assertionBinders_2269_);
lean_dec_ref(v_assertionBinders_2269_);
v___x_2280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2273_);
lean_ctor_set(v___x_2280_, 1, v___x_2277_);
lean_ctor_set(v___x_2280_, 2, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2273_);
lean_ctor_set(v___x_2281_, 1, v___x_2277_);
lean_ctor_set(v___x_2281_, 2, v___x_2278_);
v___x_2282_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2273_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_Syntax_node4(v___x_2273_, v___x_2015_, v___x_2280_, v___x_2281_, v___x_2283_, v_invBody_2257_);
v___x_2285_ = l_Lean_Syntax_node2(v___x_2273_, v___x_2275_, v___x_2276_, v___x_2284_);
v___y_2236_ = v_loopBinders_2267_;
v_invBody_2237_ = v___x_2285_;
v___y_2238_ = v___y_2260_;
v___y_2239_ = v___y_2261_;
v___y_2240_ = v___y_2262_;
v___y_2241_ = v___y_2263_;
v___y_2242_ = v___y_2264_;
v___y_2243_ = v___y_2265_;
v_ref_2244_ = v_ref_2272_;
v___y_2245_ = v___y_2266_;
goto v___jp_2235_;
}
else
{
lean_object* v_ref_2286_; 
lean_dec_ref(v_assertionBinders_2269_);
v_ref_2286_ = lean_ctor_get(v___y_2265_, 5);
v___y_2236_ = v_loopBinders_2267_;
v_invBody_2237_ = v_invBody_2257_;
v___y_2238_ = v___y_2260_;
v___y_2239_ = v___y_2261_;
v___y_2240_ = v___y_2262_;
v___y_2241_ = v___y_2263_;
v___y_2242_ = v___y_2264_;
v___y_2243_ = v___y_2265_;
v_ref_2244_ = v_ref_2286_;
v___y_2245_ = v___y_2266_;
goto v___jp_2235_;
}
}
}
v___jp_2021_:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_Elab_Term_exprToSyntax(v_xs_1995_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = l_Lean_Elab_Term_exprToSyntax(v_preS_1996_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_Elab_Term_exprToSyntax(v_body_1997_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v_ref_2038_; lean_object* v_m_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v_ref_2038_ = lean_ctor_get(v___y_2030_, 5);
v_m_2039_ = lean_ctor_get(v_mi_2001_, 0);
lean_inc_ref(v_m_2039_);
lean_dec_ref(v_mi_2001_);
v___x_2040_ = l_Lean_SourceInfo_fromRef(v_ref_2038_, v___y_2022_);
lean_inc(v___x_2040_);
v___x_2041_ = l_Lean_Syntax_node4(v___x_2040_, v___y_2023_, v_a_2033_, v_a_2035_, v_a_2037_, v___y_2025_);
v___x_2042_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2));
lean_inc(v___y_2024_);
v___x_2043_ = l_Lean_mkIdent(v___y_2024_);
v___x_2044_ = l_Lean_Syntax_node2(v___x_2040_, v___x_2042_, v___x_2043_, v___x_2041_);
v___x_2045_ = l_Lean_Expr_app___override(v_m_2039_, v_00_u03c3_1998_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
v___x_2047_ = lean_box(0);
v___x_2048_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2044_, v___x_2046_, v___x_2020_, v___x_2020_, v___x_2047_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2048_;
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_a_2035_);
lean_dec(v_a_2033_);
lean_dec(v___y_2025_);
lean_dec(v___y_2023_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
v_a_2049_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2036_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2036_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_a_2033_);
lean_dec(v___y_2025_);
lean_dec(v___y_2023_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
v_a_2057_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2034_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2034_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v___y_2025_);
lean_dec(v___y_2023_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_preS_1996_);
v_a_2065_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2032_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2032_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
v___jp_2073_:
{
lean_object* v___x_2085_; lean_object* v_env_2086_; uint8_t v___x_2087_; 
v___x_2085_ = lean_st_ref_get(v___y_2077_);
v_env_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_ref(v_env_2086_);
lean_dec(v___x_2085_);
lean_inc(v___y_2084_);
v___x_2087_ = l_Lean_Environment_contains(v_env_2086_, v___y_2084_, v___x_2020_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v___y_2083_);
lean_dec(v___y_2078_);
lean_dec_ref(v_mi_2001_);
lean_dec_ref(v_00_u03c3_1998_);
lean_dec_ref(v_body_1997_);
lean_dec_ref(v_preS_1996_);
lean_dec_ref(v_xs_1995_);
v___x_2088_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4);
v___x_2089_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_invClause_1993_, v___x_2088_, v___y_2080_, v___y_2082_, v___y_2076_, v___y_2081_, v___y_2074_, v___y_2079_, v___y_2077_);
lean_dec(v_invClause_1993_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_dec(v_invClause_1993_);
v___y_2022_ = v___y_2075_;
v___y_2023_ = v___y_2078_;
v___y_2024_ = v___y_2084_;
v___y_2025_ = v___y_2083_;
v___y_2026_ = v___y_2082_;
v___y_2027_ = v___y_2076_;
v___y_2028_ = v___y_2081_;
v___y_2029_ = v___y_2074_;
v___y_2030_ = v___y_2079_;
v___y_2031_ = v___y_2077_;
goto v___jp_2021_;
}
}
v___jp_2098_:
{
lean_object* v___x_2109_; 
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8));
v___y_2074_ = v___y_2099_;
v___y_2075_ = v___y_2100_;
v___y_2076_ = v___y_2101_;
v___y_2077_ = v___y_2102_;
v___y_2078_ = v___y_2103_;
v___y_2079_ = v___y_2105_;
v___y_2080_ = v___y_2104_;
v___y_2081_ = v___y_2107_;
v___y_2082_ = v___y_2106_;
v___y_2083_ = v___y_2108_;
v___y_2084_ = v___x_2109_;
goto v___jp_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___boxed(lean_object** _args){
lean_object* v_invClause_2299_ = _args[0];
lean_object* v_h_x3f_2300_ = _args[1];
lean_object* v_xs_2301_ = _args[2];
lean_object* v_preS_2302_ = _args[3];
lean_object* v_body_2303_ = _args[4];
lean_object* v_00_u03c3_2304_ = _args[5];
lean_object* v_loopMutVars_2305_ = _args[6];
lean_object* v_returnsEarly_2306_ = _args[7];
lean_object* v_mi_2307_ = _args[8];
lean_object* v_a_2308_ = _args[9];
lean_object* v_a_2309_ = _args[10];
lean_object* v_a_2310_ = _args[11];
lean_object* v_a_2311_ = _args[12];
lean_object* v_a_2312_ = _args[13];
lean_object* v_a_2313_ = _args[14];
lean_object* v_a_2314_ = _args[15];
lean_object* v_a_2315_ = _args[16];
_start:
{
uint8_t v_returnsEarly_boxed_2316_; lean_object* v_res_2317_; 
v_returnsEarly_boxed_2316_ = lean_unbox(v_returnsEarly_2306_);
v_res_2317_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(v_invClause_2299_, v_h_x3f_2300_, v_xs_2301_, v_preS_2302_, v_body_2303_, v_00_u03c3_2304_, v_loopMutVars_2305_, v_returnsEarly_boxed_2316_, v_mi_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec_ref(v_loopMutVars_2305_);
lean_dec(v_h_x3f_2300_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1(lean_object* v_00_u03b1_2318_, lean_object* v_ref_2319_, lean_object* v_msg_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_ref_2319_, v_msg_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___boxed(lean_object* v_00_u03b1_2330_, lean_object* v_ref_2331_, lean_object* v_msg_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1(v_00_u03b1_2330_, v_ref_2331_, v_msg_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v_ref_2331_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2(lean_object* v_as_2342_, size_t v_sz_2343_, size_t v_i_2344_, lean_object* v_b_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(v_as_2342_, v_sz_2343_, v_i_2344_, v_b_2345_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___boxed(lean_object* v_as_2355_, lean_object* v_sz_2356_, lean_object* v_i_2357_, lean_object* v_b_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
size_t v_sz_boxed_2367_; size_t v_i_boxed_2368_; lean_object* v_res_2369_; 
v_sz_boxed_2367_ = lean_unbox_usize(v_sz_2356_);
lean_dec(v_sz_2356_);
v_i_boxed_2368_ = lean_unbox_usize(v_i_2357_);
lean_dec(v_i_2357_);
v_res_2369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2(v_as_2355_, v_sz_boxed_2367_, v_i_boxed_2368_, v_b_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_as_2355_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1(lean_object* v_00_u03b1_2370_, lean_object* v_msg_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(v_msg_2371_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2381_, lean_object* v_msg_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1(v_00_u03b1_2381_, v_msg_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v_b_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; 
lean_inc(v___y_2400_);
lean_inc_ref(v___y_2399_);
lean_inc(v___y_2398_);
lean_inc_ref(v___y_2397_);
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc_ref(v___y_2393_);
v___x_2402_ = lean_apply_9(v_k_2392_, v_b_2396_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, lean_box(0));
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v_b_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v_b_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_2414_, uint8_t v_bi_2415_, lean_object* v_type_2416_, lean_object* v_k_2417_, uint8_t v_kind_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___f_2427_; lean_object* v___x_2428_; 
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc_ref(v___y_2419_);
v___f_2427_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2427_, 0, v_k_2417_);
lean_closure_set(v___f_2427_, 1, v___y_2419_);
lean_closure_set(v___f_2427_, 2, v___y_2420_);
lean_closure_set(v___f_2427_, 3, v___y_2421_);
v___x_2428_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2414_, v_bi_2415_, v_type_2416_, v___f_2427_, v_kind_2418_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
if (lean_obj_tag(v___x_2428_) == 0)
{
return v___x_2428_;
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_2437_, lean_object* v_bi_2438_, lean_object* v_type_2439_, lean_object* v_k_2440_, lean_object* v_kind_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
uint8_t v_bi_boxed_2450_; uint8_t v_kind_boxed_2451_; lean_object* v_res_2452_; 
v_bi_boxed_2450_ = lean_unbox(v_bi_2438_);
v_kind_boxed_2451_ = lean_unbox(v_kind_2441_);
v_res_2452_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2437_, v_bi_boxed_2450_, v_type_2439_, v_k_2440_, v_kind_boxed_2451_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___y_2442_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_2453_, lean_object* v_name_2454_, uint8_t v_bi_2455_, lean_object* v_type_2456_, lean_object* v_k_2457_, uint8_t v_kind_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2454_, v_bi_2455_, v_type_2456_, v_k_2457_, v_kind_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_2468_, lean_object* v_name_2469_, lean_object* v_bi_2470_, lean_object* v_type_2471_, lean_object* v_k_2472_, lean_object* v_kind_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
uint8_t v_bi_boxed_2482_; uint8_t v_kind_boxed_2483_; lean_object* v_res_2484_; 
v_bi_boxed_2482_ = lean_unbox(v_bi_2470_);
v_kind_boxed_2483_ = lean_unbox(v_kind_2473_);
v_res_2484_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_2468_, v_name_2469_, v_bi_boxed_2482_, v_type_2471_, v_k_2472_, v_kind_boxed_2483_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec_ref(v___y_2474_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_2485_, lean_object* v_x_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2495_, 0, v_a_2485_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_2496_, lean_object* v_x_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_2496_, v_x_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v_x_2497_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v_x_2507_, lean_object* v___f_2508_, lean_object* v___x_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2512_ = l_Lean_TSyntax_getId(v_x_2507_);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___f_2508_);
v___x_2514_ = lean_mk_empty_array_with_capacity(v___x_2509_);
v___x_2515_ = lean_array_push(v___x_2514_, v___x_2513_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v_x_2516_, lean_object* v___f_2517_, lean_object* v___x_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Elab_Do_elabDoFor___lam__2(v_x_2516_, v___f_2517_, v___x_2518_, v_x_2519_, v_x_2520_);
lean_dec(v_x_2520_);
lean_dec(v_x_2519_);
lean_dec(v___x_2518_);
lean_dec(v_x_2516_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_a_2522_, lean_object* v___x_2523_, uint8_t v___x_2524_, lean_object* v_r_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_k_2534_; lean_object* v___x_2535_; 
v_k_2534_ = lean_ctor_get(v_a_2522_, 1);
lean_inc_ref(v_k_2534_);
lean_dec_ref(v_a_2522_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc_ref(v_r_2525_);
v___x_2535_ = lean_apply_9(v_k_2534_, v_r_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, lean_box(0));
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = lean_mk_empty_array_with_capacity(v___x_2523_);
v___x_2538_ = lean_array_push(v___x_2537_, v_r_2525_);
v___x_2539_ = 0;
v___x_2540_ = 1;
v___x_2541_ = l_Lean_Meta_mkLambdaFVars(v___x_2538_, v_a_2536_, v___x_2539_, v___x_2524_, v___x_2539_, v___x_2524_, v___x_2540_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec_ref(v___x_2538_);
return v___x_2541_;
}
else
{
lean_dec_ref(v_r_2525_);
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_a_2542_, lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v_r_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
uint8_t v___x_73958__boxed_2554_; lean_object* v_res_2555_; 
v___x_73958__boxed_2554_ = lean_unbox(v___x_2544_);
v_res_2555_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_a_2542_, v___x_2543_, v___x_73958__boxed_2554_, v_r_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___x_2543_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v___x_2556_, lean_object* v_as_2557_, size_t v_sz_2558_, size_t v_i_2559_, lean_object* v_b_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
uint8_t v___x_2568_; 
v___x_2568_ = lean_usize_dec_lt(v_i_2559_, v_sz_2558_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
lean_dec_ref(v___x_2556_);
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_b_2560_);
return v___x_2569_;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_a_2570_ = lean_array_uget_borrowed(v_as_2557_, v_i_2559_);
v___x_2571_ = l_Lean_Elab_Do_MutVar_getId(v_a_2570_);
v___x_2572_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_2571_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v_ident_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc_n(v_a_2573_, 2);
lean_dec_ref_known(v___x_2572_, 1);
v_ident_2574_ = lean_ctor_get(v_a_2570_, 0);
v___x_2575_ = l_Lean_LocalDecl_toExpr(v_a_2573_);
v___x_2576_ = lean_box(0);
v___x_2577_ = lean_box(0);
v___x_2578_ = 0;
lean_inc_ref(v___x_2575_);
lean_inc(v_ident_2574_);
v___x_2579_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_2574_, v___x_2575_, v___x_2576_, v___x_2576_, v___x_2577_, v___x_2578_, v___x_2578_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref_known(v___x_2579_, 1);
v___x_2580_ = l_Lean_LocalDecl_type(v_a_2573_);
lean_dec(v_a_2573_);
v___x_2581_ = l_Lean_Meta_getDecLevel(v___x_2580_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_u_2583_; lean_object* v___x_2584_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref_known(v___x_2581_, 1);
v_u_2583_ = lean_ctor_get(v___x_2556_, 1);
lean_inc(v_u_2583_);
v___x_2584_ = l_Lean_Meta_isLevelDefEq(v_a_2582_, v_u_2583_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v___x_2585_; size_t v___x_2586_; size_t v___x_2587_; 
lean_dec_ref_known(v___x_2584_, 1);
v___x_2585_ = lean_array_push(v_b_2560_, v___x_2575_);
v___x_2586_ = ((size_t)1ULL);
v___x_2587_ = lean_usize_add(v_i_2559_, v___x_2586_);
v_i_2559_ = v___x_2587_;
v_b_2560_ = v___x_2585_;
goto _start;
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_dec_ref(v___x_2575_);
lean_dec_ref(v_b_2560_);
lean_dec_ref(v___x_2556_);
v_a_2589_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2584_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2584_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec_ref(v___x_2575_);
lean_dec_ref(v_b_2560_);
lean_dec_ref(v___x_2556_);
v_a_2597_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2581_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2581_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v___x_2575_);
lean_dec(v_a_2573_);
lean_dec_ref(v_b_2560_);
lean_dec_ref(v___x_2556_);
v_a_2605_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2579_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2579_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v_b_2560_);
lean_dec_ref(v___x_2556_);
v_a_2613_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2572_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2572_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v___x_2621_, lean_object* v_as_2622_, lean_object* v_sz_2623_, lean_object* v_i_2624_, lean_object* v_b_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
size_t v_sz_boxed_2633_; size_t v_i_boxed_2634_; lean_object* v_res_2635_; 
v_sz_boxed_2633_ = lean_unbox_usize(v_sz_2623_);
lean_dec(v_sz_2623_);
v_i_boxed_2634_ = lean_unbox_usize(v_i_2624_);
lean_dec(v_i_2624_);
v_res_2635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v___x_2621_, v_as_2622_, v_sz_boxed_2633_, v_i_boxed_2634_, v_b_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec_ref(v_as_2622_);
return v_res_2635_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_box(1);
v___x_2637_ = l_Lean_MessageData_ofFormat(v___x_2636_);
return v___x_2637_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2));
v___x_2642_ = l_Lean_MessageData_ofFormat(v___x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(lean_object* v_x_2643_, lean_object* v_x_2644_){
_start:
{
if (lean_obj_tag(v_x_2644_) == 0)
{
return v_x_2643_;
}
else
{
lean_object* v_head_2645_; lean_object* v_tail_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2668_; 
v_head_2645_ = lean_ctor_get(v_x_2644_, 0);
v_tail_2646_ = lean_ctor_get(v_x_2644_, 1);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2648_ = v_x_2644_;
v_isShared_2649_ = v_isSharedCheck_2668_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_tail_2646_);
lean_inc(v_head_2645_);
lean_dec(v_x_2644_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2668_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_before_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2666_; 
v_before_2650_ = lean_ctor_get(v_head_2645_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_head_2645_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v_head_2645_, 1);
lean_dec(v_unused_2667_);
v___x_2652_ = v_head_2645_;
v_isShared_2653_ = v_isSharedCheck_2666_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_before_2650_);
lean_dec(v_head_2645_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2666_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2654_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2653_ == 0)
{
lean_ctor_set_tag(v___x_2652_, 7);
lean_ctor_set(v___x_2652_, 1, v___x_2654_);
lean_ctor_set(v___x_2652_, 0, v_x_2643_);
v___x_2656_ = v___x_2652_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_x_2643_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2657_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3);
if (v_isShared_2649_ == 0)
{
lean_ctor_set_tag(v___x_2648_, 7);
lean_ctor_set(v___x_2648_, 1, v___x_2657_);
lean_ctor_set(v___x_2648_, 0, v___x_2656_);
v___x_2659_ = v___x_2648_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v___x_2657_);
v___x_2659_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = l_Lean_MessageData_ofSyntax(v_before_2650_);
v___x_2661_ = l_Lean_indentD(v___x_2660_);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2659_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v_x_2643_ = v___x_2662_;
v_x_2644_ = v_tail_2646_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(lean_object* v_opts_2669_, lean_object* v_opt_2670_){
_start:
{
lean_object* v_name_2671_; lean_object* v_defValue_2672_; lean_object* v_map_2673_; lean_object* v___x_2674_; 
v_name_2671_ = lean_ctor_get(v_opt_2670_, 0);
v_defValue_2672_ = lean_ctor_get(v_opt_2670_, 1);
v_map_2673_ = lean_ctor_get(v_opts_2669_, 0);
v___x_2674_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2673_, v_name_2671_);
if (lean_obj_tag(v___x_2674_) == 0)
{
uint8_t v___x_2675_; 
v___x_2675_ = lean_unbox(v_defValue_2672_);
return v___x_2675_;
}
else
{
lean_object* v_val_2676_; 
v_val_2676_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_val_2676_);
lean_dec_ref_known(v___x_2674_, 1);
if (lean_obj_tag(v_val_2676_) == 1)
{
uint8_t v_v_2677_; 
v_v_2677_ = lean_ctor_get_uint8(v_val_2676_, 0);
lean_dec_ref_known(v_val_2676_, 0);
return v_v_2677_;
}
else
{
uint8_t v___x_2678_; 
lean_dec(v_val_2676_);
v___x_2678_ = lean_unbox(v_defValue_2672_);
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_2679_, lean_object* v_opt_2680_){
_start:
{
uint8_t v_res_2681_; lean_object* v_r_2682_; 
v_res_2681_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_opts_2679_, v_opt_2680_);
lean_dec_ref(v_opt_2680_);
lean_dec_ref(v_opts_2679_);
v_r_2682_ = lean_box(v_res_2681_);
return v_r_2682_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1));
v___x_2687_ = l_Lean_MessageData_ofFormat(v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(lean_object* v_msgData_2688_, lean_object* v_macroStack_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v_options_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v_options_2692_ = lean_ctor_get(v___y_2690_, 2);
v___x_2693_ = l_Lean_Elab_pp_macroStack;
v___x_2694_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_options_2692_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; 
lean_dec(v_macroStack_2689_);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v_msgData_2688_);
return v___x_2695_;
}
else
{
if (lean_obj_tag(v_macroStack_2689_) == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_msgData_2688_);
return v___x_2696_;
}
else
{
lean_object* v_head_2697_; lean_object* v_after_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2713_; 
v_head_2697_ = lean_ctor_get(v_macroStack_2689_, 0);
lean_inc(v_head_2697_);
v_after_2698_ = lean_ctor_get(v_head_2697_, 1);
v_isSharedCheck_2713_ = !lean_is_exclusive(v_head_2697_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; 
v_unused_2714_ = lean_ctor_get(v_head_2697_, 0);
lean_dec(v_unused_2714_);
v___x_2700_ = v_head_2697_;
v_isShared_2701_ = v_isSharedCheck_2713_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_after_2698_);
lean_dec(v_head_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2713_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2701_ == 0)
{
lean_ctor_set_tag(v___x_2700_, 7);
lean_ctor_set(v___x_2700_, 1, v___x_2702_);
lean_ctor_set(v___x_2700_, 0, v_msgData_2688_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_msgData_2688_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v_msgData_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2705_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = l_Lean_MessageData_ofSyntax(v_after_2698_);
v___x_2708_ = l_Lean_indentD(v___x_2707_);
v_msgData_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2709_, 0, v___x_2706_);
lean_ctor_set(v_msgData_2709_, 1, v___x_2708_);
v___x_2710_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(v_msgData_2709_, v_macroStack_2689_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2715_, lean_object* v_macroStack_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_2715_, v_macroStack_2716_, v___y_2717_);
lean_dec_ref(v___y_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_ref_2728_; lean_object* v___x_2729_; lean_object* v_a_2730_; lean_object* v_macroStack_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2742_; 
v_ref_2728_ = lean_ctor_get(v___y_2725_, 5);
v___x_2729_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(v_msg_2720_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref(v___x_2729_);
v_macroStack_2731_ = lean_ctor_get(v___y_2721_, 1);
v___x_2732_ = l_Lean_Elab_getBetterRef(v_ref_2728_, v_macroStack_2731_);
lean_inc(v_macroStack_2731_);
v___x_2733_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_a_2730_, v_macroStack_2731_, v___y_2725_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2732_);
lean_ctor_set(v___x_2738_, 1, v_a_2734_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 1);
lean_ctor_set(v___x_2736_, 0, v___x_2738_);
v___x_2740_ = v___x_2736_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg___boxed(lean_object* v_msg_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2757_ = lean_box(0);
v___x_2758_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2));
v___x_2759_ = l_Lean_mkConst(v___x_2758_, v___x_2757_);
return v___x_2759_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4));
v___x_2762_ = l_Lean_stringToMessageData(v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6));
v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
return v___x_2765_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9));
v___x_2770_ = l_Lean_MessageData_ofFormat(v___x_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v___y_2771_, lean_object* v_monadInfo_2772_, uint8_t v_returnsEarly_2773_, lean_object* v___x_2774_, lean_object* v_a_2775_, uint8_t v___x_2776_, lean_object* v_e_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_defs_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___x_2809_; lean_object* v_returnVar_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2844_; lean_object* v___y_2845_; 
v___x_2809_ = lean_mk_empty_array_with_capacity(v___x_2774_);
if (lean_obj_tag(v_e_2777_) == 0)
{
if (v___x_2776_ == 0)
{
goto v___jp_2858_;
}
else
{
goto v___jp_2819_;
}
}
else
{
goto v___jp_2858_;
}
v___jp_2785_:
{
size_t v_sz_2793_; size_t v___x_2794_; lean_object* v___x_2795_; 
v_sz_2793_ = lean_array_size(v___y_2771_);
v___x_2794_ = ((size_t)0ULL);
v___x_2795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v_monadInfo_2772_, v___y_2771_, v_sz_2793_, v___x_2794_, v_defs_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
if (lean_obj_tag(v___x_2795_) == 0)
{
if (v_returnsEarly_2773_ == 0)
{
return v___x_2795_;
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
v___x_2797_ = lean_array_get_size(v___y_2771_);
v___x_2798_ = lean_nat_dec_eq(v___x_2797_, v___x_2774_);
if (v___x_2798_ == 0)
{
lean_dec(v_a_2796_);
return v___x_2795_;
}
else
{
lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2807_; 
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v___x_2795_, 0);
lean_dec(v_unused_2808_);
v___x_2800_ = v___x_2795_;
v_isShared_2801_ = v_isSharedCheck_2807_;
goto v_resetjp_2799_;
}
else
{
lean_dec(v___x_2795_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2807_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2805_; 
v___x_2802_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3);
v___x_2803_ = lean_array_push(v_a_2796_, v___x_2802_);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2803_);
v___x_2805_ = v___x_2800_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
else
{
return v___x_2795_;
}
}
v___jp_2810_:
{
lean_object* v___x_2818_; 
v___x_2818_ = lean_array_push(v___x_2809_, v_returnVar_2811_);
v_defs_2786_ = v___x_2818_;
v___y_2787_ = v___y_2812_;
v___y_2788_ = v___y_2813_;
v___y_2789_ = v___y_2814_;
v___y_2790_ = v___y_2815_;
v___y_2791_ = v___y_2816_;
v___y_2792_ = v___y_2817_;
goto v___jp_2785_;
}
v___jp_2819_:
{
if (v_returnsEarly_2773_ == 0)
{
lean_dec(v_e_2777_);
lean_dec_ref(v_a_2775_);
v_defs_2786_ = v___x_2809_;
v___y_2787_ = v___y_2778_;
v___y_2788_ = v___y_2779_;
v___y_2789_ = v___y_2780_;
v___y_2790_ = v___y_2781_;
v___y_2791_ = v___y_2782_;
v___y_2792_ = v___y_2783_;
goto v___jp_2785_;
}
else
{
if (lean_obj_tag(v_e_2777_) == 0)
{
lean_object* v_resultType_2820_; lean_object* v___x_2821_; 
v_resultType_2820_ = lean_ctor_get(v_a_2775_, 0);
lean_inc_ref(v_resultType_2820_);
lean_dec_ref(v_a_2775_);
v___x_2821_ = l_Lean_Meta_mkNone(v_resultType_2820_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v_returnVar_2811_ = v_a_2822_;
v___y_2812_ = v___y_2778_;
v___y_2813_ = v___y_2779_;
v___y_2814_ = v___y_2780_;
v___y_2815_ = v___y_2781_;
v___y_2816_ = v___y_2782_;
v___y_2817_ = v___y_2783_;
goto v___jp_2810_;
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_monadInfo_2772_);
v_a_2823_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2821_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2821_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
else
{
lean_object* v_val_2831_; lean_object* v_resultType_2832_; lean_object* v___x_2833_; 
v_val_2831_ = lean_ctor_get(v_e_2777_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v_e_2777_, 1);
v_resultType_2832_ = lean_ctor_get(v_a_2775_, 0);
lean_inc_ref(v_resultType_2832_);
lean_dec_ref(v_a_2775_);
v___x_2833_ = l_Lean_Meta_mkSome(v_resultType_2832_, v_val_2831_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v_returnVar_2811_ = v_a_2834_;
v___y_2812_ = v___y_2778_;
v___y_2813_ = v___y_2779_;
v___y_2814_ = v___y_2780_;
v___y_2815_ = v___y_2781_;
v___y_2816_ = v___y_2782_;
v___y_2817_ = v___y_2783_;
goto v___jp_2810_;
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_monadInfo_2772_);
v_a_2835_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2833_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2833_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
v___jp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_inc_ref(v___y_2844_);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___y_2844_);
lean_ctor_set(v___x_2846_, 1, v___y_2845_);
v___x_2847_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5);
v___x_2848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2846_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v___x_2848_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
v___jp_2858_:
{
if (v_returnsEarly_2773_ == 0)
{
lean_object* v___x_2859_; 
lean_dec_ref(v___x_2809_);
lean_dec_ref(v_a_2775_);
lean_dec_ref(v_monadInfo_2772_);
v___x_2859_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7);
if (lean_obj_tag(v_e_2777_) == 0)
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10);
v___y_2844_ = v___x_2859_;
v___y_2845_ = v___x_2860_;
goto v___jp_2843_;
}
else
{
lean_object* v_val_2861_; lean_object* v___x_2862_; 
v_val_2861_ = lean_ctor_get(v_e_2777_, 0);
lean_inc(v_val_2861_);
lean_dec_ref_known(v_e_2777_, 1);
v___x_2862_ = l_Lean_MessageData_ofExpr(v_val_2861_);
v___y_2844_ = v___x_2859_;
v___y_2845_ = v___x_2862_;
goto v___jp_2843_;
}
}
else
{
goto v___jp_2819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v___y_2863_, lean_object* v_monadInfo_2864_, lean_object* v_returnsEarly_2865_, lean_object* v___x_2866_, lean_object* v_a_2867_, lean_object* v___x_2868_, lean_object* v_e_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
uint8_t v_returnsEarly_boxed_2877_; uint8_t v___x_74364__boxed_2878_; lean_object* v_res_2879_; 
v_returnsEarly_boxed_2877_ = lean_unbox(v_returnsEarly_2865_);
v___x_74364__boxed_2878_ = lean_unbox(v___x_2868_);
v_res_2879_ = l_Lean_Elab_Do_elabDoFor___lam__3(v___y_2863_, v_monadInfo_2864_, v_returnsEarly_boxed_2877_, v___x_2866_, v_a_2867_, v___x_74364__boxed_2878_, v_e_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___x_2866_);
lean_dec_ref(v___y_2863_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_name_2880_, lean_object* v_type_2881_, lean_object* v_k_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
uint8_t v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = 0;
v___x_2892_ = 0;
v___x_2893_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2880_, v___x_2891_, v_type_2881_, v_k_2882_, v___x_2892_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_name_2894_, lean_object* v_type_2895_, lean_object* v_k_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_2894_, v_type_2895_, v_k_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v___y_2897_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(uint8_t v_returnsEarly_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_doBlockResultType_2926_, lean_object* v_a_2927_, lean_object* v_v_2928_, lean_object* v_u_2929_, lean_object* v___f_2930_, lean_object* v___y_2931_, lean_object* v___x_2932_, lean_object* v___x_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_ret_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; 
if (v_returnsEarly_2923_ == 0)
{
lean_object* v___x_2997_; 
lean_dec_ref(v___f_2930_);
lean_dec(v_u_2929_);
lean_dec(v_v_2928_);
lean_dec_ref(v_a_2927_);
lean_dec_ref(v_doBlockResultType_2926_);
lean_dec(v_a_2925_);
v___x_2997_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_2924_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
return v___x_2997_;
}
else
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_Meta_getFVarFromUserName(v_a_2925_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
v___x_3000_ = lean_array_get_size(v___y_2931_);
v___x_3001_ = lean_nat_dec_eq(v___x_3000_, v___x_2932_);
if (v___x_3001_ == 0)
{
v_ret_2943_ = v_a_2999_;
v___y_2944_ = v___y_2934_;
v___y_2945_ = v___y_2935_;
v___y_2946_ = v___y_2936_;
v___y_2947_ = v___y_2937_;
v___y_2948_ = v___y_2938_;
v___y_2949_ = v___y_2939_;
v___y_2950_ = v___y_2940_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3002_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__9));
v___x_3003_ = lean_mk_empty_array_with_capacity(v___x_2933_);
v___x_3004_ = lean_array_push(v___x_3003_, v_a_2999_);
v___x_3005_ = l_Lean_Meta_mkAppM(v___x_3002_, v___x_3004_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v_ret_2943_ = v_a_3006_;
v___y_2944_ = v___y_2934_;
v___y_2945_ = v___y_2935_;
v___y_2946_ = v___y_2936_;
v___y_2947_ = v___y_2937_;
v___y_2948_ = v___y_2938_;
v___y_2949_ = v___y_2939_;
v___y_2950_ = v___y_2940_;
goto v___jp_2942_;
}
else
{
lean_dec_ref(v___f_2930_);
lean_dec(v_u_2929_);
lean_dec(v_v_2928_);
lean_dec_ref(v_a_2927_);
lean_dec_ref(v_doBlockResultType_2926_);
lean_dec_ref(v_a_2924_);
return v___x_3005_;
}
}
}
else
{
lean_dec_ref(v___f_2930_);
lean_dec(v_u_2929_);
lean_dec(v_v_2928_);
lean_dec_ref(v_a_2927_);
lean_dec_ref(v_doBlockResultType_2926_);
lean_dec_ref(v_a_2924_);
return v___x_2998_;
}
}
v___jp_2942_:
{
lean_object* v___x_2951_; 
lean_inc(v___y_2950_);
lean_inc_ref(v___y_2949_);
lean_inc(v___y_2948_);
lean_inc_ref(v___y_2947_);
lean_inc_ref(v_ret_2943_);
v___x_2951_ = lean_infer_type(v_ret_2943_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2926_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_2924_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__1));
v___x_2958_ = l_Lean_Core_mkFreshUserName(v___x_2957_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v_resultType_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2987_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v_resultType_2960_ = lean_ctor_get(v_a_2927_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_a_2927_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v_a_2927_, 1);
lean_dec(v_unused_2988_);
v___x_2962_ = v_a_2927_;
v_isShared_2963_ = v_isSharedCheck_2987_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_resultType_2960_);
lean_dec(v_a_2927_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2987_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; uint8_t v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2964_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__2));
v___x_2965_ = 0;
v___x_2966_ = l_Lean_mkLambda(v___x_2964_, v___x_2965_, v_a_2952_, v_a_2954_);
v___x_2967_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__6));
v___x_2968_ = l_Lean_Level_succ___override(v_v_2928_);
v___x_2969_ = lean_box(0);
if (v_isShared_2963_ == 0)
{
lean_ctor_set_tag(v___x_2962_, 1);
lean_ctor_set(v___x_2962_, 1, v___x_2969_);
lean_ctor_set(v___x_2962_, 0, v___x_2968_);
v___x_2971_ = v___x_2962_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2972_, 0, v_u_2929_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = l_Lean_mkConst(v___x_2967_, v___x_2972_);
lean_inc_ref(v_resultType_2960_);
v___x_2974_ = l_Lean_mkApp3(v___x_2973_, v_resultType_2960_, v___x_2966_, v_ret_2943_);
v___x_2975_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_a_2959_, v_resultType_2960_, v___f_2930_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2985_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_2985_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2985_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
v___x_2980_ = l_Lean_mkSimpleThunk(v_a_2956_);
v___x_2981_ = l_Lean_mkAppB(v___x_2974_, v_a_2976_, v___x_2980_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2981_);
v___x_2983_ = v___x_2978_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
else
{
lean_dec_ref(v___x_2974_);
lean_dec(v_a_2956_);
return v___x_2975_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v_a_2956_);
lean_dec(v_a_2954_);
lean_dec(v_a_2952_);
lean_dec_ref(v_ret_2943_);
lean_dec_ref(v___f_2930_);
lean_dec(v_u_2929_);
lean_dec(v_v_2928_);
lean_dec_ref(v_a_2927_);
v_a_2989_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2958_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2958_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
else
{
lean_dec(v_a_2954_);
lean_dec(v_a_2952_);
lean_dec_ref(v_ret_2943_);
lean_dec_ref(v___f_2930_);
lean_dec(v_u_2929_);
lean_dec(v_v_2928_);
lean_dec_ref(v_a_2927_);
return v___x_2955_;
}
}
else
{
lean_dec(v_a_2952_);
lean_dec_ref(v_ret_2943_);
lean_dec_ref(v___f_2930_);
lean_dec(v_u_2929_);
lean_dec(v_v_2928_);
lean_dec_ref(v_a_2927_);
lean_dec_ref(v_a_2924_);
return v___x_2953_;
}
}
else
{
lean_dec_ref(v_ret_2943_);
lean_dec_ref(v___f_2930_);
lean_dec(v_u_2929_);
lean_dec(v_v_2928_);
lean_dec_ref(v_a_2927_);
lean_dec_ref(v_doBlockResultType_2926_);
lean_dec_ref(v_a_2924_);
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object** _args){
lean_object* v_returnsEarly_3007_ = _args[0];
lean_object* v_a_3008_ = _args[1];
lean_object* v_a_3009_ = _args[2];
lean_object* v_doBlockResultType_3010_ = _args[3];
lean_object* v_a_3011_ = _args[4];
lean_object* v_v_3012_ = _args[5];
lean_object* v_u_3013_ = _args[6];
lean_object* v___f_3014_ = _args[7];
lean_object* v___y_3015_ = _args[8];
lean_object* v___x_3016_ = _args[9];
lean_object* v___x_3017_ = _args[10];
lean_object* v___y_3018_ = _args[11];
lean_object* v___y_3019_ = _args[12];
lean_object* v___y_3020_ = _args[13];
lean_object* v___y_3021_ = _args[14];
lean_object* v___y_3022_ = _args[15];
lean_object* v___y_3023_ = _args[16];
lean_object* v___y_3024_ = _args[17];
lean_object* v___y_3025_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_3026_; lean_object* v_res_3027_; 
v_returnsEarly_boxed_3026_ = lean_unbox(v_returnsEarly_3007_);
v_res_3027_ = l_Lean_Elab_Do_elabDoFor___lam__4(v_returnsEarly_boxed_3026_, v_a_3008_, v_a_3009_, v_doBlockResultType_3010_, v_a_3011_, v_v_3012_, v_u_3013_, v___f_3014_, v___y_3015_, v___x_3016_, v___x_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___x_3017_);
lean_dec(v___x_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___x_3030_, uint8_t v___x_3031_, lean_object* v_postS_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = l_Lean_Expr_fvarId_x21(v_postS_3032_);
v___x_3042_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_3028_, v___x_3041_, v___y_3029_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v___x_3044_ = lean_mk_empty_array_with_capacity(v___x_3030_);
v___x_3045_ = lean_array_push(v___x_3044_, v_postS_3032_);
v___x_3046_ = 0;
v___x_3047_ = 1;
v___x_3048_ = l_Lean_Meta_mkLambdaFVars(v___x_3045_, v_a_3043_, v___x_3046_, v___x_3031_, v___x_3046_, v___x_3031_, v___x_3047_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
lean_dec_ref(v___x_3045_);
return v___x_3048_;
}
else
{
lean_dec_ref(v_postS_3032_);
return v___x_3042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___x_3051_, lean_object* v___x_3052_, lean_object* v_postS_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
uint8_t v___x_74824__boxed_3062_; lean_object* v_res_3063_; 
v___x_74824__boxed_3062_ = lean_unbox(v___x_3052_);
v_res_3063_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___y_3049_, v___y_3050_, v___x_3051_, v___x_74824__boxed_3062_, v_postS_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___x_3051_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_3065_, lean_object* v_u_3066_, lean_object* v___x_3067_, lean_object* v___x_3068_, lean_object* v_snd_3069_, lean_object* v___x_3070_, lean_object* v_e_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_e_3071_);
lean_inc(v___y_3078_);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
lean_inc(v___y_3074_);
lean_inc_ref(v___y_3073_);
v___x_3081_ = lean_apply_8(v___f_3065_, v___x_3080_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, lean_box(0));
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3083_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3081_, 1);
v___x_3083_ = l_Lean_Meta_mkProdMkN(v_a_3082_, v_u_3066_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_fst_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v_fst_3085_ = lean_ctor_get(v_a_3084_, 0);
lean_inc(v_fst_3085_);
lean_dec(v_a_3084_);
v___x_3086_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_3087_ = l_Lean_Name_mkStr2(v___x_3067_, v___x_3086_);
v___x_3088_ = l_Lean_mkConst(v___x_3087_, v___x_3068_);
v___x_3089_ = l_Lean_mkAppB(v___x_3088_, v_snd_3069_, v_fst_3085_);
v___x_3090_ = l_Lean_Elab_Do_mkPureApp(v___x_3070_, v___x_3089_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
return v___x_3090_;
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_snd_3069_);
lean_dec(v___x_3068_);
lean_dec_ref(v___x_3067_);
v_a_3091_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3083_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3083_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_snd_3069_);
lean_dec(v___x_3068_);
lean_dec_ref(v___x_3067_);
lean_dec(v_u_3066_);
v_a_3099_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3081_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3081_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_3107_, lean_object* v_u_3108_, lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v_snd_3111_, lean_object* v___x_3112_, lean_object* v_e_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_3107_, v_u_3108_, v___x_3109_, v___x_3110_, v_snd_3111_, v___x_3112_, v_e_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec_ref(v___y_3114_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___f_3124_, lean_object* v___x_3125_, lean_object* v_u_3126_, lean_object* v___x_3127_, lean_object* v___x_3128_, lean_object* v_snd_3129_, lean_object* v___x_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___x_3139_; 
lean_inc(v___y_3137_);
lean_inc_ref(v___y_3136_);
lean_inc(v___y_3135_);
lean_inc_ref(v___y_3134_);
lean_inc(v___y_3133_);
lean_inc_ref(v___y_3132_);
v___x_3139_ = lean_apply_8(v___f_3124_, v___x_3125_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, lean_box(0));
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = l_Lean_Meta_mkProdMkN(v_a_3140_, v_u_3126_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v_fst_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___x_3141_, 1);
v_fst_3143_ = lean_ctor_get(v_a_3142_, 0);
lean_inc(v_fst_3143_);
lean_dec(v_a_3142_);
v___x_3144_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__7___closed__0));
v___x_3145_ = l_Lean_Name_mkStr2(v___x_3127_, v___x_3144_);
v___x_3146_ = l_Lean_mkConst(v___x_3145_, v___x_3128_);
v___x_3147_ = l_Lean_mkAppB(v___x_3146_, v_snd_3129_, v_fst_3143_);
v___x_3148_ = l_Lean_Elab_Do_mkPureApp(v___x_3130_, v___x_3147_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
return v___x_3148_;
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec_ref(v___x_3130_);
lean_dec_ref(v_snd_3129_);
lean_dec(v___x_3128_);
lean_dec_ref(v___x_3127_);
v_a_3149_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3141_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3141_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref(v___x_3130_);
lean_dec_ref(v_snd_3129_);
lean_dec(v___x_3128_);
lean_dec_ref(v___x_3127_);
lean_dec(v_u_3126_);
v_a_3157_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3139_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3139_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___f_3165_, lean_object* v___x_3166_, lean_object* v_u_3167_, lean_object* v___x_3168_, lean_object* v___x_3169_, lean_object* v_snd_3170_, lean_object* v___x_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___f_3165_, v___x_3166_, v_u_3167_, v___x_3168_, v___x_3169_, v_snd_3170_, v___x_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3172_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v___f_3181_, lean_object* v___x_3182_, lean_object* v_u_3183_, lean_object* v___x_3184_, lean_object* v___x_3185_, lean_object* v_snd_3186_, lean_object* v___x_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; 
lean_inc(v___y_3194_);
lean_inc_ref(v___y_3193_);
lean_inc(v___y_3192_);
lean_inc_ref(v___y_3191_);
lean_inc(v___y_3190_);
lean_inc_ref(v___y_3189_);
v___x_3196_ = lean_apply_8(v___f_3181_, v___x_3182_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, lean_box(0));
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = l_Lean_Meta_mkProdMkN(v_a_3197_, v_u_3183_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v_fst_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3198_, 1);
v_fst_3200_ = lean_ctor_get(v_a_3199_, 0);
lean_inc(v_fst_3200_);
lean_dec(v_a_3199_);
v___x_3201_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_3202_ = l_Lean_Name_mkStr2(v___x_3184_, v___x_3201_);
v___x_3203_ = l_Lean_mkConst(v___x_3202_, v___x_3185_);
v___x_3204_ = l_Lean_mkAppB(v___x_3203_, v_snd_3186_, v_fst_3200_);
v___x_3205_ = l_Lean_Elab_Do_mkPureApp(v___x_3187_, v___x_3204_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
return v___x_3205_;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec_ref(v___x_3187_);
lean_dec_ref(v_snd_3186_);
lean_dec(v___x_3185_);
lean_dec_ref(v___x_3184_);
v_a_3206_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3198_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3198_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___x_3187_);
lean_dec_ref(v_snd_3186_);
lean_dec(v___x_3185_);
lean_dec_ref(v___x_3184_);
lean_dec(v_u_3183_);
v_a_3214_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3196_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3196_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object* v___f_3222_, lean_object* v___x_3223_, lean_object* v_u_3224_, lean_object* v___x_3225_, lean_object* v___x_3226_, lean_object* v_snd_3227_, lean_object* v___x_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_Elab_Do_elabDoFor___lam__8(v___f_3222_, v___x_3223_, v_u_3224_, v___x_3225_, v___x_3226_, v_snd_3227_, v___x_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec_ref(v___y_3229_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v___x_3238_, lean_object* v___f_3239_, lean_object* v___f_3240_, lean_object* v___x_3241_, lean_object* v___x_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_monadInfo_3251_; lean_object* v_mutVars_3252_; lean_object* v_mutVarDefs_3253_; lean_object* v_contInfo_3254_; uint8_t v_deadCode_3255_; lean_object* v_ops_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3264_; 
v_monadInfo_3251_ = lean_ctor_get(v___y_3243_, 0);
v_mutVars_3252_ = lean_ctor_get(v___y_3243_, 1);
v_mutVarDefs_3253_ = lean_ctor_get(v___y_3243_, 2);
v_contInfo_3254_ = lean_ctor_get(v___y_3243_, 4);
v_deadCode_3255_ = lean_ctor_get_uint8(v___y_3243_, sizeof(void*)*6);
v_ops_3256_ = lean_ctor_get(v___y_3243_, 5);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___y_3243_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v___y_3243_, 3);
lean_dec(v_unused_3265_);
v___x_3258_ = v___y_3243_;
v_isShared_3259_ = v_isSharedCheck_3264_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_ops_3256_);
lean_inc(v_contInfo_3254_);
lean_inc(v_mutVarDefs_3253_);
lean_inc(v_mutVars_3252_);
lean_inc(v_monadInfo_3251_);
lean_dec(v___y_3243_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3264_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 3, v___x_3238_);
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_monadInfo_3251_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v_mutVars_3252_);
lean_ctor_set(v_reuseFailAlloc_3263_, 2, v_mutVarDefs_3253_);
lean_ctor_set(v_reuseFailAlloc_3263_, 3, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3263_, 4, v_contInfo_3254_);
lean_ctor_set(v_reuseFailAlloc_3263_, 5, v_ops_3256_);
lean_ctor_set_uint8(v_reuseFailAlloc_3263_, sizeof(void*)*6, v_deadCode_3255_);
v___x_3261_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3262_; 
v___x_3262_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_3239_, v___f_3240_, v___x_3241_, v___x_3242_, v___x_3261_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec_ref(v___x_3261_);
return v___x_3262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object* v___x_3266_, lean_object* v___f_3267_, lean_object* v___f_3268_, lean_object* v___x_3269_, lean_object* v___x_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_Elab_Do_elabDoFor___lam__9(v___x_3266_, v___f_3267_, v___f_3268_, v___x_3269_, v___x_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_u_3285_, lean_object* v_snd_3286_, lean_object* v___f_3287_, lean_object* v___x_3288_, lean_object* v_body_3289_, uint8_t v___x_3290_, lean_object* v___y_3291_, lean_object* v_xh_3292_, lean_object* v_loopS_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v_resultType_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3339_; 
v_resultType_3302_ = lean_ctor_get(v_a_3283_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_a_3283_);
if (v_isSharedCheck_3339_ == 0)
{
lean_object* v_unused_3340_; 
v_unused_3340_ = lean_ctor_get(v_a_3283_, 1);
lean_dec(v_unused_3340_);
v___x_3304_ = v_a_3283_;
v_isShared_3305_ = v_isSharedCheck_3339_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_resultType_3302_);
lean_dec(v_a_3283_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3339_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_resultName_3306_; lean_object* v_resultType_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3337_; 
v_resultName_3306_ = lean_ctor_get(v_a_3284_, 0);
v_resultType_3307_ = lean_ctor_get(v_a_3284_, 1);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_a_3284_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v_a_3284_, 2);
lean_dec(v_unused_3338_);
v___x_3309_ = v_a_3284_;
v_isShared_3310_ = v_isSharedCheck_3337_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_resultType_3307_);
lean_inc(v_resultName_3306_);
lean_dec(v_a_3284_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3337_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___f_3318_; lean_object* v___f_3319_; lean_object* v___f_3320_; lean_object* v___x_3322_; 
v___x_3311_ = l_Lean_Expr_fvarId_x21(v_loopS_3293_);
v___x_3312_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0));
v___x_3313_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_3314_ = lean_box(0);
lean_inc_n(v_u_3285_, 3);
v___x_3315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3315_, 0, v_u_3285_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
lean_inc_ref_n(v___x_3315_, 3);
v___x_3316_ = l_Lean_mkConst(v___x_3313_, v___x_3315_);
lean_inc_ref_n(v_snd_3286_, 3);
v___x_3317_ = l_Lean_Expr_app___override(v___x_3316_, v_snd_3286_);
lean_inc_ref_n(v___x_3317_, 3);
lean_inc_ref_n(v___f_3287_, 2);
v___f_3318_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 6);
lean_closure_set(v___f_3318_, 0, v___f_3287_);
lean_closure_set(v___f_3318_, 1, v_u_3285_);
lean_closure_set(v___f_3318_, 2, v___x_3312_);
lean_closure_set(v___f_3318_, 3, v___x_3315_);
lean_closure_set(v___f_3318_, 4, v_snd_3286_);
lean_closure_set(v___f_3318_, 5, v___x_3317_);
lean_inc(v___x_3288_);
v___f_3319_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 15, 7);
lean_closure_set(v___f_3319_, 0, v___f_3287_);
lean_closure_set(v___f_3319_, 1, v___x_3288_);
lean_closure_set(v___f_3319_, 2, v_u_3285_);
lean_closure_set(v___f_3319_, 3, v___x_3312_);
lean_closure_set(v___f_3319_, 4, v___x_3315_);
lean_closure_set(v___f_3319_, 5, v_snd_3286_);
lean_closure_set(v___f_3319_, 6, v___x_3317_);
v___f_3320_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 15, 7);
lean_closure_set(v___f_3320_, 0, v___f_3287_);
lean_closure_set(v___f_3320_, 1, v___x_3288_);
lean_closure_set(v___f_3320_, 2, v_u_3285_);
lean_closure_set(v___f_3320_, 3, v___x_3312_);
lean_closure_set(v___f_3320_, 4, v___x_3315_);
lean_closure_set(v___f_3320_, 5, v_snd_3286_);
lean_closure_set(v___f_3320_, 6, v___x_3317_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v___f_3318_);
v___x_3322_ = v___x_3304_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_resultType_3302_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v___f_3318_);
v___x_3322_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
uint8_t v___x_3323_; lean_object* v___x_3325_; 
v___x_3323_ = 1;
lean_inc_ref(v___f_3319_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 2, v___f_3319_);
v___x_3325_ = v___x_3309_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_resultName_3306_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_resultType_3307_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v___f_3319_);
v___x_3325_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___f_3328_; lean_object* v___x_3329_; 
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*3, v___x_3323_);
v___x_3326_ = lean_box(v___x_3290_);
v___x_3327_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_3327_, 0, v_body_3289_);
lean_closure_set(v___x_3327_, 1, v___x_3325_);
lean_closure_set(v___x_3327_, 2, v___x_3326_);
v___f_3328_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 13, 5);
lean_closure_set(v___f_3328_, 0, v___x_3317_);
lean_closure_set(v___f_3328_, 1, v___f_3320_);
lean_closure_set(v___f_3328_, 2, v___f_3319_);
lean_closure_set(v___f_3328_, 3, v___x_3322_);
lean_closure_set(v___f_3328_, 4, v___x_3327_);
v___x_3329_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_3291_, v___x_3311_, v___f_3328_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; uint8_t v___x_3333_; lean_object* v___x_3334_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v___x_3331_ = lean_array_push(v_xh_3292_, v_loopS_3293_);
v___x_3332_ = 0;
v___x_3333_ = 1;
v___x_3334_ = l_Lean_Meta_mkLambdaFVars(v___x_3331_, v_a_3330_, v___x_3332_, v___x_3290_, v___x_3332_, v___x_3290_, v___x_3333_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec_ref(v___x_3331_);
return v___x_3334_;
}
else
{
lean_dec_ref(v_loopS_3293_);
lean_dec_ref(v_xh_3292_);
return v___x_3329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_a_3341_ = _args[0];
lean_object* v_a_3342_ = _args[1];
lean_object* v_u_3343_ = _args[2];
lean_object* v_snd_3344_ = _args[3];
lean_object* v___f_3345_ = _args[4];
lean_object* v___x_3346_ = _args[5];
lean_object* v_body_3347_ = _args[6];
lean_object* v___x_3348_ = _args[7];
lean_object* v___y_3349_ = _args[8];
lean_object* v_xh_3350_ = _args[9];
lean_object* v_loopS_3351_ = _args[10];
lean_object* v___y_3352_ = _args[11];
lean_object* v___y_3353_ = _args[12];
lean_object* v___y_3354_ = _args[13];
lean_object* v___y_3355_ = _args[14];
lean_object* v___y_3356_ = _args[15];
lean_object* v___y_3357_ = _args[16];
lean_object* v___y_3358_ = _args[17];
lean_object* v___y_3359_ = _args[18];
_start:
{
uint8_t v___x_75233__boxed_3360_; lean_object* v_res_3361_; 
v___x_75233__boxed_3360_ = lean_unbox(v___x_3348_);
v_res_3361_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_a_3341_, v_a_3342_, v_u_3343_, v_snd_3344_, v___f_3345_, v___x_3346_, v_body_3347_, v___x_75233__boxed_3360_, v___y_3349_, v_xh_3350_, v_loopS_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec_ref(v___y_3352_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v_x_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_u_3367_, lean_object* v_snd_3368_, lean_object* v___f_3369_, lean_object* v___x_3370_, lean_object* v_body_3371_, uint8_t v___x_3372_, lean_object* v___y_3373_, lean_object* v_a_3374_, lean_object* v_h_x3f_3375_, lean_object* v___x_3376_, lean_object* v_xh_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_array_get_borrowed(v___x_3362_, v_xh_3377_, v___x_3363_);
lean_inc(v___x_3386_);
v___x_3387_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_3364_, v___x_3386_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v___x_3388_; lean_object* v___f_3389_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; 
lean_dec_ref_known(v___x_3387_, 1);
v___x_3388_ = lean_box(v___x_3372_);
lean_inc_ref(v_xh_3377_);
lean_inc_ref(v_snd_3368_);
v___f_3389_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 10);
lean_closure_set(v___f_3389_, 0, v_a_3365_);
lean_closure_set(v___f_3389_, 1, v_a_3366_);
lean_closure_set(v___f_3389_, 2, v_u_3367_);
lean_closure_set(v___f_3389_, 3, v_snd_3368_);
lean_closure_set(v___f_3389_, 4, v___f_3369_);
lean_closure_set(v___f_3389_, 5, v___x_3370_);
lean_closure_set(v___f_3389_, 6, v_body_3371_);
lean_closure_set(v___f_3389_, 7, v___x_3388_);
lean_closure_set(v___f_3389_, 8, v___y_3373_);
lean_closure_set(v___f_3389_, 9, v_xh_3377_);
if (lean_obj_tag(v_h_x3f_3375_) == 1)
{
lean_object* v_val_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_val_3401_ = lean_ctor_get(v_h_x3f_3375_, 0);
lean_inc(v_val_3401_);
lean_dec_ref_known(v_h_x3f_3375_, 1);
v___x_3402_ = lean_array_get(v___x_3362_, v_xh_3377_, v___x_3376_);
lean_dec_ref(v_xh_3377_);
v___x_3403_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_3401_, v___x_3402_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_dec_ref_known(v___x_3403_, 1);
v___y_3391_ = v___y_3378_;
v___y_3392_ = v___y_3379_;
v___y_3393_ = v___y_3380_;
v___y_3394_ = v___y_3381_;
v___y_3395_ = v___y_3382_;
v___y_3396_ = v___y_3383_;
v___y_3397_ = v___y_3384_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v___f_3389_);
lean_dec(v_a_3374_);
lean_dec_ref(v_snd_3368_);
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3403_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3403_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
else
{
lean_dec_ref(v_xh_3377_);
lean_dec(v_h_x3f_3375_);
v___y_3391_ = v___y_3378_;
v___y_3392_ = v___y_3379_;
v___y_3393_ = v___y_3380_;
v___y_3394_ = v___y_3381_;
v___y_3395_ = v___y_3382_;
v___y_3396_ = v___y_3383_;
v___y_3397_ = v___y_3384_;
goto v___jp_3390_;
}
v___jp_3390_:
{
uint8_t v___x_3398_; uint8_t v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = 0;
v___x_3399_ = 1;
v___x_3400_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_3374_, v___x_3398_, v_snd_3368_, v___f_3389_, v___x_3399_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3400_;
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec_ref(v_xh_3377_);
lean_dec(v_h_x3f_3375_);
lean_dec(v_a_3374_);
lean_dec(v___y_3373_);
lean_dec(v_body_3371_);
lean_dec(v___x_3370_);
lean_dec_ref(v___f_3369_);
lean_dec_ref(v_snd_3368_);
lean_dec(v_u_3367_);
lean_dec_ref(v_a_3366_);
lean_dec_ref(v_a_3365_);
v_a_3412_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3387_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3387_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object** _args){
lean_object* v___x_3420_ = _args[0];
lean_object* v___x_3421_ = _args[1];
lean_object* v_x_3422_ = _args[2];
lean_object* v_a_3423_ = _args[3];
lean_object* v_a_3424_ = _args[4];
lean_object* v_u_3425_ = _args[5];
lean_object* v_snd_3426_ = _args[6];
lean_object* v___f_3427_ = _args[7];
lean_object* v___x_3428_ = _args[8];
lean_object* v_body_3429_ = _args[9];
lean_object* v___x_3430_ = _args[10];
lean_object* v___y_3431_ = _args[11];
lean_object* v_a_3432_ = _args[12];
lean_object* v_h_x3f_3433_ = _args[13];
lean_object* v___x_3434_ = _args[14];
lean_object* v_xh_3435_ = _args[15];
lean_object* v___y_3436_ = _args[16];
lean_object* v___y_3437_ = _args[17];
lean_object* v___y_3438_ = _args[18];
lean_object* v___y_3439_ = _args[19];
lean_object* v___y_3440_ = _args[20];
lean_object* v___y_3441_ = _args[21];
lean_object* v___y_3442_ = _args[22];
lean_object* v___y_3443_ = _args[23];
_start:
{
uint8_t v___x_75356__boxed_3444_; lean_object* v_res_3445_; 
v___x_75356__boxed_3444_ = lean_unbox(v___x_3430_);
v_res_3445_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___x_3420_, v___x_3421_, v_x_3422_, v_a_3423_, v_a_3424_, v_u_3425_, v_snd_3426_, v___f_3427_, v___x_3428_, v_body_3429_, v___x_75356__boxed_3444_, v___y_3431_, v_a_3432_, v_h_x3f_3433_, v___x_3434_, v_xh_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___x_3434_);
lean_dec(v___x_3421_);
lean_dec_ref(v___x_3420_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v___x_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_val_3456_, lean_object* v_a_3457_, lean_object* v_x_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3467_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_3468_ = lean_box(0);
v___x_3469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3469_, 0, v_a_3451_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3470_, 0, v_a_3452_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_Lean_mkConst(v___x_3467_, v___x_3470_);
v___x_3472_ = l_Lean_instInhabitedExpr;
v___x_3473_ = lean_array_get_borrowed(v___x_3472_, v_x_3458_, v___x_3453_);
lean_inc(v___x_3473_);
v___x_3474_ = l_Lean_mkApp5(v___x_3471_, v_a_3454_, v_a_3455_, v_val_3456_, v_a_3457_, v___x_3473_);
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v___x_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_val_3481_, lean_object* v_a_3482_, lean_object* v_x_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_3476_, v_a_3477_, v___x_3478_, v_a_3479_, v_a_3480_, v_val_3481_, v_a_3482_, v_x_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v_x_3483_);
lean_dec(v___x_3478_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(size_t v_sz_3493_, size_t v_i_3494_, lean_object* v_bs_3495_){
_start:
{
uint8_t v___x_3496_; 
v___x_3496_ = lean_usize_dec_lt(v_i_3494_, v_sz_3493_);
if (v___x_3496_ == 0)
{
return v_bs_3495_;
}
else
{
lean_object* v_v_3497_; lean_object* v___x_3498_; lean_object* v_bs_x27_3499_; lean_object* v___x_3500_; size_t v___x_3501_; size_t v___x_3502_; lean_object* v___x_3503_; 
v_v_3497_ = lean_array_uget(v_bs_3495_, v_i_3494_);
v___x_3498_ = lean_unsigned_to_nat(0u);
v_bs_x27_3499_ = lean_array_uset(v_bs_3495_, v_i_3494_, v___x_3498_);
v___x_3500_ = l_Lean_Elab_Do_MutVar_getId(v_v_3497_);
lean_dec(v_v_3497_);
v___x_3501_ = ((size_t)1ULL);
v___x_3502_ = lean_usize_add(v_i_3494_, v___x_3501_);
v___x_3503_ = lean_array_uset(v_bs_x27_3499_, v_i_3494_, v___x_3500_);
v_i_3494_ = v___x_3502_;
v_bs_3495_ = v___x_3503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_sz_3505_, lean_object* v_i_3506_, lean_object* v_bs_3507_){
_start:
{
size_t v_sz_boxed_3508_; size_t v_i_boxed_3509_; lean_object* v_res_3510_; 
v_sz_boxed_3508_ = lean_unbox_usize(v_sz_3505_);
lean_dec(v_sz_3505_);
v_i_boxed_3509_ = lean_unbox_usize(v_i_3506_);
lean_dec(v_i_3506_);
v_res_3510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_boxed_3508_, v_i_boxed_3509_, v_bs_3507_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_a_3511_, lean_object* v_as_3512_, size_t v_i_3513_, size_t v_stop_3514_, lean_object* v_b_3515_){
_start:
{
lean_object* v___y_3517_; uint8_t v___x_3521_; 
v___x_3521_ = lean_usize_dec_eq(v_i_3513_, v_stop_3514_);
if (v___x_3521_ == 0)
{
lean_object* v_reassigns_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v_reassigns_3522_ = lean_ctor_get(v_a_3511_, 1);
v___x_3523_ = lean_array_uget_borrowed(v_as_3512_, v_i_3513_);
v___x_3524_ = l_Lean_Elab_Do_MutVar_getId(v___x_3523_);
v___x_3525_ = l_Lean_NameSet_contains(v_reassigns_3522_, v___x_3524_);
lean_dec(v___x_3524_);
if (v___x_3525_ == 0)
{
v___y_3517_ = v_b_3515_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3526_; 
lean_inc(v___x_3523_);
v___x_3526_ = lean_array_push(v_b_3515_, v___x_3523_);
v___y_3517_ = v___x_3526_;
goto v___jp_3516_;
}
}
else
{
return v_b_3515_;
}
v___jp_3516_:
{
size_t v___x_3518_; size_t v___x_3519_; 
v___x_3518_ = ((size_t)1ULL);
v___x_3519_ = lean_usize_add(v_i_3513_, v___x_3518_);
v_i_3513_ = v___x_3519_;
v_b_3515_ = v___y_3517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_a_3527_, lean_object* v_as_3528_, lean_object* v_i_3529_, lean_object* v_stop_3530_, lean_object* v_b_3531_){
_start:
{
size_t v_i_boxed_3532_; size_t v_stop_boxed_3533_; lean_object* v_res_3534_; 
v_i_boxed_3532_ = lean_unbox_usize(v_i_3529_);
lean_dec(v_i_3529_);
v_stop_boxed_3533_ = lean_unbox_usize(v_stop_3530_);
lean_dec(v_stop_3530_);
v_res_3534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_3527_, v_as_3528_, v_i_boxed_3532_, v_stop_boxed_3533_, v_b_3531_);
lean_dec_ref(v_as_3528_);
lean_dec_ref(v_a_3527_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(lean_object* v___x_3535_, lean_object* v_a_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_73796__overap_3546_; lean_object* v___x_3547_; 
v___x_3545_ = l_Lean_instInhabitedExpr;
v___x_73796__overap_3546_ = l_instInhabitedOfMonad___redArg(v___x_3535_, v___x_3545_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3540_);
lean_inc(v___y_3539_);
lean_inc_ref(v___y_3538_);
lean_inc_ref(v___y_3537_);
v___x_3547_ = lean_apply_8(v___x_73796__overap_3546_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, lean_box(0));
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed(lean_object* v___x_3548_, lean_object* v_a_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(v___x_3548_, v_a_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v_a_3549_);
return v_res_3558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_instMonadEIO(lean_box(0));
return v___x_3559_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0);
v___x_3561_ = l_StateRefT_x27_instMonad___redArg(v___x_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed(lean_object* v_acc_3568_, lean_object* v_declInfos_3569_, lean_object* v_k_3570_, lean_object* v_kind_3571_, lean_object* v_x_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v_kind_boxed_3581_; lean_object* v_res_3582_; 
v_kind_boxed_3581_ = lean_unbox(v_kind_3571_);
v_res_3582_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(v_acc_3568_, v_declInfos_3569_, v_k_3570_, v_kind_boxed_3581_, v_x_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec_ref(v___y_3573_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(lean_object* v_declInfos_3583_, lean_object* v_k_3584_, uint8_t v_kind_3585_, lean_object* v_acc_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; lean_object* v_toApplicative_3596_; lean_object* v_toFunctor_3597_; lean_object* v_toSeq_3598_; lean_object* v_toSeqLeft_3599_; lean_object* v_toSeqRight_3600_; lean_object* v___f_3601_; lean_object* v___f_3602_; lean_object* v___f_3603_; lean_object* v___f_3604_; lean_object* v___x_3605_; lean_object* v___f_3606_; lean_object* v___f_3607_; lean_object* v___f_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v_toApplicative_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3692_; 
v___x_3595_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1);
v_toApplicative_3596_ = lean_ctor_get(v___x_3595_, 0);
v_toFunctor_3597_ = lean_ctor_get(v_toApplicative_3596_, 0);
v_toSeq_3598_ = lean_ctor_get(v_toApplicative_3596_, 2);
v_toSeqLeft_3599_ = lean_ctor_get(v_toApplicative_3596_, 3);
v_toSeqRight_3600_ = lean_ctor_get(v_toApplicative_3596_, 4);
v___f_3601_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2));
v___f_3602_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3597_, 2);
v___f_3603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3603_, 0, v_toFunctor_3597_);
v___f_3604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3604_, 0, v_toFunctor_3597_);
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___f_3603_);
lean_ctor_set(v___x_3605_, 1, v___f_3604_);
lean_inc(v_toSeqRight_3600_);
v___f_3606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3606_, 0, v_toSeqRight_3600_);
lean_inc(v_toSeqLeft_3599_);
v___f_3607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3607_, 0, v_toSeqLeft_3599_);
lean_inc(v_toSeq_3598_);
v___f_3608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3608_, 0, v_toSeq_3598_);
v___x_3609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3605_);
lean_ctor_set(v___x_3609_, 1, v___f_3601_);
lean_ctor_set(v___x_3609_, 2, v___f_3608_);
lean_ctor_set(v___x_3609_, 3, v___f_3607_);
lean_ctor_set(v___x_3609_, 4, v___f_3606_);
v___x_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set(v___x_3610_, 1, v___f_3602_);
v___x_3611_ = l_StateRefT_x27_instMonad___redArg(v___x_3610_);
v_toApplicative_3612_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; 
v_unused_3693_ = lean_ctor_get(v___x_3611_, 1);
lean_dec(v_unused_3693_);
v___x_3614_ = v___x_3611_;
v_isShared_3615_ = v_isSharedCheck_3692_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_toApplicative_3612_);
lean_dec(v___x_3611_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3692_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v_toFunctor_3616_; lean_object* v_toSeq_3617_; lean_object* v_toSeqLeft_3618_; lean_object* v_toSeqRight_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3690_; 
v_toFunctor_3616_ = lean_ctor_get(v_toApplicative_3612_, 0);
v_toSeq_3617_ = lean_ctor_get(v_toApplicative_3612_, 2);
v_toSeqLeft_3618_ = lean_ctor_get(v_toApplicative_3612_, 3);
v_toSeqRight_3619_ = lean_ctor_get(v_toApplicative_3612_, 4);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_toApplicative_3612_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; 
v_unused_3691_ = lean_ctor_get(v_toApplicative_3612_, 1);
lean_dec(v_unused_3691_);
v___x_3621_ = v_toApplicative_3612_;
v_isShared_3622_ = v_isSharedCheck_3690_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_toSeqRight_3619_);
lean_inc(v_toSeqLeft_3618_);
lean_inc(v_toSeq_3617_);
lean_inc(v_toFunctor_3616_);
lean_dec(v_toApplicative_3612_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3690_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___f_3623_; lean_object* v___f_3624_; lean_object* v___f_3625_; lean_object* v___f_3626_; lean_object* v___x_3627_; lean_object* v___f_3628_; lean_object* v___f_3629_; lean_object* v___f_3630_; lean_object* v___x_3632_; 
v___f_3623_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4));
v___f_3624_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3616_);
v___f_3625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3625_, 0, v_toFunctor_3616_);
v___f_3626_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3626_, 0, v_toFunctor_3616_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___f_3625_);
lean_ctor_set(v___x_3627_, 1, v___f_3626_);
v___f_3628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3628_, 0, v_toSeqRight_3619_);
v___f_3629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3629_, 0, v_toSeqLeft_3618_);
v___f_3630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3630_, 0, v_toSeq_3617_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 4, v___f_3628_);
lean_ctor_set(v___x_3621_, 3, v___f_3629_);
lean_ctor_set(v___x_3621_, 2, v___f_3630_);
lean_ctor_set(v___x_3621_, 1, v___f_3623_);
lean_ctor_set(v___x_3621_, 0, v___x_3627_);
v___x_3632_ = v___x_3621_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v___f_3623_);
lean_ctor_set(v_reuseFailAlloc_3689_, 2, v___f_3630_);
lean_ctor_set(v_reuseFailAlloc_3689_, 3, v___f_3629_);
lean_ctor_set(v_reuseFailAlloc_3689_, 4, v___f_3628_);
v___x_3632_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3634_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 1, v___f_3624_);
lean_ctor_set(v___x_3614_, 0, v___x_3632_);
v___x_3634_ = v___x_3614_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___f_3624_);
v___x_3634_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_object* v___x_3635_; lean_object* v_toApplicative_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3686_; 
v___x_3635_ = l_StateRefT_x27_instMonad___redArg(v___x_3634_);
v_toApplicative_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v___x_3635_, 1);
lean_dec(v_unused_3687_);
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3686_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_toApplicative_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3686_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v_toFunctor_3640_; lean_object* v_toSeq_3641_; lean_object* v_toSeqLeft_3642_; lean_object* v_toSeqRight_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3684_; 
v_toFunctor_3640_ = lean_ctor_get(v_toApplicative_3636_, 0);
v_toSeq_3641_ = lean_ctor_get(v_toApplicative_3636_, 2);
v_toSeqLeft_3642_ = lean_ctor_get(v_toApplicative_3636_, 3);
v_toSeqRight_3643_ = lean_ctor_get(v_toApplicative_3636_, 4);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_toApplicative_3636_);
if (v_isSharedCheck_3684_ == 0)
{
lean_object* v_unused_3685_; 
v_unused_3685_ = lean_ctor_get(v_toApplicative_3636_, 1);
lean_dec(v_unused_3685_);
v___x_3645_ = v_toApplicative_3636_;
v_isShared_3646_ = v_isSharedCheck_3684_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_toSeqRight_3643_);
lean_inc(v_toSeqLeft_3642_);
lean_inc(v_toSeq_3641_);
lean_inc(v_toFunctor_3640_);
lean_dec(v_toApplicative_3636_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3684_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___f_3647_; lean_object* v___f_3648_; lean_object* v___f_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; lean_object* v___f_3652_; lean_object* v___f_3653_; lean_object* v___f_3654_; lean_object* v___x_3656_; 
v___f_3647_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6));
v___f_3648_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7));
lean_inc_ref(v_toFunctor_3640_);
v___f_3649_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3649_, 0, v_toFunctor_3640_);
v___f_3650_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3650_, 0, v_toFunctor_3640_);
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___f_3649_);
lean_ctor_set(v___x_3651_, 1, v___f_3650_);
v___f_3652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3652_, 0, v_toSeqRight_3643_);
v___f_3653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3653_, 0, v_toSeqLeft_3642_);
v___f_3654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3654_, 0, v_toSeq_3641_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 4, v___f_3652_);
lean_ctor_set(v___x_3645_, 3, v___f_3653_);
lean_ctor_set(v___x_3645_, 2, v___f_3654_);
lean_ctor_set(v___x_3645_, 1, v___f_3647_);
lean_ctor_set(v___x_3645_, 0, v___x_3651_);
v___x_3656_ = v___x_3645_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v___f_3647_);
lean_ctor_set(v_reuseFailAlloc_3683_, 2, v___f_3654_);
lean_ctor_set(v_reuseFailAlloc_3683_, 3, v___f_3653_);
lean_ctor_set(v_reuseFailAlloc_3683_, 4, v___f_3652_);
v___x_3656_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 1, v___f_3648_);
lean_ctor_set(v___x_3638_, 0, v___x_3656_);
v___x_3658_ = v___x_3638_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___f_3648_);
v___x_3658_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3659_ = l_ReaderT_instMonad___redArg(v___x_3658_);
v___x_3660_ = lean_array_get_size(v_acc_3586_);
v___x_3661_ = lean_array_get_size(v_declInfos_3583_);
v___x_3662_ = lean_nat_dec_lt(v___x_3660_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; 
lean_dec_ref(v___x_3659_);
lean_dec_ref(v_declInfos_3583_);
lean_inc(v___y_3593_);
lean_inc_ref(v___y_3592_);
lean_inc(v___y_3591_);
lean_inc_ref(v___y_3590_);
lean_inc(v___y_3589_);
lean_inc_ref(v___y_3588_);
lean_inc_ref(v___y_3587_);
v___x_3663_ = lean_apply_9(v_k_3584_, v_acc_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, lean_box(0));
return v___x_3663_;
}
else
{
lean_object* v___f_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; lean_object* v___f_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v_snd_3672_; lean_object* v_fst_3673_; lean_object* v_fst_3674_; lean_object* v_snd_3675_; lean_object* v___x_3676_; 
v___f_3664_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3664_, 0, v___x_3659_);
v___x_3665_ = lean_box(0);
v___x_3666_ = 0;
v___f_3667_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3667_, 0, v___f_3664_);
v___x_3668_ = lean_box(v___x_3666_);
v___x_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
lean_ctor_set(v___x_3669_, 1, v___f_3667_);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3665_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_array_get(v___x_3670_, v_declInfos_3583_, v___x_3660_);
lean_dec_ref_known(v___x_3670_, 2);
v_snd_3672_ = lean_ctor_get(v___x_3671_, 1);
lean_inc(v_snd_3672_);
v_fst_3673_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_fst_3673_);
lean_dec(v___x_3671_);
v_fst_3674_ = lean_ctor_get(v_snd_3672_, 0);
lean_inc(v_fst_3674_);
v_snd_3675_ = lean_ctor_get(v_snd_3672_, 1);
lean_inc(v_snd_3675_);
lean_dec(v_snd_3672_);
lean_inc(v___y_3593_);
lean_inc_ref(v___y_3592_);
lean_inc(v___y_3591_);
lean_inc_ref(v___y_3590_);
lean_inc(v___y_3589_);
lean_inc_ref(v___y_3588_);
lean_inc_ref(v___y_3587_);
lean_inc_ref(v_acc_3586_);
v___x_3676_ = lean_apply_9(v_snd_3675_, v_acc_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, lean_box(0));
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3678_; lean_object* v___f_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
v___x_3678_ = lean_box(v_kind_3585_);
v___f_3679_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed), 13, 4);
lean_closure_set(v___f_3679_, 0, v_acc_3586_);
lean_closure_set(v___f_3679_, 1, v_declInfos_3583_);
lean_closure_set(v___f_3679_, 2, v_k_3584_);
lean_closure_set(v___f_3679_, 3, v___x_3678_);
v___x_3680_ = lean_unbox(v_fst_3674_);
lean_dec(v_fst_3674_);
v___x_3681_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_3673_, v___x_3680_, v_a_3677_, v___f_3679_, v_kind_3585_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v___x_3681_;
}
else
{
lean_dec(v_fst_3674_);
lean_dec(v_fst_3673_);
lean_dec_ref(v_acc_3586_);
lean_dec_ref(v_k_3584_);
lean_dec_ref(v_declInfos_3583_);
return v___x_3676_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(lean_object* v_acc_3694_, lean_object* v_declInfos_3695_, lean_object* v_k_3696_, uint8_t v_kind_3697_, lean_object* v_x_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_array_push(v_acc_3694_, v_x_3698_);
v___x_3708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_3695_, v_k_3696_, v_kind_3697_, v___x_3707_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___boxed(lean_object* v_declInfos_3709_, lean_object* v_k_3710_, lean_object* v_kind_3711_, lean_object* v_acc_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
uint8_t v_kind_boxed_3721_; lean_object* v_res_3722_; 
v_kind_boxed_3721_ = lean_unbox(v_kind_3711_);
v_res_3722_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_3709_, v_k_3710_, v_kind_boxed_3721_, v_acc_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(lean_object* v_declInfos_3725_, lean_object* v_k_3726_, uint8_t v_kind_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0));
v___x_3737_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_3725_, v_k_3726_, v_kind_3727_, v___x_3736_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_declInfos_3738_, lean_object* v_k_3739_, lean_object* v_kind_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
uint8_t v_kind_boxed_3749_; lean_object* v_res_3750_; 
v_kind_boxed_3749_ = lean_unbox(v_kind_3740_);
v_res_3750_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_declInfos_3738_, v_k_3739_, v_kind_boxed_3749_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec_ref(v___y_3741_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(size_t v_sz_3751_, size_t v_i_3752_, lean_object* v_bs_3753_){
_start:
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_usize_dec_lt(v_i_3752_, v_sz_3751_);
if (v___x_3754_ == 0)
{
return v_bs_3753_;
}
else
{
lean_object* v_v_3755_; lean_object* v_fst_3756_; lean_object* v_snd_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3773_; 
v_v_3755_ = lean_array_uget(v_bs_3753_, v_i_3752_);
v_fst_3756_ = lean_ctor_get(v_v_3755_, 0);
v_snd_3757_ = lean_ctor_get(v_v_3755_, 1);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_v_3755_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3759_ = v_v_3755_;
v_isShared_3760_ = v_isSharedCheck_3773_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_snd_3757_);
lean_inc(v_fst_3756_);
lean_dec(v_v_3755_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3773_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3761_; lean_object* v_bs_x27_3762_; uint8_t v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3761_ = lean_unsigned_to_nat(0u);
v_bs_x27_3762_ = lean_array_uset(v_bs_3753_, v_i_3752_, v___x_3761_);
v___x_3763_ = 0;
v___x_3764_ = lean_box(v___x_3763_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3764_);
v___x_3766_ = v___x_3759_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_snd_3757_);
v___x_3766_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; size_t v___x_3768_; size_t v___x_3769_; lean_object* v___x_3770_; 
v___x_3767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3767_, 0, v_fst_3756_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = ((size_t)1ULL);
v___x_3769_ = lean_usize_add(v_i_3752_, v___x_3768_);
v___x_3770_ = lean_array_uset(v_bs_x27_3762_, v_i_3752_, v___x_3767_);
v_i_3752_ = v___x_3769_;
v_bs_3753_ = v___x_3770_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5___boxed(lean_object* v_sz_3774_, lean_object* v_i_3775_, lean_object* v_bs_3776_){
_start:
{
size_t v_sz_boxed_3777_; size_t v_i_boxed_3778_; lean_object* v_res_3779_; 
v_sz_boxed_3777_ = lean_unbox_usize(v_sz_3774_);
lean_dec(v_sz_3774_);
v_i_boxed_3778_ = lean_unbox_usize(v_i_3775_);
lean_dec(v_i_3775_);
v_res_3779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_boxed_3777_, v_i_boxed_3778_, v_bs_3776_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_3780_, lean_object* v_k_3781_, uint8_t v_kind_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
size_t v_sz_3791_; size_t v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v_sz_3791_ = lean_array_size(v_declInfos_3780_);
v___x_3792_ = ((size_t)0ULL);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_3791_, v___x_3792_, v_declInfos_3780_);
v___x_3794_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v___x_3793_, v_k_3781_, v_kind_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_3795_, lean_object* v_k_3796_, lean_object* v_kind_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
uint8_t v_kind_boxed_3806_; lean_object* v_res_3807_; 
v_kind_boxed_3806_ = lean_unbox(v_kind_3797_);
v_res_3807_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_3795_, v_k_3796_, v_kind_boxed_3806_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec_ref(v___y_3798_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_3836_, lean_object* v_dec_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___x_3846_; uint8_t v___x_3847_; 
v___x_3846_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_3836_);
v___x_3847_ = l_Lean_Syntax_isOfKind(v_stx_3836_, v___x_3846_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; 
lean_dec_ref(v_dec_3837_);
lean_dec(v_stx_3836_);
v___x_3848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_3848_;
}
else
{
lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3849_ = lean_unsigned_to_nat(1u);
v___x_3850_ = l_Lean_Syntax_getArg(v_stx_3836_, v___x_3849_);
lean_inc(v___x_3850_);
v___x_3851_ = l_Lean_Syntax_matchesNull(v___x_3850_, v___x_3849_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; 
lean_dec(v___x_3850_);
lean_dec_ref(v_dec_3837_);
lean_dec(v_stx_3836_);
v___x_3852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_3852_;
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; uint8_t v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v_forIn_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; uint8_t v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; uint8_t v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; uint8_t v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; uint8_t v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; uint8_t v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; uint8_t v___y_3999_; lean_object* v_fst_4000_; lean_object* v_snd_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; uint8_t v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; uint8_t v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; uint8_t v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; uint8_t v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; 
v___x_3853_ = lean_unsigned_to_nat(0u);
v___x_3854_ = l_Lean_Syntax_getArg(v___x_3850_, v___x_3853_);
lean_dec(v___x_3850_);
v___x_3855_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_3854_);
v___x_3856_ = l_Lean_Syntax_isOfKind(v___x_3854_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_4204_; 
lean_dec(v___x_3854_);
lean_dec_ref(v_dec_3837_);
lean_dec(v_stx_3836_);
v___x_4204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4204_;
}
else
{
lean_object* v_tk_4205_; lean_object* v___y_4207_; uint8_t v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v_inv_x3f_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v_h_x3f_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___x_4367_; uint8_t v___x_4368_; 
v_tk_4205_ = l_Lean_Syntax_getArg(v_stx_3836_, v___x_3853_);
v___x_4367_ = l_Lean_Syntax_getArg(v___x_3854_, v___x_3853_);
v___x_4368_ = l_Lean_Syntax_isNone(v___x_4367_);
if (v___x_4368_ == 0)
{
lean_object* v___x_4369_; uint8_t v___x_4370_; 
v___x_4369_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4367_);
v___x_4370_ = l_Lean_Syntax_matchesNull(v___x_4367_, v___x_4369_);
if (v___x_4370_ == 0)
{
lean_object* v___x_4371_; 
lean_dec(v___x_4367_);
lean_dec(v_tk_4205_);
lean_dec(v___x_3854_);
lean_dec_ref(v_dec_3837_);
lean_dec(v_stx_3836_);
v___x_4371_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4371_;
}
else
{
lean_object* v_h_x3f_4372_; lean_object* v___x_4373_; 
v_h_x3f_4372_ = l_Lean_Syntax_getArg(v___x_4367_, v___x_3853_);
lean_dec(v___x_4367_);
v___x_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4373_, 0, v_h_x3f_4372_);
v_h_x3f_4342_ = v___x_4373_;
v___y_4343_ = v_a_3838_;
v___y_4344_ = v_a_3839_;
v___y_4345_ = v_a_3840_;
v___y_4346_ = v_a_3841_;
v___y_4347_ = v_a_3842_;
v___y_4348_ = v_a_3843_;
v___y_4349_ = v_a_3844_;
goto v___jp_4341_;
}
}
else
{
lean_object* v___x_4374_; 
lean_dec(v___x_4367_);
v___x_4374_ = lean_box(0);
v_h_x3f_4342_ = v___x_4374_;
v___y_4343_ = v_a_3838_;
v___y_4344_ = v_a_3839_;
v___y_4345_ = v_a_3840_;
v___y_4346_ = v_a_3841_;
v___y_4347_ = v_a_3842_;
v___y_4348_ = v_a_3843_;
v___y_4349_ = v_a_3844_;
goto v___jp_4341_;
}
v___jp_4206_:
{
lean_object* v___x_4222_; 
v___x_4222_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_3837_, v_tk_4205_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v_tk_4205_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4222_, 1);
v___x_4224_ = lean_mk_empty_array_with_capacity(v___x_3849_);
lean_inc(v___y_4210_);
v___x_4225_ = lean_array_push(v___x_4224_, v___y_4210_);
v___x_4226_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_4225_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec_ref(v___x_4225_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v___x_4227_; 
lean_dec_ref_known(v___x_4226_, 1);
v___x_4227_ = l_Lean_Meta_mkFreshLevelMVar(v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = l_Lean_Meta_mkFreshLevelMVar(v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v___x_4229_, 1);
lean_inc(v_a_4228_);
v___x_4231_ = l_Lean_Level_succ___override(v_a_4228_);
v___x_4232_ = l_Lean_mkSort(v___x_4231_);
v___x_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
v___x_4234_ = 0;
v___x_4235_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_4236_ = l_Lean_Meta_mkFreshExprMVar(v___x_4233_, v___x_4234_, v___x_4235_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4308_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4308_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4308_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4244_; 
lean_inc(v_a_4230_);
v___x_4241_ = l_Lean_Level_succ___override(v_a_4230_);
v___x_4242_ = l_Lean_mkSort(v___x_4241_);
if (v_isShared_4240_ == 0)
{
lean_ctor_set_tag(v___x_4239_, 1);
lean_ctor_set(v___x_4239_, 0, v___x_4242_);
v___x_4244_ = v___x_4239_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__12));
v___x_4246_ = l_Lean_Meta_mkFreshExprMVar(v___x_4244_, v___x_4234_, v___x_4245_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4306_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4249_ = v___x_4246_;
v_isShared_4250_ = v_isSharedCheck_4306_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4246_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4306_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
lean_inc(v_a_4247_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set_tag(v___x_4249_, 1);
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = lean_box(0);
v___x_4254_ = l_Lean_Elab_Term_elabTermEnsuringType(v___y_4213_, v___x_4252_, v___x_3856_, v___x_3856_, v___x_4253_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v___x_4256_; lean_object* v_body_4257_; lean_object* v___x_4258_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4254_, 1);
v___x_4256_ = lean_unsigned_to_nat(4u);
v_body_4257_ = l_Lean_Syntax_getArg(v_stx_3836_, v___x_4256_);
lean_dec(v_stx_3836_);
lean_inc(v_body_4257_);
v___x_4258_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_4257_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4260_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4258_, 1);
v___x_4260_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_4215_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4260_, 1);
v___x_4262_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__14));
v___x_4263_ = l_Lean_Core_mkFreshUserName(v___x_4262_, v___y_4220_, v___y_4221_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; lean_object* v_monadInfo_4265_; lean_object* v_mutVars_4266_; lean_object* v___f_4267_; lean_object* v___f_4268_; lean_object* v___x_4269_; lean_object* v___f_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; uint8_t v___x_4273_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
lean_dec_ref_known(v___x_4263_, 1);
v_monadInfo_4265_ = lean_ctor_get(v___y_4215_, 0);
v_mutVars_4266_ = lean_ctor_get(v___y_4215_, 1);
lean_inc(v_a_4237_);
v___f_4267_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4267_, 0, v_a_4237_);
lean_inc_ref(v___f_4267_);
lean_inc(v___y_4207_);
v___f_4268_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4268_, 0, v___y_4207_);
lean_closure_set(v___f_4268_, 1, v___f_4267_);
lean_closure_set(v___f_4268_, 2, v___x_3849_);
v___x_4269_ = lean_box(v___x_3856_);
lean_inc(v_a_4261_);
v___f_4270_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 12, 3);
lean_closure_set(v___f_4270_, 0, v_a_4261_);
lean_closure_set(v___f_4270_, 1, v___x_3849_);
lean_closure_set(v___f_4270_, 2, v___x_4269_);
v___x_4271_ = lean_array_get_size(v_mutVars_4266_);
v___x_4272_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__15));
v___x_4273_ = lean_nat_dec_lt(v___x_3853_, v___x_4271_);
if (v___x_4273_ == 0)
{
lean_inc(v_a_4228_);
lean_inc(v_a_4230_);
lean_inc(v_a_4247_);
lean_inc(v_a_4255_);
lean_inc(v_a_4264_);
lean_inc(v_a_4237_);
v___y_4155_ = v_a_4237_;
v___y_4156_ = v_a_4264_;
v___y_4157_ = v___f_4267_;
v___y_4158_ = v___y_4208_;
v___y_4159_ = v_a_4255_;
v___y_4160_ = v_a_4247_;
v___y_4161_ = v___y_4207_;
v___y_4162_ = v_body_4257_;
v___y_4163_ = v_a_4261_;
v___y_4164_ = v___f_4268_;
v___y_4165_ = v_monadInfo_4265_;
v___y_4166_ = v_a_4230_;
v___y_4167_ = v___y_4209_;
v___y_4168_ = v_a_4228_;
v___y_4169_ = v___f_4270_;
v___y_4170_ = v_a_4223_;
v___y_4171_ = v_a_4237_;
v___y_4172_ = v_a_4264_;
v___y_4173_ = v___y_4211_;
v___y_4174_ = v___x_4234_;
v___y_4175_ = v_a_4255_;
v___y_4176_ = v_a_4247_;
v___y_4177_ = v___y_4216_;
v___y_4178_ = v___y_4218_;
v___y_4179_ = v___y_4221_;
v___y_4180_ = v_a_4259_;
v___y_4181_ = v___y_4217_;
v___y_4182_ = v___y_4210_;
v___y_4183_ = v_inv_x3f_4214_;
v___y_4184_ = v___y_4219_;
v___y_4185_ = v_a_4230_;
v___y_4186_ = v___y_4212_;
v___y_4187_ = v___y_4220_;
v___y_4188_ = v_a_4228_;
v___y_4189_ = v___y_4215_;
v___y_4190_ = v___x_4272_;
goto v___jp_4154_;
}
else
{
uint8_t v___x_4274_; 
v___x_4274_ = lean_nat_dec_le(v___x_4271_, v___x_4271_);
if (v___x_4274_ == 0)
{
if (v___x_4273_ == 0)
{
lean_inc(v_a_4228_);
lean_inc(v_a_4230_);
lean_inc(v_a_4247_);
lean_inc(v_a_4255_);
lean_inc(v_a_4264_);
lean_inc(v_a_4237_);
v___y_4155_ = v_a_4237_;
v___y_4156_ = v_a_4264_;
v___y_4157_ = v___f_4267_;
v___y_4158_ = v___y_4208_;
v___y_4159_ = v_a_4255_;
v___y_4160_ = v_a_4247_;
v___y_4161_ = v___y_4207_;
v___y_4162_ = v_body_4257_;
v___y_4163_ = v_a_4261_;
v___y_4164_ = v___f_4268_;
v___y_4165_ = v_monadInfo_4265_;
v___y_4166_ = v_a_4230_;
v___y_4167_ = v___y_4209_;
v___y_4168_ = v_a_4228_;
v___y_4169_ = v___f_4270_;
v___y_4170_ = v_a_4223_;
v___y_4171_ = v_a_4237_;
v___y_4172_ = v_a_4264_;
v___y_4173_ = v___y_4211_;
v___y_4174_ = v___x_4234_;
v___y_4175_ = v_a_4255_;
v___y_4176_ = v_a_4247_;
v___y_4177_ = v___y_4216_;
v___y_4178_ = v___y_4218_;
v___y_4179_ = v___y_4221_;
v___y_4180_ = v_a_4259_;
v___y_4181_ = v___y_4217_;
v___y_4182_ = v___y_4210_;
v___y_4183_ = v_inv_x3f_4214_;
v___y_4184_ = v___y_4219_;
v___y_4185_ = v_a_4230_;
v___y_4186_ = v___y_4212_;
v___y_4187_ = v___y_4220_;
v___y_4188_ = v_a_4228_;
v___y_4189_ = v___y_4215_;
v___y_4190_ = v___x_4272_;
goto v___jp_4154_;
}
else
{
size_t v___x_4275_; size_t v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = ((size_t)0ULL);
v___x_4276_ = lean_usize_of_nat(v___x_4271_);
v___x_4277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_4259_, v_mutVars_4266_, v___x_4275_, v___x_4276_, v___x_4272_);
lean_inc(v_a_4228_);
lean_inc(v_a_4230_);
lean_inc(v_a_4247_);
lean_inc(v_a_4255_);
lean_inc(v_a_4264_);
lean_inc(v_a_4237_);
v___y_4155_ = v_a_4237_;
v___y_4156_ = v_a_4264_;
v___y_4157_ = v___f_4267_;
v___y_4158_ = v___y_4208_;
v___y_4159_ = v_a_4255_;
v___y_4160_ = v_a_4247_;
v___y_4161_ = v___y_4207_;
v___y_4162_ = v_body_4257_;
v___y_4163_ = v_a_4261_;
v___y_4164_ = v___f_4268_;
v___y_4165_ = v_monadInfo_4265_;
v___y_4166_ = v_a_4230_;
v___y_4167_ = v___y_4209_;
v___y_4168_ = v_a_4228_;
v___y_4169_ = v___f_4270_;
v___y_4170_ = v_a_4223_;
v___y_4171_ = v_a_4237_;
v___y_4172_ = v_a_4264_;
v___y_4173_ = v___y_4211_;
v___y_4174_ = v___x_4234_;
v___y_4175_ = v_a_4255_;
v___y_4176_ = v_a_4247_;
v___y_4177_ = v___y_4216_;
v___y_4178_ = v___y_4218_;
v___y_4179_ = v___y_4221_;
v___y_4180_ = v_a_4259_;
v___y_4181_ = v___y_4217_;
v___y_4182_ = v___y_4210_;
v___y_4183_ = v_inv_x3f_4214_;
v___y_4184_ = v___y_4219_;
v___y_4185_ = v_a_4230_;
v___y_4186_ = v___y_4212_;
v___y_4187_ = v___y_4220_;
v___y_4188_ = v_a_4228_;
v___y_4189_ = v___y_4215_;
v___y_4190_ = v___x_4277_;
goto v___jp_4154_;
}
}
else
{
size_t v___x_4278_; size_t v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = ((size_t)0ULL);
v___x_4279_ = lean_usize_of_nat(v___x_4271_);
v___x_4280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_4259_, v_mutVars_4266_, v___x_4278_, v___x_4279_, v___x_4272_);
lean_inc(v_a_4228_);
lean_inc(v_a_4230_);
lean_inc(v_a_4247_);
lean_inc(v_a_4255_);
lean_inc(v_a_4264_);
lean_inc(v_a_4237_);
v___y_4155_ = v_a_4237_;
v___y_4156_ = v_a_4264_;
v___y_4157_ = v___f_4267_;
v___y_4158_ = v___y_4208_;
v___y_4159_ = v_a_4255_;
v___y_4160_ = v_a_4247_;
v___y_4161_ = v___y_4207_;
v___y_4162_ = v_body_4257_;
v___y_4163_ = v_a_4261_;
v___y_4164_ = v___f_4268_;
v___y_4165_ = v_monadInfo_4265_;
v___y_4166_ = v_a_4230_;
v___y_4167_ = v___y_4209_;
v___y_4168_ = v_a_4228_;
v___y_4169_ = v___f_4270_;
v___y_4170_ = v_a_4223_;
v___y_4171_ = v_a_4237_;
v___y_4172_ = v_a_4264_;
v___y_4173_ = v___y_4211_;
v___y_4174_ = v___x_4234_;
v___y_4175_ = v_a_4255_;
v___y_4176_ = v_a_4247_;
v___y_4177_ = v___y_4216_;
v___y_4178_ = v___y_4218_;
v___y_4179_ = v___y_4221_;
v___y_4180_ = v_a_4259_;
v___y_4181_ = v___y_4217_;
v___y_4182_ = v___y_4210_;
v___y_4183_ = v_inv_x3f_4214_;
v___y_4184_ = v___y_4219_;
v___y_4185_ = v_a_4230_;
v___y_4186_ = v___y_4212_;
v___y_4187_ = v___y_4220_;
v___y_4188_ = v_a_4228_;
v___y_4189_ = v___y_4215_;
v___y_4190_ = v___x_4280_;
goto v___jp_4154_;
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_a_4261_);
lean_dec(v_a_4259_);
lean_dec(v_body_4257_);
lean_dec(v_a_4255_);
lean_dec(v_a_4247_);
lean_dec(v_a_4237_);
lean_dec(v_a_4230_);
lean_dec(v_a_4228_);
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
v_a_4281_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4263_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4263_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v_a_4259_);
lean_dec(v_body_4257_);
lean_dec(v_a_4255_);
lean_dec(v_a_4247_);
lean_dec(v_a_4237_);
lean_dec(v_a_4230_);
lean_dec(v_a_4228_);
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
v_a_4289_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4260_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4260_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
else
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4304_; 
lean_dec(v_body_4257_);
lean_dec(v_a_4255_);
lean_dec(v_a_4247_);
lean_dec(v_a_4237_);
lean_dec(v_a_4230_);
lean_dec(v_a_4228_);
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
v_a_4297_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4299_ = v___x_4258_;
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4258_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4304_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4302_; 
if (v_isShared_4300_ == 0)
{
v___x_4302_ = v___x_4299_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_a_4297_);
v___x_4302_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
return v___x_4302_;
}
}
}
}
else
{
lean_dec(v_a_4247_);
lean_dec(v_a_4237_);
lean_dec(v_a_4230_);
lean_dec(v_a_4228_);
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
lean_dec(v_stx_3836_);
return v___x_4254_;
}
}
}
}
else
{
lean_dec(v_a_4237_);
lean_dec(v_a_4230_);
lean_dec(v_a_4228_);
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
lean_dec(v_stx_3836_);
return v___x_4246_;
}
}
}
}
else
{
lean_dec(v_a_4230_);
lean_dec(v_a_4228_);
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
lean_dec(v_stx_3836_);
return v___x_4236_;
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec(v_a_4228_);
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
lean_dec(v_stx_3836_);
v_a_4309_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4229_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4229_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
lean_dec(v_stx_3836_);
v_a_4317_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4227_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4227_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4322_; 
if (v_isShared_4320_ == 0)
{
v___x_4322_ = v___x_4319_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4317_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec(v_a_4223_);
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
lean_dec(v_stx_3836_);
v_a_4325_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4226_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4226_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec(v_inv_x3f_4214_);
lean_dec(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec(v___y_4207_);
lean_dec(v_stx_3836_);
v_a_4333_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4222_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4222_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
v___jp_4341_:
{
lean_object* v_x_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v_x_4350_ = l_Lean_Syntax_getArg(v___x_3854_, v___x_3849_);
v___x_4351_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_x_4350_);
v___x_4352_ = l_Lean_Syntax_isOfKind(v_x_4350_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; 
lean_dec(v_x_4350_);
lean_dec(v_h_x3f_4342_);
lean_dec(v_tk_4205_);
lean_dec(v___x_3854_);
lean_dec_ref(v_dec_3837_);
lean_dec(v_stx_3836_);
v___x_4353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4353_;
}
else
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4354_ = lean_unsigned_to_nat(2u);
v___x_4355_ = lean_unsigned_to_nat(3u);
v___x_4356_ = l_Lean_Syntax_getArg(v___x_3854_, v___x_4355_);
lean_dec(v___x_3854_);
v___x_4357_ = l_Lean_Syntax_getArg(v_stx_3836_, v___x_4354_);
v___x_4358_ = l_Lean_Syntax_isNone(v___x_4357_);
if (v___x_4358_ == 0)
{
uint8_t v___x_4359_; 
lean_inc(v___x_4357_);
v___x_4359_ = l_Lean_Syntax_matchesNull(v___x_4357_, v___x_3849_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; 
lean_dec(v___x_4357_);
lean_dec(v___x_4356_);
lean_dec(v_x_4350_);
lean_dec(v_h_x3f_4342_);
lean_dec(v_tk_4205_);
lean_dec_ref(v_dec_3837_);
lean_dec(v_stx_3836_);
v___x_4360_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4360_;
}
else
{
lean_object* v_inv_x3f_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; 
v_inv_x3f_4361_ = l_Lean_Syntax_getArg(v___x_4357_, v___x_3853_);
lean_dec(v___x_4357_);
v___x_4362_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_x3f_4361_);
v___x_4363_ = l_Lean_Syntax_isOfKind(v_inv_x3f_4361_, v___x_4362_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; 
lean_dec(v_inv_x3f_4361_);
lean_dec(v___x_4356_);
lean_dec(v_x_4350_);
lean_dec(v_h_x3f_4342_);
lean_dec(v_tk_4205_);
lean_dec_ref(v_dec_3837_);
lean_dec(v_stx_3836_);
v___x_4364_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4364_;
}
else
{
lean_object* v___x_4365_; 
v___x_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4365_, 0, v_inv_x3f_4361_);
lean_inc(v_h_x3f_4342_);
lean_inc(v_x_4350_);
v___y_4207_ = v_x_4350_;
v___y_4208_ = v___x_4352_;
v___y_4209_ = v_h_x3f_4342_;
v___y_4210_ = v_x_4350_;
v___y_4211_ = v___x_4354_;
v___y_4212_ = v_h_x3f_4342_;
v___y_4213_ = v___x_4356_;
v_inv_x3f_4214_ = v___x_4365_;
v___y_4215_ = v___y_4343_;
v___y_4216_ = v___y_4344_;
v___y_4217_ = v___y_4345_;
v___y_4218_ = v___y_4346_;
v___y_4219_ = v___y_4347_;
v___y_4220_ = v___y_4348_;
v___y_4221_ = v___y_4349_;
goto v___jp_4206_;
}
}
}
else
{
lean_object* v___x_4366_; 
lean_dec(v___x_4357_);
v___x_4366_ = lean_box(0);
lean_inc(v_h_x3f_4342_);
lean_inc(v_x_4350_);
v___y_4207_ = v_x_4350_;
v___y_4208_ = v___x_4352_;
v___y_4209_ = v_h_x3f_4342_;
v___y_4210_ = v_x_4350_;
v___y_4211_ = v___x_4354_;
v___y_4212_ = v_h_x3f_4342_;
v___y_4213_ = v___x_4356_;
v_inv_x3f_4214_ = v___x_4366_;
v___y_4215_ = v___y_4343_;
v___y_4216_ = v___y_4344_;
v___y_4217_ = v___y_4345_;
v___y_4218_ = v___y_4346_;
v___y_4219_ = v___y_4347_;
v___y_4220_ = v___y_4348_;
v___y_4221_ = v___y_4349_;
goto v___jp_4206_;
}
}
}
}
v___jp_3857_:
{
lean_object* v_doBlockResultType_3877_; lean_object* v___x_3878_; lean_object* v___y_3879_; lean_object* v___x_3880_; lean_object* v___f_3881_; lean_object* v___x_3882_; 
v_doBlockResultType_3877_ = lean_ctor_get(v___y_3870_, 3);
v___x_3878_ = lean_box(v___y_3866_);
lean_inc(v___y_3864_);
lean_inc_ref(v_doBlockResultType_3877_);
v___y_3879_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 19, 11);
lean_closure_set(v___y_3879_, 0, v___x_3878_);
lean_closure_set(v___y_3879_, 1, v___y_3865_);
lean_closure_set(v___y_3879_, 2, v___y_3861_);
lean_closure_set(v___y_3879_, 3, v_doBlockResultType_3877_);
lean_closure_set(v___y_3879_, 4, v___y_3860_);
lean_closure_set(v___y_3879_, 5, v___y_3864_);
lean_closure_set(v___y_3879_, 6, v___y_3859_);
lean_closure_set(v___y_3879_, 7, v___y_3862_);
lean_closure_set(v___y_3879_, 8, v___y_3858_);
lean_closure_set(v___y_3879_, 9, v___x_3853_);
lean_closure_set(v___y_3879_, 10, v___x_3849_);
v___x_3880_ = lean_box(v___x_3856_);
v___f_3881_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 13, 4);
lean_closure_set(v___f_3881_, 0, v___y_3863_);
lean_closure_set(v___f_3881_, 1, v___y_3879_);
lean_closure_set(v___f_3881_, 2, v___x_3849_);
lean_closure_set(v___f_3881_, 3, v___x_3880_);
lean_inc_ref(v___y_3867_);
v___x_3882_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___y_3868_, v___y_3867_, v___f_3881_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3884_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3882_, 1);
lean_inc_ref(v_doBlockResultType_3877_);
v___x_3884_ = l_Lean_Elab_Do_mkBindApp(v___y_3867_, v_doBlockResultType_3877_, v_forIn_3869_, v_a_3883_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3884_;
}
else
{
lean_dec_ref(v_forIn_3869_);
lean_dec_ref(v___y_3867_);
return v___x_3882_;
}
}
v___jp_3885_:
{
lean_object* v___x_3912_; 
lean_inc_ref(v___y_3907_);
lean_inc_ref(v___y_3903_);
v___x_3912_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(v___y_3902_, v___y_3911_, v___y_3898_, v___y_3900_, v___y_3901_, v___y_3903_, v___y_3904_, v___y_3910_, v___y_3907_, v___y_3908_, v___y_3906_, v___y_3909_, v___y_3895_, v___y_3899_, v___y_3905_, v___y_3896_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3911_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___y_3858_ = v___y_3886_;
v___y_3859_ = v___y_3889_;
v___y_3860_ = v___y_3888_;
v___y_3861_ = v___y_3887_;
v___y_3862_ = v___y_3890_;
v___y_3863_ = v___y_3891_;
v___y_3864_ = v___y_3892_;
v___y_3865_ = v___y_3893_;
v___y_3866_ = v___y_3894_;
v___y_3867_ = v___y_3903_;
v___y_3868_ = v___y_3897_;
v_forIn_3869_ = v_a_3913_;
v___y_3870_ = v___y_3908_;
v___y_3871_ = v___y_3906_;
v___y_3872_ = v___y_3909_;
v___y_3873_ = v___y_3895_;
v___y_3874_ = v___y_3899_;
v___y_3875_ = v___y_3905_;
v___y_3876_ = v___y_3896_;
goto v___jp_3857_;
}
else
{
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
return v___x_3912_;
}
}
v___jp_3914_:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___f_3950_; uint8_t v___x_3951_; lean_object* v___x_3952_; 
v___x_3948_ = l_Lean_instInhabitedExpr;
v___x_3949_ = lean_box(v___x_3856_);
lean_inc(v___y_3917_);
lean_inc(v___y_3927_);
lean_inc(v___y_3916_);
lean_inc_ref(v___y_3929_);
lean_inc_ref(v___y_3922_);
v___f_3950_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 24, 15);
lean_closure_set(v___f_3950_, 0, v___x_3948_);
lean_closure_set(v___f_3950_, 1, v___x_3853_);
lean_closure_set(v___f_3950_, 2, v___y_3918_);
lean_closure_set(v___f_3950_, 3, v___y_3922_);
lean_closure_set(v___f_3950_, 4, v___y_3929_);
lean_closure_set(v___f_3950_, 5, v___y_3916_);
lean_closure_set(v___f_3950_, 6, v___y_3919_);
lean_closure_set(v___f_3950_, 7, v___y_3924_);
lean_closure_set(v___f_3950_, 8, v___y_3923_);
lean_closure_set(v___f_3950_, 9, v___y_3921_);
lean_closure_set(v___f_3950_, 10, v___x_3949_);
lean_closure_set(v___f_3950_, 11, v___y_3927_);
lean_closure_set(v___f_3950_, 12, v___y_3917_);
lean_closure_set(v___f_3950_, 13, v___y_3925_);
lean_closure_set(v___f_3950_, 14, v___x_3849_);
v___x_3951_ = 0;
v___x_3952_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_3947_, v___f_3950_, v___x_3951_, v___y_3943_, v___y_3941_, v___y_3945_, v___y_3931_, v___y_3935_, v___y_3940_, v___y_3933_);
if (lean_obj_tag(v___x_3952_) == 0)
{
if (lean_obj_tag(v___y_3938_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3954_; 
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3939_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v___y_3934_);
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3954_ = l_Lean_Expr_app___override(v___y_3932_, v_a_3953_);
v___y_3858_ = v___y_3920_;
v___y_3859_ = v___y_3916_;
v___y_3860_ = v___y_3922_;
v___y_3861_ = v___y_3915_;
v___y_3862_ = v___y_3926_;
v___y_3863_ = v___y_3927_;
v___y_3864_ = v___y_3928_;
v___y_3865_ = v___y_3929_;
v___y_3866_ = v___y_3930_;
v___y_3867_ = v___y_3937_;
v___y_3868_ = v___y_3917_;
v_forIn_3869_ = v___x_3954_;
v___y_3870_ = v___y_3943_;
v___y_3871_ = v___y_3941_;
v___y_3872_ = v___y_3945_;
v___y_3873_ = v___y_3931_;
v___y_3874_ = v___y_3935_;
v___y_3875_ = v___y_3940_;
v___y_3876_ = v___y_3933_;
goto v___jp_3857_;
}
else
{
lean_dec_ref(v___y_3932_);
if (lean_obj_tag(v___y_3944_) == 0)
{
lean_object* v_a_3955_; lean_object* v_val_3956_; lean_object* v___x_3957_; 
v_a_3955_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3952_, 1);
v_val_3956_ = lean_ctor_get(v___y_3938_, 0);
lean_inc(v_val_3956_);
lean_dec_ref_known(v___y_3938_, 1);
v___x_3957_ = lean_box(0);
v___y_3886_ = v___y_3920_;
v___y_3887_ = v___y_3915_;
v___y_3888_ = v___y_3922_;
v___y_3889_ = v___y_3916_;
v___y_3890_ = v___y_3926_;
v___y_3891_ = v___y_3927_;
v___y_3892_ = v___y_3928_;
v___y_3893_ = v___y_3929_;
v___y_3894_ = v___y_3930_;
v___y_3895_ = v___y_3931_;
v___y_3896_ = v___y_3933_;
v___y_3897_ = v___y_3917_;
v___y_3898_ = v___y_3934_;
v___y_3899_ = v___y_3935_;
v___y_3900_ = v___y_3936_;
v___y_3901_ = v_a_3955_;
v___y_3902_ = v_val_3956_;
v___y_3903_ = v___y_3937_;
v___y_3904_ = v___y_3939_;
v___y_3905_ = v___y_3940_;
v___y_3906_ = v___y_3941_;
v___y_3907_ = v___y_3942_;
v___y_3908_ = v___y_3943_;
v___y_3909_ = v___y_3945_;
v___y_3910_ = v___y_3946_;
v___y_3911_ = v___x_3957_;
goto v___jp_3885_;
}
else
{
lean_object* v_a_3958_; lean_object* v_val_3959_; lean_object* v_val_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
v_a_3958_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3952_, 1);
v_val_3959_ = lean_ctor_get(v___y_3938_, 0);
lean_inc(v_val_3959_);
lean_dec_ref_known(v___y_3938_, 1);
v_val_3960_ = lean_ctor_get(v___y_3944_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___y_3944_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___y_3944_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_val_3960_);
lean_dec(v___y_3944_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_val_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
v___y_3886_ = v___y_3920_;
v___y_3887_ = v___y_3915_;
v___y_3888_ = v___y_3922_;
v___y_3889_ = v___y_3916_;
v___y_3890_ = v___y_3926_;
v___y_3891_ = v___y_3927_;
v___y_3892_ = v___y_3928_;
v___y_3893_ = v___y_3929_;
v___y_3894_ = v___y_3930_;
v___y_3895_ = v___y_3931_;
v___y_3896_ = v___y_3933_;
v___y_3897_ = v___y_3917_;
v___y_3898_ = v___y_3934_;
v___y_3899_ = v___y_3935_;
v___y_3900_ = v___y_3936_;
v___y_3901_ = v_a_3958_;
v___y_3902_ = v_val_3959_;
v___y_3903_ = v___y_3937_;
v___y_3904_ = v___y_3939_;
v___y_3905_ = v___y_3940_;
v___y_3906_ = v___y_3941_;
v___y_3907_ = v___y_3942_;
v___y_3908_ = v___y_3943_;
v___y_3909_ = v___y_3945_;
v___y_3910_ = v___y_3946_;
v___y_3911_ = v___x_3965_;
goto v___jp_3885_;
}
}
}
}
}
else
{
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v___y_3934_);
lean_dec_ref(v___y_3932_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec_ref(v___y_3922_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec(v___y_3915_);
return v___x_3952_;
}
}
v___jp_3968_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_4010_ = l_Lean_Core_mkFreshUserName(v___x_4009_, v___y_4007_, v___y_4008_);
if (lean_obj_tag(v___x_4010_) == 0)
{
if (lean_obj_tag(v___y_3998_) == 1)
{
if (lean_obj_tag(v_snd_4001_) == 1)
{
lean_object* v_a_4011_; lean_object* v_val_4012_; lean_object* v_val_4013_; lean_object* v___f_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
lean_dec_ref(v___y_3995_);
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v_val_4012_ = lean_ctor_get(v___y_3998_, 0);
v_val_4013_ = lean_ctor_get(v_snd_4001_, 0);
lean_inc(v_val_4013_);
lean_dec_ref_known(v_snd_4001_, 1);
v___f_4014_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_4014_, 0, v___y_3980_);
lean_closure_set(v___f_4014_, 1, v___y_3984_);
lean_closure_set(v___f_4014_, 2, v___x_3853_);
lean_closure_set(v___f_4014_, 3, v___y_3969_);
lean_closure_set(v___f_4014_, 4, v___y_3973_);
lean_closure_set(v___f_4014_, 5, v_val_4013_);
lean_closure_set(v___f_4014_, 6, v___y_3972_);
v___x_4015_ = l_Lean_TSyntax_getId(v___y_3990_);
lean_dec(v___y_3990_);
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
lean_ctor_set(v___x_4016_, 1, v___y_3994_);
v___x_4017_ = l_Lean_TSyntax_getId(v_val_4012_);
v___x_4018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
lean_ctor_set(v___x_4018_, 1, v___f_4014_);
v___x_4019_ = lean_mk_empty_array_with_capacity(v___y_3993_);
v___x_4020_ = lean_array_push(v___x_4019_, v___x_4016_);
v___x_4021_ = lean_array_push(v___x_4020_, v___x_4018_);
lean_inc_ref(v___y_3976_);
v___y_3915_ = v___y_3970_;
v___y_3916_ = v___y_3971_;
v___y_3917_ = v_a_4011_;
v___y_3918_ = v___y_3975_;
v___y_3919_ = v___y_3976_;
v___y_3920_ = v___y_3977_;
v___y_3921_ = v___y_3978_;
v___y_3922_ = v___y_3979_;
v___y_3923_ = v___y_3981_;
v___y_3924_ = v___y_3982_;
v___y_3925_ = v___y_3983_;
v___y_3926_ = v___y_3985_;
v___y_3927_ = v___y_3986_;
v___y_3928_ = v___y_3987_;
v___y_3929_ = v___y_3988_;
v___y_3930_ = v___y_3989_;
v___y_3931_ = v___y_4005_;
v___y_3932_ = v_fst_4000_;
v___y_3933_ = v___y_4008_;
v___y_3934_ = v___y_3997_;
v___y_3935_ = v___y_4006_;
v___y_3936_ = v___y_3974_;
v___y_3937_ = v___y_3976_;
v___y_3938_ = v___y_3991_;
v___y_3939_ = v___y_3992_;
v___y_3940_ = v___y_4007_;
v___y_3941_ = v___y_4003_;
v___y_3942_ = v___y_3996_;
v___y_3943_ = v___y_4002_;
v___y_3944_ = v___y_3998_;
v___y_3945_ = v___y_4004_;
v___y_3946_ = v___y_3999_;
v___y_3947_ = v___x_4021_;
goto v___jp_3914_;
}
else
{
lean_object* v_a_4022_; lean_object* v___x_4023_; 
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3990_);
lean_dec(v___y_3984_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec_ref(v___y_3969_);
v_a_4022_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4010_, 1);
lean_inc_ref(v___y_3998_);
v___x_4023_ = lean_apply_2(v___y_3995_, v___y_3998_, v_snd_4001_);
lean_inc_ref(v___y_3976_);
v___y_3915_ = v___y_3970_;
v___y_3916_ = v___y_3971_;
v___y_3917_ = v_a_4022_;
v___y_3918_ = v___y_3975_;
v___y_3919_ = v___y_3976_;
v___y_3920_ = v___y_3977_;
v___y_3921_ = v___y_3978_;
v___y_3922_ = v___y_3979_;
v___y_3923_ = v___y_3981_;
v___y_3924_ = v___y_3982_;
v___y_3925_ = v___y_3983_;
v___y_3926_ = v___y_3985_;
v___y_3927_ = v___y_3986_;
v___y_3928_ = v___y_3987_;
v___y_3929_ = v___y_3988_;
v___y_3930_ = v___y_3989_;
v___y_3931_ = v___y_4005_;
v___y_3932_ = v_fst_4000_;
v___y_3933_ = v___y_4008_;
v___y_3934_ = v___y_3997_;
v___y_3935_ = v___y_4006_;
v___y_3936_ = v___y_3974_;
v___y_3937_ = v___y_3976_;
v___y_3938_ = v___y_3991_;
v___y_3939_ = v___y_3992_;
v___y_3940_ = v___y_4007_;
v___y_3941_ = v___y_4003_;
v___y_3942_ = v___y_3996_;
v___y_3943_ = v___y_4002_;
v___y_3944_ = v___y_3998_;
v___y_3945_ = v___y_4004_;
v___y_3946_ = v___y_3999_;
v___y_3947_ = v___x_4023_;
goto v___jp_3914_;
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4025_; 
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3990_);
lean_dec(v___y_3984_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec_ref(v___y_3969_);
v_a_4024_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4010_, 1);
lean_inc(v___y_3998_);
v___x_4025_ = lean_apply_2(v___y_3995_, v___y_3998_, v_snd_4001_);
lean_inc_ref(v___y_3976_);
v___y_3915_ = v___y_3970_;
v___y_3916_ = v___y_3971_;
v___y_3917_ = v_a_4024_;
v___y_3918_ = v___y_3975_;
v___y_3919_ = v___y_3976_;
v___y_3920_ = v___y_3977_;
v___y_3921_ = v___y_3978_;
v___y_3922_ = v___y_3979_;
v___y_3923_ = v___y_3981_;
v___y_3924_ = v___y_3982_;
v___y_3925_ = v___y_3983_;
v___y_3926_ = v___y_3985_;
v___y_3927_ = v___y_3986_;
v___y_3928_ = v___y_3987_;
v___y_3929_ = v___y_3988_;
v___y_3930_ = v___y_3989_;
v___y_3931_ = v___y_4005_;
v___y_3932_ = v_fst_4000_;
v___y_3933_ = v___y_4008_;
v___y_3934_ = v___y_3997_;
v___y_3935_ = v___y_4006_;
v___y_3936_ = v___y_3974_;
v___y_3937_ = v___y_3976_;
v___y_3938_ = v___y_3991_;
v___y_3939_ = v___y_3992_;
v___y_3940_ = v___y_4007_;
v___y_3941_ = v___y_4003_;
v___y_3942_ = v___y_3996_;
v___y_3943_ = v___y_4002_;
v___y_3944_ = v___y_3998_;
v___y_3945_ = v___y_4004_;
v___y_3946_ = v___y_3999_;
v___y_3947_ = v___x_4025_;
goto v___jp_3914_;
}
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec(v_snd_4001_);
lean_dec_ref(v_fst_4000_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec_ref(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
v_a_4026_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_4010_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_4010_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
v___jp_4034_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = lean_box(0);
lean_inc_ref(v___y_4045_);
lean_inc(v___y_4058_);
lean_inc_ref(v___y_4068_);
lean_inc(v___y_4063_);
lean_inc_ref(v___y_4057_);
lean_inc(v___y_4059_);
lean_inc_ref(v___y_4056_);
v___x_4073_ = lean_apply_8(v___y_4045_, v___x_4072_, v___y_4056_, v___y_4059_, v___y_4057_, v___y_4063_, v___y_4068_, v___y_4058_, lean_box(0));
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v_m_4075_; lean_object* v_u_4076_; lean_object* v_v_4077_; lean_object* v___x_4078_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
v_m_4075_ = lean_ctor_get(v___y_4066_, 0);
v_u_4076_ = lean_ctor_get(v___y_4066_, 1);
v_v_4077_ = lean_ctor_get(v___y_4066_, 2);
lean_inc(v_u_4076_);
v___x_4078_ = l_Lean_Meta_mkProdMkN(v_a_4074_, v_u_4076_, v___y_4057_, v___y_4063_, v___y_4068_, v___y_4058_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___x_4078_, 1);
if (lean_obj_tag(v___y_4067_) == 0)
{
lean_object* v_fst_4080_; lean_object* v_snd_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4100_; 
v_fst_4080_ = lean_ctor_get(v_a_4079_, 0);
v_snd_4081_ = lean_ctor_get(v_a_4079_, 1);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_a_4079_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4083_ = v_a_4079_;
v_isShared_4084_ = v_isSharedCheck_4100_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_snd_4081_);
lean_inc(v_fst_4080_);
lean_dec(v_a_4079_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4100_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4085_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__0));
v___x_4086_ = lean_box(0);
lean_inc(v_v_4077_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set_tag(v___x_4083_, 1);
lean_ctor_set(v___x_4083_, 1, v___x_4086_);
lean_ctor_set(v___x_4083_, 0, v_v_4077_);
v___x_4088_ = v___x_4083_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_v_4077_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
lean_inc(v_u_4076_);
v___x_4089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4089_, 0, v_u_4076_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___y_4069_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___y_4064_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
lean_inc_ref(v___x_4091_);
v___x_4092_ = l_Lean_mkConst(v___x_4085_, v___x_4091_);
lean_inc_ref(v___y_4050_);
lean_inc_ref(v___y_4055_);
lean_inc_ref(v_m_4075_);
v___x_4093_ = l_Lean_mkApp3(v___x_4092_, v_m_4075_, v___y_4055_, v___y_4050_);
v___x_4094_ = l_Lean_Elab_Term_mkInstMVar(v___x_4093_, v___x_4072_, v___y_4056_, v___y_4059_, v___y_4057_, v___y_4063_, v___y_4068_, v___y_4058_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v___x_4096_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__2));
v___x_4097_ = l_Lean_mkConst(v___x_4096_, v___x_4091_);
lean_inc(v_fst_4080_);
lean_inc_ref(v___y_4054_);
lean_inc(v_snd_4081_);
lean_inc_ref(v_m_4075_);
v___x_4098_ = l_Lean_mkApp7(v___x_4097_, v_m_4075_, v___y_4055_, v___y_4050_, v_a_4095_, v_snd_4081_, v___y_4054_, v_fst_4080_);
lean_inc(v_u_4076_);
v___y_3969_ = v___y_4035_;
v___y_3970_ = v___y_4036_;
v___y_3971_ = v_u_4076_;
v___y_3972_ = v___y_4037_;
v___y_3973_ = v___y_4038_;
v___y_3974_ = v_fst_4080_;
v___y_3975_ = v___y_4039_;
v___y_3976_ = v_snd_4081_;
v___y_3977_ = v___y_4040_;
v___y_3978_ = v___y_4041_;
v___y_3979_ = v___y_4042_;
v___y_3980_ = v___y_4043_;
v___y_3981_ = v___x_4072_;
v___y_3982_ = v___y_4045_;
v___y_3983_ = v___y_4044_;
v___y_3984_ = v___y_4046_;
v___y_3985_ = v___y_4047_;
v___y_3986_ = v___y_4071_;
v___y_3987_ = v_v_4077_;
v___y_3988_ = v___y_4048_;
v___y_3989_ = v___y_4049_;
v___y_3990_ = v___y_4060_;
v___y_3991_ = v___y_4061_;
v___y_3992_ = v___y_4062_;
v___y_3993_ = v___y_4051_;
v___y_3994_ = v___y_4053_;
v___y_3995_ = v___y_4065_;
v___y_3996_ = v___y_4066_;
v___y_3997_ = v___y_4054_;
v___y_3998_ = v___y_4067_;
v___y_3999_ = v___y_4049_;
v_fst_4000_ = v___x_4098_;
v_snd_4001_ = v___x_4072_;
v___y_4002_ = v___y_4070_;
v___y_4003_ = v___y_4056_;
v___y_4004_ = v___y_4059_;
v___y_4005_ = v___y_4057_;
v___y_4006_ = v___y_4063_;
v___y_4007_ = v___y_4068_;
v___y_4008_ = v___y_4058_;
goto v___jp_3968_;
}
else
{
lean_dec_ref_known(v___x_4091_, 2);
lean_dec(v_snd_4081_);
lean_dec(v_fst_4080_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4065_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
return v___x_4094_;
}
}
}
}
else
{
lean_object* v_fst_4101_; lean_object* v_snd_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4137_; 
v_fst_4101_ = lean_ctor_get(v_a_4079_, 0);
v_snd_4102_ = lean_ctor_get(v_a_4079_, 1);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_a_4079_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4104_ = v_a_4079_;
v_isShared_4105_ = v_isSharedCheck_4137_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_snd_4102_);
lean_inc(v_fst_4101_);
lean_dec(v_a_4079_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4137_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_4107_ = lean_box(0);
lean_inc(v___y_4064_);
if (v_isShared_4105_ == 0)
{
lean_ctor_set_tag(v___x_4104_, 1);
lean_ctor_set(v___x_4104_, 1, v___x_4107_);
lean_ctor_set(v___x_4104_, 0, v___y_4064_);
v___x_4109_ = v___x_4104_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___y_4064_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_inc(v___y_4069_);
v___x_4110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___y_4069_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Lean_mkConst(v___x_4106_, v___x_4110_);
lean_inc_ref(v___y_4055_);
lean_inc_ref(v___y_4050_);
v___x_4112_ = l_Lean_mkAppB(v___x_4111_, v___y_4050_, v___y_4055_);
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
v___x_4114_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__5));
v___x_4115_ = l_Lean_Meta_mkFreshExprMVar(v___x_4113_, v___y_4052_, v___x_4114_, v___y_4057_, v___y_4063_, v___y_4068_, v___y_4058_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc_n(v_a_4116_, 2);
lean_dec_ref_known(v___x_4115_, 1);
v___x_4117_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
lean_inc(v_v_4077_);
v___x_4118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4118_, 0, v_v_4077_);
lean_ctor_set(v___x_4118_, 1, v___x_4107_);
lean_inc(v_u_4076_);
v___x_4119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4119_, 0, v_u_4076_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___y_4069_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___y_4064_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
lean_inc_ref(v___x_4121_);
v___x_4122_ = l_Lean_mkConst(v___x_4117_, v___x_4121_);
lean_inc_ref(v___y_4050_);
lean_inc_ref(v___y_4055_);
lean_inc_ref(v_m_4075_);
v___x_4123_ = l_Lean_mkApp4(v___x_4122_, v_m_4075_, v___y_4055_, v___y_4050_, v_a_4116_);
v___x_4124_ = l_Lean_Elab_Term_mkInstMVar(v___x_4123_, v___x_4072_, v___y_4056_, v___y_4059_, v___y_4057_, v___y_4063_, v___y_4068_, v___y_4058_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4135_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4127_ = v___x_4124_;
v_isShared_4128_ = v_isSharedCheck_4135_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4124_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4135_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___x_4129_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
v___x_4130_ = l_Lean_mkConst(v___x_4129_, v___x_4121_);
lean_inc(v_fst_4101_);
lean_inc_ref(v___y_4054_);
lean_inc(v_snd_4102_);
lean_inc(v_a_4116_);
lean_inc_ref(v_m_4075_);
v___x_4131_ = l_Lean_mkApp8(v___x_4130_, v_m_4075_, v___y_4055_, v___y_4050_, v_a_4116_, v_a_4125_, v_snd_4102_, v___y_4054_, v_fst_4101_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set_tag(v___x_4127_, 1);
lean_ctor_set(v___x_4127_, 0, v_a_4116_);
v___x_4133_ = v___x_4127_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4116_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
lean_inc(v_u_4076_);
v___y_3969_ = v___y_4035_;
v___y_3970_ = v___y_4036_;
v___y_3971_ = v_u_4076_;
v___y_3972_ = v___y_4037_;
v___y_3973_ = v___y_4038_;
v___y_3974_ = v_fst_4101_;
v___y_3975_ = v___y_4039_;
v___y_3976_ = v_snd_4102_;
v___y_3977_ = v___y_4040_;
v___y_3978_ = v___y_4041_;
v___y_3979_ = v___y_4042_;
v___y_3980_ = v___y_4043_;
v___y_3981_ = v___x_4072_;
v___y_3982_ = v___y_4045_;
v___y_3983_ = v___y_4044_;
v___y_3984_ = v___y_4046_;
v___y_3985_ = v___y_4047_;
v___y_3986_ = v___y_4071_;
v___y_3987_ = v_v_4077_;
v___y_3988_ = v___y_4048_;
v___y_3989_ = v___y_4049_;
v___y_3990_ = v___y_4060_;
v___y_3991_ = v___y_4061_;
v___y_3992_ = v___y_4062_;
v___y_3993_ = v___y_4051_;
v___y_3994_ = v___y_4053_;
v___y_3995_ = v___y_4065_;
v___y_3996_ = v___y_4066_;
v___y_3997_ = v___y_4054_;
v___y_3998_ = v___y_4067_;
v___y_3999_ = v___y_4049_;
v_fst_4000_ = v___x_4131_;
v_snd_4001_ = v___x_4133_;
v___y_4002_ = v___y_4070_;
v___y_4003_ = v___y_4056_;
v___y_4004_ = v___y_4059_;
v___y_4005_ = v___y_4057_;
v___y_4006_ = v___y_4063_;
v___y_4007_ = v___y_4068_;
v___y_4008_ = v___y_4058_;
goto v___jp_3968_;
}
}
}
else
{
lean_dec_ref_known(v___x_4121_, 2);
lean_dec(v_a_4116_);
lean_dec(v_snd_4102_);
lean_dec_ref_known(v___y_4067_, 1);
lean_dec(v_fst_4101_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4065_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
return v___x_4124_;
}
}
else
{
lean_dec(v_snd_4102_);
lean_dec_ref_known(v___y_4067_, 1);
lean_dec(v_fst_4101_);
lean_dec(v___y_4071_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
return v___x_4115_;
}
}
}
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec(v___y_4071_);
lean_dec(v___y_4069_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
v_a_4138_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4078_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4078_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec(v___y_4071_);
lean_dec(v___y_4069_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
v_a_4146_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4073_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4073_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
v___jp_4154_:
{
uint8_t v_returnsEarly_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___f_4194_; 
v_returnsEarly_4191_ = lean_ctor_get_uint8(v___y_4180_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_4180_);
v___x_4192_ = lean_box(v_returnsEarly_4191_);
v___x_4193_ = lean_box(v___y_4158_);
lean_inc_ref(v___y_4163_);
lean_inc_ref(v___y_4165_);
lean_inc_ref(v___y_4190_);
v___f_4194_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 14, 6);
lean_closure_set(v___f_4194_, 0, v___y_4190_);
lean_closure_set(v___f_4194_, 1, v___y_4165_);
lean_closure_set(v___f_4194_, 2, v___x_4192_);
lean_closure_set(v___f_4194_, 3, v___x_3853_);
lean_closure_set(v___f_4194_, 4, v___y_4163_);
lean_closure_set(v___f_4194_, 5, v___x_4193_);
if (v_returnsEarly_4191_ == 0)
{
size_t v_sz_4195_; size_t v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
lean_dec(v___y_4172_);
v_sz_4195_ = lean_array_size(v___y_4190_);
v___x_4196_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_4190_, 2);
v___x_4197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_4195_, v___x_4196_, v___y_4190_);
v___x_4198_ = lean_array_to_list(v___x_4197_);
v___y_4035_ = v___y_4155_;
v___y_4036_ = v___y_4156_;
v___y_4037_ = v___y_4159_;
v___y_4038_ = v___y_4160_;
v___y_4039_ = v___y_4161_;
v___y_4040_ = v___y_4190_;
v___y_4041_ = v___y_4162_;
v___y_4042_ = v___y_4163_;
v___y_4043_ = v___y_4166_;
v___y_4044_ = v___y_4167_;
v___y_4045_ = v___f_4194_;
v___y_4046_ = v___y_4168_;
v___y_4047_ = v___y_4169_;
v___y_4048_ = v___y_4170_;
v___y_4049_ = v_returnsEarly_4191_;
v___y_4050_ = v___y_4171_;
v___y_4051_ = v___y_4173_;
v___y_4052_ = v___y_4174_;
v___y_4053_ = v___y_4157_;
v___y_4054_ = v___y_4175_;
v___y_4055_ = v___y_4176_;
v___y_4056_ = v___y_4177_;
v___y_4057_ = v___y_4178_;
v___y_4058_ = v___y_4179_;
v___y_4059_ = v___y_4181_;
v___y_4060_ = v___y_4182_;
v___y_4061_ = v___y_4183_;
v___y_4062_ = v___y_4190_;
v___y_4063_ = v___y_4184_;
v___y_4064_ = v___y_4185_;
v___y_4065_ = v___y_4164_;
v___y_4066_ = v___y_4165_;
v___y_4067_ = v___y_4186_;
v___y_4068_ = v___y_4187_;
v___y_4069_ = v___y_4188_;
v___y_4070_ = v___y_4189_;
v___y_4071_ = v___x_4198_;
goto v___jp_4034_;
}
else
{
size_t v_sz_4199_; size_t v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_sz_4199_ = lean_array_size(v___y_4190_);
v___x_4200_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_4190_, 2);
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_4199_, v___x_4200_, v___y_4190_);
v___x_4202_ = lean_array_to_list(v___x_4201_);
v___x_4203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___y_4172_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___y_4035_ = v___y_4155_;
v___y_4036_ = v___y_4156_;
v___y_4037_ = v___y_4159_;
v___y_4038_ = v___y_4160_;
v___y_4039_ = v___y_4161_;
v___y_4040_ = v___y_4190_;
v___y_4041_ = v___y_4162_;
v___y_4042_ = v___y_4163_;
v___y_4043_ = v___y_4166_;
v___y_4044_ = v___y_4167_;
v___y_4045_ = v___f_4194_;
v___y_4046_ = v___y_4168_;
v___y_4047_ = v___y_4169_;
v___y_4048_ = v___y_4170_;
v___y_4049_ = v_returnsEarly_4191_;
v___y_4050_ = v___y_4171_;
v___y_4051_ = v___y_4173_;
v___y_4052_ = v___y_4174_;
v___y_4053_ = v___y_4157_;
v___y_4054_ = v___y_4175_;
v___y_4055_ = v___y_4176_;
v___y_4056_ = v___y_4177_;
v___y_4057_ = v___y_4178_;
v___y_4058_ = v___y_4179_;
v___y_4059_ = v___y_4181_;
v___y_4060_ = v___y_4182_;
v___y_4061_ = v___y_4183_;
v___y_4062_ = v___y_4190_;
v___y_4063_ = v___y_4184_;
v___y_4064_ = v___y_4185_;
v___y_4065_ = v___y_4164_;
v___y_4066_ = v___y_4165_;
v___y_4067_ = v___y_4186_;
v___y_4068_ = v___y_4187_;
v___y_4069_ = v___y_4188_;
v___y_4070_ = v___y_4189_;
v___y_4071_ = v___x_4203_;
goto v___jp_4034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_4375_, lean_object* v_dec_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Lean_Elab_Do_elabDoFor(v_stx_4375_, v_dec_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_);
lean_dec(v_a_4383_);
lean_dec_ref(v_a_4382_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4380_);
lean_dec(v_a_4379_);
lean_dec_ref(v_a_4378_);
lean_dec_ref(v_a_4377_);
return v_res_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v_00_u03b1_4386_, lean_object* v_msg_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v_00_u03b1_4396_, lean_object* v_msg_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(v_00_u03b1_4396_, v_msg_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_4406_, lean_object* v_name_4407_, lean_object* v_type_4408_, lean_object* v_k_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_4407_, v_type_4408_, v_k_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_4419_, lean_object* v_name_4420_, lean_object* v_type_4421_, lean_object* v_k_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_4419_, v_name_4420_, v_type_4421_, v_k_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec_ref(v___y_4423_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(lean_object* v_msgData_4432_, lean_object* v_macroStack_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_4432_, v_macroStack_4433_, v___y_4438_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___boxed(lean_object* v_msgData_4442_, lean_object* v_macroStack_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(v_msgData_4442_, v_macroStack_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4459_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4460_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_4461_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_4462_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_4463_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4459_, v___x_4460_, v___x_4461_, v___x_4462_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_4465_;
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
