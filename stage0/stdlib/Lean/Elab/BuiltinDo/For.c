// Lean compiler output
// Module: Lean.Elab.BuiltinDo.For
// Imports: public import Lean.Elab.BuiltinDo.Basic meta import Lean.Parser.Do meta import Std.WP.Gadget.ForIn import Init.Control.Do import Init.Data.Sum.Basic import Init.While import Lean.Meta.ProdN
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Do_MutVar_getId(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallArity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkBindApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value;
static const lean_array_object l_Lean_Elab_Do_expandDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
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
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "The `invariant` clause takes a `for` loop over a single collection."};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doLoopDecreasing"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value),LEAN_SCALAR_PTR_LITERAL(0, 112, 64, 8, 91, 183, 41, 148)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__17 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doLoopInvariant"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__18 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 155, 107, 150, 202, 64, 185, 181)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__19 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__20 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__20_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__21 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expandDoFor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 157, 21, 52, 135, 185, 36, 254)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 129, .m_capacity = 129, .m_length = 128, .m_data = "The `invariant` clause is stated over this class, which says that iterating the container produces its elements without effects."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PureForIn"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(147, 246, 122, 181, 55, 202, 108, 55)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "PureForIn'"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 225, 86, 37, 42, 243, 162, 173)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "WPMonad"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(202, 83, 143, 139, 231, 107, 0, 192)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__3;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "The "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " of a loop in this monad takes "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ", and this clause has "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = ". The loop's mutable variables are named without binding them."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " binders"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "one binder"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " arguments"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "one argument"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__3;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(86, 142, 99, 99, 156, 120, 56, 132)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__8;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(209, 212, 202, 104, 137, 8, 49, 108)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "a loop annotation elaborates to a `vcgen` gadget; add `import Std.WP` to use it."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 164, .m_capacity = 164, .m_length = 162, .m_data = "The `invariant` clause takes no type ascription covering all its binders; ascribe the type on an individual binder, as in `invariant (pref : List α) suff => ...`."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "invariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Gadget"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "forInPureWithInvariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(183, 165, 133, 99, 223, 97, 236, 183)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "forInPureWithInvariant'"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__4_value),LEAN_SCALAR_PTR_LITERAL(107, 130, 88, 65, 130, 23, 203, 175)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "The `invariant` clause takes at least two binders: the elements consumed so far and the elements remaining."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "measure"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "RepeatInvariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 107, 113, 125, 115, 103, 32, 219)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(188, 118, 211, 95, 195, 159, 204, 32)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "forInLoopWithVariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 161, 208, 243, 4, 56, 187, 242)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "forInLoopWithInvariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__2_value),LEAN_SCALAR_PTR_LITERAL(86, 62, 119, 157, 208, 178, 34, 119)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "forInLoopWithInvariantAndVariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__4_value),LEAN_SCALAR_PTR_LITERAL(100, 75, 86, 181, 82, 124, 122, 58)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__c"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__6_value),LEAN_SCALAR_PTR_LITERAL(112, 73, 1, 111, 65, 2, 155, 239)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__7_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sum"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isRight"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__9_value),LEAN_SCALAR_PTR_LITERAL(246, 115, 20, 157, 28, 185, 140, 7)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Loop"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 180, 170, 243, 159, 48, 205, 98)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "A `for` loop terminates with the collection it iterates; `decreasing` states the termination measure of a `repeat` or `while` loop."};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___closed__3;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ForIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "forIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 12, 142, 239, 44, 138, 10, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 234, 148, 175, 115, 149, 2, 231)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ForIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value),LEAN_SCALAR_PTR_LITERAL(10, 254, 232, 131, 195, 189, 138, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "ρ"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__17_value),LEAN_SCALAR_PTR_LITERAL(148, 87, 172, 24, 54, 35, 28, 246)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__19_value),LEAN_SCALAR_PTR_LITERAL(38, 26, 183, 93, 43, 136, 227, 87)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__20_value;
static const lean_array_object l_Lean_Elab_Do_elabDoFor___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__21_value;
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
uint8_t v___x_203177__boxed_428_; lean_object* v_res_429_; 
v___x_203177__boxed_428_ = lean_unbox(v___x_416_);
v_res_429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_413_, v___x_414_, v___x_415_, v___x_203177__boxed_428_, v___x_417_, v___x_418_, v___x_419_, v___f_420_, v_fst_421_, v___x_422_, v_snd_423_, v_x_424_, v_h_x3f_425_, v___y_426_, v___y_427_);
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
uint8_t v___x_203783__boxed_440_; lean_object* v_res_441_; 
v___x_203783__boxed_440_ = lean_unbox(v___x_436_);
v_res_441_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(v___x_203783__boxed_440_, v_____do__lift_437_, v___y_438_, v___y_439_);
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
uint8_t v___x_203819__boxed_559_; lean_object* v_res_560_; 
v___x_203819__boxed_559_ = lean_unbox(v___x_554_);
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_203819__boxed_559_, v_a_555_, v_b_556_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v___x_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v___f_567_, lean_object* v_fst_568_, lean_object* v___x_569_, lean_object* v_snd_570_, lean_object* v_x_571_, lean_object* v_h_x3f_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___y_578_; 
v___x_575_ = l_Lean_Syntax_getArg(v___x_561_, v___x_562_);
v___x_576_ = l_Lean_Syntax_getArg(v___x_561_, v___x_563_);
if (lean_obj_tag(v_h_x3f_572_) == 1)
{
lean_object* v_val_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_val_797_ = lean_ctor_get(v_h_x3f_572_, 0);
v___x_798_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77));
v___x_799_ = l_Lean_Macro_throwErrorAt___redArg(v_val_797_, v___x_798_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; 
v_a_800_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 2);
v___y_578_ = v_a_800_;
goto v___jp_577_;
}
else
{
lean_object* v_a_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v___x_576_);
lean_dec(v___x_575_);
lean_dec(v_snd_570_);
lean_dec_ref(v___x_569_);
lean_dec(v_fst_568_);
lean_dec_ref(v___f_567_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_564_);
v_a_801_ = lean_ctor_get(v___x_799_, 0);
v_a_802_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_799_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_inc(v_a_801_);
lean_dec(v___x_799_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
v___y_578_ = v___y_574_;
goto v___jp_577_;
}
v___jp_577_:
{
lean_object* v_quotContext_579_; lean_object* v_currMacroScope_580_; lean_object* v_ref_581_; lean_object* v_ref_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_macroScope_605_; lean_object* v_traceMsgs_606_; lean_object* v_expandedMacroDecls_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_796_; 
v_quotContext_579_ = lean_ctor_get(v___y_573_, 1);
v_currMacroScope_580_ = lean_ctor_get(v___y_573_, 2);
v_ref_581_ = lean_ctor_get(v___y_573_, 5);
v_ref_582_ = l_Lean_replaceRef(v___x_576_, v_ref_581_);
v___x_583_ = 0;
v___x_584_ = l_Lean_SourceInfo_fromRef(v_ref_582_, v___x_583_);
lean_dec(v_ref_582_);
v___x_585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
lean_inc_ref_n(v___x_566_, 3);
lean_inc_ref_n(v___x_565_, 3);
lean_inc_ref_n(v___x_564_, 3);
v___x_586_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_585_);
v___x_587_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1));
v___x_588_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_587_);
v___x_589_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2));
lean_inc_n(v___x_584_, 6);
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_584_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
v___x_592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_580_);
lean_inc(v_quotContext_579_);
v___x_593_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_592_, v_currMacroScope_580_);
v___x_594_ = lean_box(0);
v___x_595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11));
v___x_596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_596_, 0, v___x_584_);
lean_ctor_set(v___x_596_, 1, v___x_591_);
lean_ctor_set(v___x_596_, 2, v___x_593_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
lean_inc(v___x_588_);
v___x_597_ = l_Lean_Syntax_node2(v___x_584_, v___x_588_, v___x_590_, v___x_596_);
v___x_598_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_599_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14));
v___x_600_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_599_);
v___x_601_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_584_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc(v___x_600_);
v___x_603_ = l_Lean_Syntax_node1(v___x_584_, v___x_600_, v___x_602_);
lean_inc(v___x_576_);
lean_inc_n(v___x_603_, 2);
v___x_604_ = l_Lean_Syntax_node4(v___x_584_, v___x_598_, v___x_603_, v___x_603_, v___x_603_, v___x_576_);
v_macroScope_605_ = lean_ctor_get(v___y_578_, 0);
v_traceMsgs_606_ = lean_ctor_get(v___y_578_, 1);
v_expandedMacroDecls_607_ = lean_ctor_get(v___y_578_, 2);
v_isSharedCheck_796_ = !lean_is_exclusive(v___y_578_);
if (v_isSharedCheck_796_ == 0)
{
v___x_609_ = v___y_578_;
v_isShared_610_ = v_isSharedCheck_796_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_expandedMacroDecls_607_);
lean_inc(v_traceMsgs_606_);
lean_inc(v_macroScope_605_);
lean_dec(v___y_578_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_796_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_nat_add(v_macroScope_605_, v___x_562_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_traceMsgs_606_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_expandedMacroDecls_607_);
v___x_613_ = v_reuseFailAlloc_795_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; 
lean_inc_ref(v___f_567_);
lean_inc_ref(v___y_573_);
lean_inc(v_ref_581_);
v___x_614_ = lean_apply_3(v___f_567_, v_ref_581_, v___y_573_, v___x_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_n(v_a_615_, 9);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_614_, 2);
lean_inc(v___x_586_);
v___x_617_ = l_Lean_Syntax_node2(v___x_584_, v___x_586_, v___x_597_, v___x_604_);
v___x_618_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
lean_inc(v_quotContext_579_);
v___x_619_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_618_, v_macroScope_605_);
v___x_620_ = l_Lean_mkIdentFrom(v___x_576_, v___x_619_, v___x_583_);
lean_dec(v___x_576_);
v___x_621_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18));
lean_inc_ref_n(v___x_566_, 6);
lean_inc_ref_n(v___x_565_, 6);
lean_inc_ref_n(v___x_564_, 6);
v___x_622_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_621_);
v___x_623_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19));
v___x_624_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_623_);
v___x_625_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20));
v___x_626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_626_, 0, v_a_615_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21));
v___x_628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_628_, 0, v_a_615_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_Syntax_node1(v_a_615_, v___x_598_, v___x_628_);
v___x_630_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22));
v___x_631_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_630_);
v___x_632_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_633_, 0, v_a_615_);
lean_ctor_set(v___x_633_, 1, v___x_598_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
lean_inc_ref_n(v___x_633_, 3);
v___x_634_ = l_Lean_Syntax_node1(v_a_615_, v___x_631_, v___x_633_);
v___x_635_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24));
v___x_636_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_635_);
v___x_637_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25));
v___x_638_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_637_);
v___x_639_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26));
v___x_640_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_639_);
lean_inc(v___x_620_);
lean_inc(v___x_640_);
v___x_641_ = l_Lean_Syntax_node1(v_a_615_, v___x_640_, v___x_620_);
v___x_642_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27));
v___x_643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_643_, 0, v_a_615_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Lean_Syntax_node5(v_a_615_, v___x_638_, v___x_641_, v___x_633_, v___x_633_, v___x_643_, v___x_617_);
lean_inc_ref(v___y_573_);
lean_inc(v_ref_581_);
v___x_645_ = lean_apply_3(v___f_567_, v_ref_581_, v___y_573_, v_a_616_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_776_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_a_647_ = lean_ctor_get(v___x_645_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_776_ == 0)
{
v___x_649_ = v___x_645_;
v_isShared_650_ = v_isSharedCheck_776_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_776_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
lean_inc_n(v_a_615_, 2);
v___x_651_ = l_Lean_Syntax_node1(v_a_615_, v___x_636_, v___x_644_);
v___x_652_ = l_Lean_Syntax_node4(v_a_615_, v___x_624_, v___x_626_, v___x_629_, v___x_634_, v___x_651_);
lean_inc_n(v___x_622_, 4);
v___x_653_ = l_Lean_Syntax_node2(v_a_615_, v___x_622_, v___x_652_, v___x_633_);
v___x_654_ = lean_array_push(v_fst_568_, v___x_653_);
v___x_655_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28));
lean_inc_ref_n(v___x_566_, 11);
lean_inc_ref_n(v___x_565_, 11);
lean_inc_ref_n(v___x_564_, 13);
v___x_656_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_655_);
v___x_657_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
v___x_658_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_657_);
v___x_659_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v_a_646_, 54);
v___x_660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_660_, 0, v_a_646_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_661_, 0, v_a_646_);
lean_ctor_set(v___x_661_, 1, v___x_598_);
lean_ctor_set(v___x_661_, 2, v___x_632_);
v___x_662_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31));
v___x_663_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_662_);
v___x_664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_664_, 0, v_a_646_);
lean_ctor_set(v___x_664_, 1, v___x_589_);
v___x_665_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33);
v___x_666_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36));
lean_inc_n(v_currMacroScope_580_, 5);
lean_inc_n(v_quotContext_579_, 5);
v___x_667_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_666_, v_currMacroScope_580_);
v___x_668_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_669_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_669_, 0, v_a_646_);
lean_ctor_set(v___x_669_, 1, v___x_665_);
lean_ctor_set(v___x_669_, 2, v___x_667_);
lean_ctor_set(v___x_669_, 3, v___x_668_);
v___x_670_ = l_Lean_Syntax_node2(v_a_646_, v___x_588_, v___x_664_, v___x_669_);
v___x_671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_671_, 0, v_a_646_);
lean_ctor_set(v___x_671_, 1, v___x_601_);
v___x_672_ = l_Lean_Syntax_node1(v_a_646_, v___x_600_, v___x_671_);
lean_inc(v___x_620_);
lean_inc_n(v___x_672_, 2);
v___x_673_ = l_Lean_Syntax_node4(v_a_646_, v___x_598_, v___x_672_, v___x_672_, v___x_672_, v___x_620_);
lean_inc(v___x_586_);
v___x_674_ = l_Lean_Syntax_node2(v_a_646_, v___x_586_, v___x_670_, v___x_673_);
lean_inc_ref_n(v___x_661_, 9);
v___x_675_ = l_Lean_Syntax_node2(v_a_646_, v___x_663_, v___x_661_, v___x_674_);
v___x_676_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_675_);
v___x_677_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_678_, 0, v_a_646_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40));
v___x_680_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_679_);
v___x_681_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_682_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_681_);
v___x_683_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_684_, 0, v_a_646_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44);
v___x_686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45));
v___x_687_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_686_, v_currMacroScope_580_);
v___x_688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_689_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_689_, 0, v_a_646_);
lean_ctor_set(v___x_689_, 1, v___x_685_);
lean_ctor_set(v___x_689_, 2, v___x_687_);
lean_ctor_set(v___x_689_, 3, v___x_688_);
v___x_690_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_689_);
v___x_691_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_690_);
v___x_692_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_693_, 0, v_a_646_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51));
v___x_695_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_694_);
v___x_696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v_a_646_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_Lean_Syntax_node1(v_a_646_, v___x_695_, v___x_697_);
v___x_699_ = l_Lean_Syntax_node2(v_a_646_, v___x_622_, v___x_698_, v___x_661_);
v___x_700_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_699_);
lean_inc_n(v___x_656_, 2);
v___x_701_ = l_Lean_Syntax_node1(v_a_646_, v___x_656_, v___x_700_);
lean_inc_ref(v___x_693_);
lean_inc_ref(v___x_684_);
lean_inc(v___x_682_);
v___x_702_ = l_Lean_Syntax_node4(v_a_646_, v___x_682_, v___x_684_, v___x_691_, v___x_693_, v___x_701_);
v___x_703_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54);
v___x_704_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55));
v___x_705_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_704_, v_currMacroScope_580_);
v___x_706_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58));
v___x_707_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_707_, 0, v_a_646_);
lean_ctor_set(v___x_707_, 1, v___x_703_);
lean_ctor_set(v___x_707_, 2, v___x_705_);
lean_ctor_set(v___x_707_, 3, v___x_706_);
v___x_708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59));
v___x_709_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_708_);
v___x_710_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60));
v___x_711_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_710_);
v___x_712_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61));
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v_a_646_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
v___x_715_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65);
v___x_716_ = lean_box(0);
v___x_717_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_716_, v_currMacroScope_580_);
v___x_718_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66));
v___x_719_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67));
v___x_720_ = l_Lean_Name_mkStr3(v___x_564_, v___x_718_, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68));
v___x_723_ = l_Lean_Name_mkStr2(v___x_564_, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___x_725_ = l_Lean_Name_mkStr3(v___x_564_, v___x_565_, v___x_566_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_594_);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_724_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_721_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_730_, 0, v_a_646_);
lean_ctor_set(v___x_730_, 1, v___x_715_);
lean_ctor_set(v___x_730_, 2, v___x_717_);
lean_ctor_set(v___x_730_, 3, v___x_729_);
v___x_731_ = l_Lean_Syntax_node1(v_a_646_, v___x_714_, v___x_730_);
v___x_732_ = l_Lean_Syntax_node2(v_a_646_, v___x_711_, v___x_713_, v___x_731_);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v_a_646_);
lean_ctor_set(v___x_733_, 1, v___x_569_);
v___x_734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70);
v___x_735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71));
v___x_736_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_735_, v_currMacroScope_580_);
v___x_737_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_737_, 0, v_a_646_);
lean_ctor_set(v___x_737_, 1, v___x_734_);
lean_ctor_set(v___x_737_, 2, v___x_736_);
lean_ctor_set(v___x_737_, 3, v___x_594_);
lean_inc_ref(v___x_737_);
v___x_738_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_737_);
v___x_739_ = l_Lean_Syntax_node3(v_a_646_, v___x_598_, v___x_575_, v___x_733_, v___x_738_);
v___x_740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_646_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_Syntax_node3(v_a_646_, v___x_709_, v___x_732_, v___x_739_, v___x_741_);
v___x_743_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_742_);
v___x_744_ = l_Lean_Syntax_node2(v_a_646_, v___x_586_, v___x_707_, v___x_743_);
v___x_745_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_744_);
v___x_746_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_745_);
v___x_747_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73));
v___x_748_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_747_);
v___x_749_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74));
v___x_750_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v_a_646_, v___x_640_, v___x_620_);
v___x_752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_752_, 0, v_a_646_);
lean_ctor_set(v___x_752_, 1, v___x_642_);
v___x_753_ = l_Lean_Syntax_node5(v_a_646_, v___x_750_, v___x_751_, v___x_661_, v___x_661_, v___x_752_, v___x_737_);
v___x_754_ = l_Lean_Syntax_node1(v_a_646_, v___x_748_, v___x_753_);
v___x_755_ = l_Lean_Syntax_node2(v_a_646_, v___x_622_, v___x_754_, v___x_661_);
v___x_756_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_757_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_756_);
v___x_758_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v_a_646_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_Syntax_node2(v_a_646_, v___x_757_, v___x_759_, v_snd_570_);
v___x_761_ = l_Lean_Syntax_node2(v_a_646_, v___x_622_, v___x_760_, v___x_661_);
v___x_762_ = l_Lean_Syntax_node2(v_a_646_, v___x_598_, v___x_755_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v_a_646_, v___x_656_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node4(v_a_646_, v___x_682_, v___x_684_, v___x_746_, v___x_693_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node2(v_a_646_, v___x_598_, v___x_702_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v_a_646_, v___x_680_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node7(v_a_646_, v___x_658_, v___x_660_, v___x_661_, v___x_661_, v___x_661_, v___x_676_, v___x_678_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node2(v_a_646_, v___x_622_, v___x_767_, v___x_661_);
v___x_769_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node1(v_a_646_, v___x_656_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_654_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_772_);
v___x_774_ = v___x_649_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_a_647_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
lean_object* v_a_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v___x_644_);
lean_dec(v___x_640_);
lean_dec(v___x_636_);
lean_dec(v___x_634_);
lean_dec_ref_known(v___x_633_, 3);
lean_dec(v___x_629_);
lean_dec_ref_known(v___x_626_, 2);
lean_dec(v___x_624_);
lean_dec(v___x_622_);
lean_dec(v___x_620_);
lean_dec(v_a_615_);
lean_dec(v___x_600_);
lean_dec(v___x_588_);
lean_dec(v___x_586_);
lean_dec(v___x_575_);
lean_dec(v_snd_570_);
lean_dec_ref(v___x_569_);
lean_dec(v_fst_568_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_564_);
v_a_777_ = lean_ctor_get(v___x_645_, 0);
v_a_778_ = lean_ctor_get(v___x_645_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_645_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_inc(v_a_777_);
lean_dec(v___x_645_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_macroScope_605_);
lean_dec(v___x_604_);
lean_dec(v___x_600_);
lean_dec(v___x_597_);
lean_dec(v___x_588_);
lean_dec(v___x_586_);
lean_dec(v___x_584_);
lean_dec(v___x_576_);
lean_dec(v___x_575_);
lean_dec(v_snd_570_);
lean_dec_ref(v___x_569_);
lean_dec(v_fst_568_);
lean_dec_ref(v___f_567_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_564_);
v_a_786_ = lean_ctor_get(v___x_614_, 0);
v_a_787_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_614_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_inc(v_a_786_);
lean_dec(v___x_614_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_786_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1___boxed(lean_object* v___x_810_, lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v___x_813_, lean_object* v___x_814_, lean_object* v___x_815_, lean_object* v___f_816_, lean_object* v_fst_817_, lean_object* v___x_818_, lean_object* v_snd_819_, lean_object* v_x_820_, lean_object* v_h_x3f_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(v___x_810_, v___x_811_, v___x_812_, v___x_813_, v___x_814_, v___x_815_, v___f_816_, v_fst_817_, v___x_818_, v_snd_819_, v_x_820_, v_h_x3f_821_, v___y_822_, v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v_h_x3f_821_);
lean_dec(v___x_812_);
lean_dec(v___x_811_);
lean_dec(v___x_810_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0(lean_object* v_____do__lift_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = 0;
v___x_829_ = l_Lean_SourceInfo_fromRef(v_____do__lift_825_, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___y_827_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0___boxed(lean_object* v_____do__lift_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0(v_____do__lift_831_, v___y_832_, v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v_____do__lift_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(lean_object* v_a_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_array_840_; lean_object* v_start_841_; lean_object* v_stop_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_935_; 
v_array_840_ = lean_ctor_get(v_a_836_, 0);
v_start_841_ = lean_ctor_get(v_a_836_, 1);
v_stop_842_ = lean_ctor_get(v_a_836_, 2);
v_isSharedCheck_935_ = !lean_is_exclusive(v_a_836_);
if (v_isSharedCheck_935_ == 0)
{
v___x_844_ = v_a_836_;
v_isShared_845_ = v_isSharedCheck_935_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_stop_842_);
lean_inc(v_start_841_);
lean_inc(v_array_840_);
lean_dec(v_a_836_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_935_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
uint8_t v___x_846_; 
v___x_846_ = lean_nat_dec_lt(v_start_841_, v_stop_842_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_del_object(v___x_844_);
lean_dec(v_stop_842_);
lean_dec(v_start_841_);
lean_dec_ref(v_array_840_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_b_837_);
lean_ctor_set(v___x_847_, 1, v___y_839_);
return v___x_847_;
}
else
{
lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_934_; 
v_fst_848_ = lean_ctor_get(v_b_837_, 0);
v_snd_849_ = lean_ctor_get(v_b_837_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_b_837_);
if (v_isSharedCheck_934_ == 0)
{
v___x_851_ = v_b_837_;
v_isShared_852_ = v_isSharedCheck_934_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_848_);
lean_dec(v_b_837_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_934_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_855_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_856_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_857_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v___x_858_ = lean_nat_add(v_start_841_, v___x_853_);
lean_inc_ref(v_array_840_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_858_);
v___x_860_ = v___x_844_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_array_840_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_stop_842_);
v___x_860_ = v_reuseFailAlloc_933_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___y_862_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = lean_array_fget(v_array_840_, v_start_841_);
lean_dec(v_start_841_);
lean_dec_ref(v_array_840_);
lean_inc(v___x_886_);
v___x_887_ = l_Lean_Syntax_isOfKind(v___x_886_, v___x_857_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v___x_886_);
v___x_888_ = l_Lean_Macro_throwUnsupported___redArg(v___y_839_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; 
v_a_889_ = lean_ctor_get(v___x_888_, 1);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 2);
if (v_isShared_852_ == 0)
{
v___x_891_ = v___x_851_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_snd_849_);
v___x_891_ = v_reuseFailAlloc_893_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
v_a_836_ = v___x_860_;
v_b_837_ = v___x_891_;
v___y_839_ = v_a_889_;
goto _start;
}
}
else
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v___x_860_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
v_a_894_ = lean_ctor_get(v___x_888_, 0);
v_a_895_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_888_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_inc(v_a_894_);
lean_dec(v___x_888_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_894_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___f_903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___closed__0));
v___x_904_ = lean_unsigned_to_nat(3u);
v___x_905_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = l_Lean_Syntax_getArg(v___x_886_, v___x_906_);
v___x_908_ = l_Lean_Syntax_isNone(v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_907_);
v___x_910_ = l_Lean_Syntax_matchesNull(v___x_907_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
lean_dec(v___x_907_);
lean_dec(v___x_886_);
v___x_911_ = l_Lean_Macro_throwUnsupported___redArg(v___y_839_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; 
v_a_912_ = lean_ctor_get(v___x_911_, 1);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 2);
if (v_isShared_852_ == 0)
{
v___x_914_ = v___x_851_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_snd_849_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
v_a_836_ = v___x_860_;
v_b_837_ = v___x_914_;
v___y_839_ = v_a_912_;
goto _start;
}
}
else
{
lean_object* v_a_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v___x_860_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
v_a_917_ = lean_ctor_get(v___x_911_, 0);
v_a_918_ = lean_ctor_get(v___x_911_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_911_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_inc(v_a_917_);
lean_dec(v___x_911_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_917_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_del_object(v___x_851_);
v___x_926_ = l_Lean_Syntax_getArg(v___x_907_, v___x_906_);
lean_dec(v___x_907_);
v___x_927_ = lean_box(0);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
v___x_929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(v___x_886_, v___x_853_, v___x_904_, v___x_854_, v___x_855_, v___x_856_, v___f_903_, v_fst_848_, v___x_905_, v_snd_849_, v___x_927_, v___x_928_, v___y_838_, v___y_839_);
lean_dec_ref_known(v___x_928_, 1);
lean_dec(v___x_886_);
v___y_862_ = v___x_929_;
goto v___jp_861_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v___x_907_);
lean_del_object(v___x_851_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_box(0);
v___x_932_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(v___x_886_, v___x_853_, v___x_904_, v___x_854_, v___x_855_, v___x_856_, v___f_903_, v_fst_848_, v___x_905_, v_snd_849_, v___x_930_, v___x_931_, v___y_838_, v___y_839_);
lean_dec(v___x_886_);
v___y_862_ = v___x_932_;
goto v___jp_861_;
}
}
v___jp_861_:
{
if (lean_obj_tag(v___y_862_) == 0)
{
lean_object* v_a_863_; 
v_a_863_ = lean_ctor_get(v___y_862_, 0);
lean_inc(v_a_863_);
if (lean_obj_tag(v_a_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v___x_860_);
v_a_864_ = lean_ctor_get(v___y_862_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v___y_862_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v___y_862_, 0);
lean_dec(v_unused_873_);
v___x_866_ = v___y_862_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___y_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_a_868_; lean_object* v___x_870_; 
v_a_868_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v_a_863_, 1);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_a_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_868_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_a_864_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v_a_875_; 
v_a_874_ = lean_ctor_get(v___y_862_, 1);
lean_inc(v_a_874_);
lean_dec_ref_known(v___y_862_, 2);
v_a_875_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v_a_863_, 1);
v_a_836_ = v___x_860_;
v_b_837_ = v_a_875_;
v___y_839_ = v_a_874_;
goto _start;
}
}
else
{
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v___x_860_);
v_a_877_ = lean_ctor_get(v___y_862_, 0);
v_a_878_ = lean_ctor_get(v___y_862_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___y_862_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___y_862_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_inc(v_a_877_);
lean_dec(v___y_862_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_877_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___boxed(lean_object* v_a_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v_a_936_, v_b_937_, v___y_938_, v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object* v_stx_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; uint8_t v___x_1149_; 
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_1010_);
v___x_1149_ = l_Lean_Syntax_isOfKind(v_stx_1010_, v___x_1013_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec(v_stx_1010_);
v___x_1150_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v_tk_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v_x_1273_; lean_object* v_body_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v_h_x3f_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v_tk_1261_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1151_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1262_);
lean_inc(v___x_1263_);
v___x_1264_ = l_Lean_Syntax_matchesNull(v___x_1263_, v___x_1262_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1384_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v_dec_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v_inv_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1384_ = lean_unsigned_to_nat(2u);
v___x_1446_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1384_);
v___x_1447_ = l_Lean_Syntax_isNone(v___x_1446_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; 
lean_inc(v___x_1446_);
v___x_1448_ = l_Lean_Syntax_matchesNull(v___x_1446_, v___x_1262_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v___x_1446_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1449_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_1449_;
}
else
{
lean_object* v_inv_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_inv_1450_ = l_Lean_Syntax_getArg(v___x_1446_, v___x_1151_);
lean_dec(v___x_1446_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1450_);
v___x_1452_ = l_Lean_Syntax_isOfKind(v_inv_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_dec(v_inv_1450_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1453_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_inv_1450_);
v_inv_1432_ = v___x_1454_;
v___y_1433_ = v_a_1011_;
v___y_1434_ = v_a_1012_;
goto v___jp_1431_;
}
}
}
else
{
lean_object* v___x_1455_; 
lean_dec(v___x_1446_);
v___x_1455_ = lean_box(0);
v_inv_1432_ = v___x_1455_;
v___y_1433_ = v_a_1011_;
v___y_1434_ = v_a_1012_;
goto v___jp_1431_;
}
v___jp_1385_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_array_get(v___x_1394_, v___y_1387_, v___x_1151_);
lean_inc(v___x_1395_);
v___x_1396_ = l_Lean_Syntax_isOfKind(v___x_1395_, v___y_1389_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v___x_1395_);
lean_dec(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v_tk_1261_);
v___x_1397_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1393_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = l_Lean_Syntax_getArg(v___x_1395_, v___x_1151_);
v___x_1399_ = l_Lean_Syntax_isNone(v___x_1398_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; 
lean_inc(v___x_1398_);
v___x_1400_ = l_Lean_Syntax_matchesNull(v___x_1398_, v___x_1384_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v___x_1398_);
lean_dec(v___x_1395_);
lean_dec(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v_tk_1261_);
v___x_1401_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1393_);
return v___x_1401_;
}
else
{
lean_object* v_h_x3f_1402_; lean_object* v___x_1403_; 
v_h_x3f_1402_ = l_Lean_Syntax_getArg(v___x_1398_, v___x_1151_);
lean_dec(v___x_1398_);
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_h_x3f_1402_);
v___y_1314_ = v___y_1386_;
v___y_1315_ = v___y_1387_;
v___y_1316_ = v___x_1395_;
v___y_1317_ = v___y_1388_;
v___y_1318_ = v___y_1389_;
v___y_1319_ = v___y_1390_;
v___y_1320_ = v___y_1391_;
v_h_x3f_1321_ = v___x_1403_;
v___y_1322_ = v___y_1392_;
v___y_1323_ = v___y_1393_;
goto v___jp_1313_;
}
}
else
{
lean_object* v___x_1404_; 
lean_dec(v___x_1398_);
v___x_1404_ = lean_box(0);
v___y_1314_ = v___y_1386_;
v___y_1315_ = v___y_1387_;
v___y_1316_ = v___x_1395_;
v___y_1317_ = v___y_1388_;
v___y_1318_ = v___y_1389_;
v___y_1319_ = v___y_1390_;
v___y_1320_ = v___y_1391_;
v_h_x3f_1321_ = v___x_1404_;
v___y_1322_ = v___y_1392_;
v___y_1323_ = v___y_1393_;
goto v___jp_1313_;
}
}
}
v___jp_1405_:
{
lean_object* v___x_1411_; lean_object* v_body_1412_; lean_object* v___x_1413_; lean_object* v_decls_1414_; lean_object* v_decls_1415_; 
v___x_1411_ = lean_unsigned_to_nat(5u);
v_body_1412_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1411_);
lean_dec(v_stx_1010_);
v___x_1413_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v_decls_1414_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_1415_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1414_);
lean_dec_ref(v_decls_1414_);
if (lean_obj_tag(v___y_1407_) == 1)
{
lean_object* v_val_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_val_1416_ = lean_ctor_get(v___y_1407_, 0);
v___x_1417_ = lean_array_get_size(v_decls_1415_);
v___x_1418_ = lean_nat_dec_lt(v___x_1262_, v___x_1417_);
if (v___x_1418_ == 0)
{
v___y_1386_ = v_body_1412_;
v___y_1387_ = v_decls_1415_;
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___x_1413_;
v___y_1390_ = v_dec_1408_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___y_1409_;
v___y_1393_ = v___y_1410_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1420_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1416_, v___x_1419_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 1);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 2);
v___y_1386_ = v_body_1412_;
v___y_1387_ = v_decls_1415_;
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___x_1413_;
v___y_1390_ = v_dec_1408_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___y_1409_;
v___y_1393_ = v_a_1421_;
goto v___jp_1385_;
}
else
{
lean_object* v_a_1422_; lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref_known(v___y_1407_, 1);
lean_dec_ref(v_decls_1415_);
lean_dec(v_body_1412_);
lean_dec(v_dec_1408_);
lean_dec(v_tk_1261_);
v_a_1422_ = lean_ctor_get(v___x_1420_, 0);
v_a_1423_ = lean_ctor_get(v___x_1420_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1420_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_inc(v_a_1422_);
lean_dec(v___x_1420_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1422_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
else
{
v___y_1386_ = v_body_1412_;
v___y_1387_ = v_decls_1415_;
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___x_1413_;
v___y_1390_ = v_dec_1408_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___y_1409_;
v___y_1393_ = v___y_1410_;
goto v___jp_1385_;
}
}
v___jp_1431_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_unsigned_to_nat(3u);
v___x_1436_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1435_);
v___x_1437_ = l_Lean_Syntax_isNone(v___x_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; 
lean_inc(v___x_1436_);
v___x_1438_ = l_Lean_Syntax_matchesNull(v___x_1436_, v___x_1262_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; 
lean_dec(v___x_1436_);
lean_dec(v_inv_1432_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1439_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1434_);
return v___x_1439_;
}
else
{
lean_object* v_dec_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_dec_1440_ = l_Lean_Syntax_getArg(v___x_1436_, v___x_1151_);
lean_dec(v___x_1436_);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1440_);
v___x_1442_ = l_Lean_Syntax_isOfKind(v_dec_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_dec_1440_);
lean_dec(v_inv_1432_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1443_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1434_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_dec_1440_);
v___y_1406_ = v___x_1435_;
v___y_1407_ = v_inv_1432_;
v_dec_1408_ = v___x_1444_;
v___y_1409_ = v___y_1433_;
v___y_1410_ = v___y_1434_;
goto v___jp_1405_;
}
}
}
else
{
lean_object* v___x_1445_; 
lean_dec(v___x_1436_);
v___x_1445_ = lean_box(0);
v___y_1406_ = v___x_1435_;
v___y_1407_ = v_inv_1432_;
v_dec_1408_ = v___x_1445_;
v___y_1409_ = v___y_1433_;
v___y_1410_ = v___y_1434_;
goto v___jp_1405_;
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v_x_1511_; lean_object* v_body_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v_h_x3f_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v_inv_1645_; lean_object* v_dec_1646_; lean_object* v_body_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; uint8_t v___y_1672_; uint8_t v___y_1673_; lean_object* v_inv_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v___y_1685_; uint8_t v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; uint8_t v___y_1690_; lean_object* v___y_1691_; lean_object* v_inv_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v_dec_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v_x_1775_; lean_object* v_body_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; uint8_t v___y_1821_; lean_object* v___y_1822_; lean_object* v_h_x3f_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; uint8_t v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; lean_object* v___y_1911_; lean_object* v_dec_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v_inv_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; uint8_t v___x_2013_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v_x_2021_; lean_object* v_body_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v_h_x3f_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; 
v___x_1456_ = l_Lean_Syntax_getArg(v___x_1263_, v___x_1151_);
v___x_1457_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_1456_);
v___x_2013_ = l_Lean_Syntax_isOfKind(v___x_1456_, v___x_1457_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2131_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v_dec_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v_inv_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
lean_dec(v___x_1456_);
v___x_2131_ = lean_unsigned_to_nat(2u);
v___x_2191_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2131_);
v___x_2192_ = l_Lean_Syntax_isNone(v___x_2191_);
if (v___x_2192_ == 0)
{
uint8_t v___x_2193_; 
lean_inc(v___x_2191_);
v___x_2193_ = l_Lean_Syntax_matchesNull(v___x_2191_, v___x_1262_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec(v___x_2191_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2194_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_2194_;
}
else
{
lean_object* v_inv_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_inv_2195_ = l_Lean_Syntax_getArg(v___x_2191_, v___x_1151_);
lean_dec(v___x_2191_);
v___x_2196_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_2195_);
v___x_2197_ = l_Lean_Syntax_isOfKind(v_inv_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v_inv_2195_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2198_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_2198_;
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_inv_2195_);
v_inv_2177_ = v___x_2199_;
v___y_2178_ = v_a_1011_;
v___y_2179_ = v_a_1012_;
goto v___jp_2176_;
}
}
}
else
{
lean_object* v___x_2200_; 
lean_dec(v___x_2191_);
v___x_2200_ = lean_box(0);
v_inv_2177_ = v___x_2200_;
v___y_2178_ = v_a_1011_;
v___y_2179_ = v_a_1012_;
goto v___jp_2176_;
}
v___jp_2132_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_array_get(v___x_2140_, v___y_2133_, v___x_1151_);
lean_inc(v___x_2141_);
v___x_2142_ = l_Lean_Syntax_isOfKind(v___x_2141_, v___x_1457_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v___x_2141_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v_tk_1261_);
v___x_2143_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2139_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = l_Lean_Syntax_getArg(v___x_2141_, v___x_1151_);
v___x_2145_ = l_Lean_Syntax_isNone(v___x_2144_);
if (v___x_2145_ == 0)
{
uint8_t v___x_2146_; 
lean_inc(v___x_2144_);
v___x_2146_ = l_Lean_Syntax_matchesNull(v___x_2144_, v___x_2131_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec(v___x_2144_);
lean_dec(v___x_2141_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v_tk_1261_);
v___x_2147_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2139_);
return v___x_2147_;
}
else
{
lean_object* v_h_x3f_2148_; lean_object* v___x_2149_; 
v_h_x3f_2148_ = l_Lean_Syntax_getArg(v___x_2144_, v___x_1151_);
lean_dec(v___x_2144_);
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_h_x3f_2148_);
v___y_2062_ = v___y_2133_;
v___y_2063_ = v___y_2134_;
v___y_2064_ = v___y_2135_;
v___y_2065_ = v___y_2136_;
v___y_2066_ = v___x_2141_;
v___y_2067_ = v___y_2137_;
v_h_x3f_2068_ = v___x_2149_;
v___y_2069_ = v___y_2138_;
v___y_2070_ = v___y_2139_;
goto v___jp_2061_;
}
}
else
{
lean_object* v___x_2150_; 
lean_dec(v___x_2144_);
v___x_2150_ = lean_box(0);
v___y_2062_ = v___y_2133_;
v___y_2063_ = v___y_2134_;
v___y_2064_ = v___y_2135_;
v___y_2065_ = v___y_2136_;
v___y_2066_ = v___x_2141_;
v___y_2067_ = v___y_2137_;
v_h_x3f_2068_ = v___x_2150_;
v___y_2069_ = v___y_2138_;
v___y_2070_ = v___y_2139_;
goto v___jp_2061_;
}
}
}
v___jp_2151_:
{
lean_object* v___x_2157_; lean_object* v_body_2158_; lean_object* v_decls_2159_; lean_object* v_decls_2160_; 
v___x_2157_ = lean_unsigned_to_nat(5u);
v_body_2158_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2157_);
lean_dec(v_stx_1010_);
v_decls_2159_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_2160_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_2159_);
lean_dec_ref(v_decls_2159_);
if (lean_obj_tag(v___y_2152_) == 1)
{
lean_object* v_val_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v_val_2161_ = lean_ctor_get(v___y_2152_, 0);
v___x_2162_ = lean_array_get_size(v_decls_2160_);
v___x_2163_ = lean_nat_dec_lt(v___x_1262_, v___x_2162_);
if (v___x_2163_ == 0)
{
v___y_2133_ = v_decls_2160_;
v___y_2134_ = v_body_2158_;
v___y_2135_ = v_dec_2154_;
v___y_2136_ = v___y_2152_;
v___y_2137_ = v___y_2153_;
v___y_2138_ = v___y_2155_;
v___y_2139_ = v___y_2156_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_2165_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2161_, v___x_2164_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 1);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 2);
v___y_2133_ = v_decls_2160_;
v___y_2134_ = v_body_2158_;
v___y_2135_ = v_dec_2154_;
v___y_2136_ = v___y_2152_;
v___y_2137_ = v___y_2153_;
v___y_2138_ = v___y_2155_;
v___y_2139_ = v_a_2166_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2167_; lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref_known(v___y_2152_, 1);
lean_dec_ref(v_decls_2160_);
lean_dec(v_body_2158_);
lean_dec(v_dec_2154_);
lean_dec(v_tk_1261_);
v_a_2167_ = lean_ctor_get(v___x_2165_, 0);
v_a_2168_ = lean_ctor_get(v___x_2165_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2165_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_inc(v_a_2167_);
lean_dec(v___x_2165_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2167_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
else
{
v___y_2133_ = v_decls_2160_;
v___y_2134_ = v_body_2158_;
v___y_2135_ = v_dec_2154_;
v___y_2136_ = v___y_2152_;
v___y_2137_ = v___y_2153_;
v___y_2138_ = v___y_2155_;
v___y_2139_ = v___y_2156_;
goto v___jp_2132_;
}
}
v___jp_2176_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2180_ = lean_unsigned_to_nat(3u);
v___x_2181_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2180_);
v___x_2182_ = l_Lean_Syntax_isNone(v___x_2181_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; 
lean_inc(v___x_2181_);
v___x_2183_ = l_Lean_Syntax_matchesNull(v___x_2181_, v___x_1262_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; 
lean_dec(v___x_2181_);
lean_dec(v_inv_2177_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2184_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2179_);
return v___x_2184_;
}
else
{
lean_object* v_dec_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_dec_2185_ = l_Lean_Syntax_getArg(v___x_2181_, v___x_1151_);
lean_dec(v___x_2181_);
v___x_2186_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_2185_);
v___x_2187_ = l_Lean_Syntax_isOfKind(v_dec_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
lean_dec(v_dec_2185_);
lean_dec(v_inv_2177_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2188_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2179_);
return v___x_2188_;
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_dec_2185_);
v___y_2152_ = v_inv_2177_;
v___y_2153_ = v___x_2180_;
v_dec_2154_ = v___x_2189_;
v___y_2155_ = v___y_2178_;
v___y_2156_ = v___y_2179_;
goto v___jp_2151_;
}
}
}
else
{
lean_object* v___x_2190_; 
lean_dec(v___x_2181_);
v___x_2190_ = lean_box(0);
v___y_2152_ = v_inv_2177_;
v___y_2153_ = v___x_2180_;
v_dec_2154_ = v___x_2190_;
v___y_2155_ = v___y_2178_;
v___y_2156_ = v___y_2179_;
goto v___jp_2151_;
}
}
}
else
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = l_Lean_Syntax_getArg(v___x_1456_, v___x_1151_);
v___x_2202_ = l_Lean_Syntax_isNone(v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v_x_2212_; lean_object* v_body_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; 
v___x_2203_ = lean_unsigned_to_nat(2u);
v___x_2204_ = l_Lean_Syntax_matchesNull(v___x_2201_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2252_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v_h_x3f_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2341_; lean_object* v_dec_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v_inv_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
lean_dec(v___x_1456_);
v___x_2252_ = lean_unsigned_to_nat(3u);
v___x_2378_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2203_);
v___x_2379_ = l_Lean_Syntax_isNone(v___x_2378_);
if (v___x_2379_ == 0)
{
uint8_t v___x_2380_; 
lean_inc(v___x_2378_);
v___x_2380_ = l_Lean_Syntax_matchesNull(v___x_2378_, v___x_1262_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
lean_dec(v___x_2378_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2381_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_2381_;
}
else
{
lean_object* v_inv_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_inv_2382_ = l_Lean_Syntax_getArg(v___x_2378_, v___x_1151_);
lean_dec(v___x_2378_);
v___x_2383_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_2382_);
v___x_2384_ = l_Lean_Syntax_isOfKind(v_inv_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; 
lean_dec(v_inv_2382_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2385_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_2385_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_inv_2382_);
v_inv_2365_ = v___x_2386_;
v___y_2366_ = v_a_1011_;
v___y_2367_ = v_a_1012_;
goto v___jp_2364_;
}
}
}
else
{
lean_object* v___x_2387_; 
lean_dec(v___x_2378_);
v___x_2387_ = lean_box(0);
v_inv_2365_ = v___x_2387_;
v___y_2366_ = v_a_1011_;
v___y_2367_ = v_a_1012_;
goto v___jp_2364_;
}
v___jp_2253_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_doElems_2264_; uint8_t v___x_2265_; 
v___x_2262_ = l_Lean_Syntax_getArg(v___y_2255_, v___x_1262_);
v___x_2263_ = l_Lean_Syntax_getArg(v___y_2255_, v___x_2252_);
lean_dec(v___y_2255_);
v_doElems_2264_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_2265_ = l_Lean_Syntax_isIdent(v___x_2262_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_2262_);
v___x_2267_ = l_Lean_Syntax_isOfKind(v___x_2262_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_2262_, v___x_2267_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v_a_2270_; lean_object* v_ref_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc_n(v_a_2269_, 2);
v_a_2270_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2268_, 2);
v_ref_2271_ = lean_ctor_get(v___y_2260_, 5);
v___x_2272_ = l_Lean_SourceInfo_fromRef(v_ref_2271_, v___x_2267_);
v___x_2273_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_2274_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2275_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_2277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_2272_, 15);
v___x_2278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2272_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2272_);
lean_ctor_set(v___x_2280_, 1, v___x_2274_);
lean_ctor_set(v___x_2280_, 2, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_2280_, 4);
v___x_2282_ = l_Lean_Syntax_node2(v___x_2272_, v___x_2281_, v___x_2280_, v_a_2269_);
v___x_2283_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2282_);
v___x_2284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_2285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2272_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_2287_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_2288_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_2289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2272_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2262_);
v___x_2291_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2272_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_Syntax_node4(v___x_2272_, v___x_2287_, v___x_2289_, v___x_2291_, v___x_2293_, v___y_2258_);
v___x_2295_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2294_);
v___x_2296_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2286_, v___x_2295_);
v___x_2297_ = l_Lean_Syntax_node7(v___x_2272_, v___x_2276_, v___x_2278_, v___x_2280_, v___x_2280_, v___x_2280_, v___x_2283_, v___x_2285_, v___x_2296_);
v___x_2298_ = l_Lean_Syntax_node2(v___x_2272_, v___x_2275_, v___x_2297_, v___x_2280_);
v___x_2299_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2298_);
v___x_2300_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2273_, v___x_2299_);
v___y_2206_ = v_doElems_2264_;
v___y_2207_ = v_h_x3f_2259_;
v___y_2208_ = v___y_2254_;
v___y_2209_ = v___x_2263_;
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2257_;
v_x_2212_ = v_a_2269_;
v_body_2213_ = v___x_2300_;
v___y_2214_ = v___y_2260_;
v___y_2215_ = v_a_2270_;
goto v___jp_2205_;
}
else
{
lean_object* v_a_2301_; lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v___x_2263_);
lean_dec(v___x_2262_);
lean_dec(v_h_x3f_2259_);
lean_dec(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2254_);
lean_dec(v_tk_1261_);
v_a_2301_ = lean_ctor_get(v___x_2268_, 0);
v_a_2302_ = lean_ctor_get(v___x_2268_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2268_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_inc(v_a_2301_);
lean_dec(v___x_2268_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2301_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_2262_, v___x_2265_, v___y_2260_, v___y_2261_);
lean_dec(v___x_2262_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v_a_2312_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
v_a_2312_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2310_, 2);
v___y_2206_ = v_doElems_2264_;
v___y_2207_ = v_h_x3f_2259_;
v___y_2208_ = v___y_2254_;
v___y_2209_ = v___x_2263_;
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2257_;
v_x_2212_ = v_a_2311_;
v_body_2213_ = v___y_2258_;
v___y_2214_ = v___y_2260_;
v___y_2215_ = v_a_2312_;
goto v___jp_2205_;
}
else
{
lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v___x_2263_);
lean_dec(v_h_x3f_2259_);
lean_dec(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2254_);
lean_dec(v_tk_1261_);
v_a_2313_ = lean_ctor_get(v___x_2310_, 0);
v_a_2314_ = lean_ctor_get(v___x_2310_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2310_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_inc(v_a_2313_);
lean_dec(v___x_2310_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2313_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
else
{
v___y_2206_ = v_doElems_2264_;
v___y_2207_ = v_h_x3f_2259_;
v___y_2208_ = v___y_2254_;
v___y_2209_ = v___x_2263_;
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2257_;
v_x_2212_ = v___x_2262_;
v_body_2213_ = v___y_2258_;
v___y_2214_ = v___y_2260_;
v___y_2215_ = v___y_2261_;
goto v___jp_2205_;
}
}
v___jp_2322_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = lean_box(0);
v___x_2330_ = lean_array_get(v___x_2329_, v___y_2323_, v___x_1151_);
lean_inc(v___x_2330_);
v___x_2331_ = l_Lean_Syntax_isOfKind(v___x_2330_, v___x_1457_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_dec(v___x_2330_);
lean_dec(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v_tk_1261_);
v___x_2332_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2328_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = l_Lean_Syntax_getArg(v___x_2330_, v___x_1151_);
v___x_2334_ = l_Lean_Syntax_isNone(v___x_2333_);
if (v___x_2334_ == 0)
{
uint8_t v___x_2335_; 
lean_inc(v___x_2333_);
v___x_2335_ = l_Lean_Syntax_matchesNull(v___x_2333_, v___x_2203_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
lean_dec(v___x_2333_);
lean_dec(v___x_2330_);
lean_dec(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v_tk_1261_);
v___x_2336_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2328_);
return v___x_2336_;
}
else
{
lean_object* v_h_x3f_2337_; lean_object* v___x_2338_; 
v_h_x3f_2337_ = l_Lean_Syntax_getArg(v___x_2333_, v___x_1151_);
lean_dec(v___x_2333_);
v___x_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_h_x3f_2337_);
v___y_2254_ = v___y_2323_;
v___y_2255_ = v___x_2330_;
v___y_2256_ = v___y_2324_;
v___y_2257_ = v___y_2325_;
v___y_2258_ = v___y_2326_;
v_h_x3f_2259_ = v___x_2338_;
v___y_2260_ = v___y_2327_;
v___y_2261_ = v___y_2328_;
goto v___jp_2253_;
}
}
else
{
lean_object* v___x_2339_; 
lean_dec(v___x_2333_);
v___x_2339_ = lean_box(0);
v___y_2254_ = v___y_2323_;
v___y_2255_ = v___x_2330_;
v___y_2256_ = v___y_2324_;
v___y_2257_ = v___y_2325_;
v___y_2258_ = v___y_2326_;
v_h_x3f_2259_ = v___x_2339_;
v___y_2260_ = v___y_2327_;
v___y_2261_ = v___y_2328_;
goto v___jp_2253_;
}
}
}
v___jp_2340_:
{
lean_object* v___x_2345_; lean_object* v_body_2346_; lean_object* v_decls_2347_; lean_object* v_decls_2348_; 
v___x_2345_ = lean_unsigned_to_nat(5u);
v_body_2346_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2345_);
lean_dec(v_stx_1010_);
v_decls_2347_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_2348_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_2347_);
lean_dec_ref(v_decls_2347_);
if (lean_obj_tag(v___y_2341_) == 1)
{
lean_object* v_val_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_val_2349_ = lean_ctor_get(v___y_2341_, 0);
v___x_2350_ = lean_array_get_size(v_decls_2348_);
v___x_2351_ = lean_nat_dec_lt(v___x_1262_, v___x_2350_);
if (v___x_2351_ == 0)
{
v___y_2323_ = v_decls_2348_;
v___y_2324_ = v_dec_2342_;
v___y_2325_ = v___y_2341_;
v___y_2326_ = v_body_2346_;
v___y_2327_ = v___y_2343_;
v___y_2328_ = v___y_2344_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_2353_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2349_, v___x_2352_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 1);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 2);
v___y_2323_ = v_decls_2348_;
v___y_2324_ = v_dec_2342_;
v___y_2325_ = v___y_2341_;
v___y_2326_ = v_body_2346_;
v___y_2327_ = v___y_2343_;
v___y_2328_ = v_a_2354_;
goto v___jp_2322_;
}
else
{
lean_object* v_a_2355_; lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref_known(v___y_2341_, 1);
lean_dec_ref(v_decls_2348_);
lean_dec(v_body_2346_);
lean_dec(v_dec_2342_);
lean_dec(v_tk_1261_);
v_a_2355_ = lean_ctor_get(v___x_2353_, 0);
v_a_2356_ = lean_ctor_get(v___x_2353_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2353_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_inc(v_a_2355_);
lean_dec(v___x_2353_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2355_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
else
{
v___y_2323_ = v_decls_2348_;
v___y_2324_ = v_dec_2342_;
v___y_2325_ = v___y_2341_;
v___y_2326_ = v_body_2346_;
v___y_2327_ = v___y_2343_;
v___y_2328_ = v___y_2344_;
goto v___jp_2322_;
}
}
v___jp_2364_:
{
lean_object* v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2252_);
v___x_2369_ = l_Lean_Syntax_isNone(v___x_2368_);
if (v___x_2369_ == 0)
{
uint8_t v___x_2370_; 
lean_inc(v___x_2368_);
v___x_2370_ = l_Lean_Syntax_matchesNull(v___x_2368_, v___x_1262_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; 
lean_dec(v___x_2368_);
lean_dec(v_inv_2365_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2371_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2367_);
return v___x_2371_;
}
else
{
lean_object* v_dec_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
v_dec_2372_ = l_Lean_Syntax_getArg(v___x_2368_, v___x_1151_);
lean_dec(v___x_2368_);
v___x_2373_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_2372_);
v___x_2374_ = l_Lean_Syntax_isOfKind(v_dec_2372_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; 
lean_dec(v_dec_2372_);
lean_dec(v_inv_2365_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2375_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2367_);
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_dec_2372_);
v___y_2341_ = v_inv_2365_;
v_dec_2342_ = v___x_2376_;
v___y_2343_ = v___y_2366_;
v___y_2344_ = v___y_2367_;
goto v___jp_2340_;
}
}
}
else
{
lean_object* v___x_2377_; 
lean_dec(v___x_2368_);
v___x_2377_ = lean_box(0);
v___y_2341_ = v_inv_2365_;
v_dec_2342_ = v___x_2377_;
v___y_2343_ = v___y_2366_;
v___y_2344_ = v___y_2367_;
goto v___jp_2340_;
}
}
}
else
{
v___y_1952_ = v_a_1011_;
v___y_1953_ = v_a_1012_;
goto v___jp_1951_;
}
v___jp_2205_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2216_ = lean_array_get_size(v___y_2208_);
v___x_2217_ = l_Array_toSubarray___redArg(v___y_2208_, v___x_1262_, v___x_2216_);
lean_inc_ref(v___y_2206_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___y_2206_);
lean_ctor_set(v___x_2218_, 1, v_body_2213_);
v___x_2219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_2204_, v___x_2217_, v___x_2218_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v_a_2221_; lean_object* v_fst_2222_; lean_object* v_snd_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2242_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
v_a_2221_ = lean_ctor_get(v___x_2219_, 1);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2219_, 2);
v_fst_2222_ = lean_ctor_get(v_a_2220_, 0);
v_snd_2223_ = lean_ctor_get(v_a_2220_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2220_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2225_ = v_a_2220_;
v_isShared_2226_ = v_isSharedCheck_2242_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_snd_2223_);
lean_inc(v_fst_2222_);
lean_dec(v_a_2220_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2242_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v_ref_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v_ref_2227_ = lean_ctor_get(v___y_2214_, 5);
v___x_2228_ = l_Lean_SourceInfo_fromRef(v_ref_2227_, v___x_2204_);
v___x_2229_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_2230_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_2231_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_2226_ == 0)
{
lean_ctor_set_tag(v___x_2225_, 2);
lean_ctor_set(v___x_2225_, 1, v___x_2231_);
lean_ctor_set(v___x_2225_, 0, v___x_2230_);
v___x_2233_ = v___x_2225_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2235_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_2207_) == 1)
{
lean_object* v_val_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_val_2236_ = lean_ctor_get(v___y_2207_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v___y_2207_, 1);
v___x_2237_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_2228_);
v___x_2238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2228_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = l_Array_mkArray2___redArg(v_val_2236_, v___x_2238_);
v___y_1459_ = v___x_2234_;
v___y_1460_ = v_x_2212_;
v___y_1461_ = v_a_2221_;
v___y_1462_ = v_snd_2223_;
v___y_1463_ = v___x_2233_;
v___y_1464_ = v___x_2235_;
v___y_1465_ = v___x_2228_;
v___y_1466_ = v___x_2229_;
v___y_1467_ = v_fst_2222_;
v___y_1468_ = v___y_2210_;
v___y_1469_ = v___y_2209_;
v___y_1470_ = v___y_2211_;
v___y_1471_ = v___x_2239_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_2240_; 
lean_dec(v___y_2207_);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1459_ = v___x_2234_;
v___y_1460_ = v_x_2212_;
v___y_1461_ = v_a_2221_;
v___y_1462_ = v_snd_2223_;
v___y_1463_ = v___x_2233_;
v___y_1464_ = v___x_2235_;
v___y_1465_ = v___x_2228_;
v___y_1466_ = v___x_2229_;
v___y_1467_ = v_fst_2222_;
v___y_1468_ = v___y_2210_;
v___y_1469_ = v___y_2209_;
v___y_1470_ = v___y_2211_;
v___y_1471_ = v___x_2240_;
goto v___jp_1458_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_x_2212_);
lean_dec(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec(v___y_2207_);
lean_dec(v_tk_1261_);
v_a_2243_ = lean_ctor_get(v___x_2219_, 0);
v_a_2244_ = lean_ctor_get(v___x_2219_, 1);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2219_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_inc(v_a_2243_);
lean_dec(v___x_2219_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2243_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_dec(v___x_2201_);
v___y_1952_ = v_a_1011_;
v___y_1953_ = v_a_1012_;
goto v___jp_1951_;
}
}
v___jp_1458_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_inc_ref(v___y_1464_);
v___x_1472_ = l_Array_append___redArg(v___y_1464_, v___y_1471_);
lean_dec_ref(v___y_1471_);
lean_inc_n(v___y_1459_, 2);
lean_inc_n(v___y_1465_, 4);
v___x_1473_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1473_, 0, v___y_1465_);
lean_ctor_set(v___x_1473_, 1, v___y_1459_);
lean_ctor_set(v___x_1473_, 2, v___x_1472_);
v___x_1474_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1465_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = l_Lean_Syntax_node4(v___y_1465_, v___x_1457_, v___x_1473_, v___y_1460_, v___x_1475_, v___y_1469_);
v___x_1477_ = l_Lean_Syntax_node1(v___y_1465_, v___y_1459_, v___x_1476_);
if (lean_obj_tag(v___y_1470_) == 1)
{
lean_object* v_val_1478_; lean_object* v___x_1479_; 
v_val_1478_ = lean_ctor_get(v___y_1470_, 0);
lean_inc(v_val_1478_);
lean_dec_ref_known(v___y_1470_, 1);
v___x_1479_ = l_Array_mkArray1___redArg(v_val_1478_);
v___y_1245_ = v___y_1459_;
v___y_1246_ = v___y_1461_;
v___y_1247_ = v___y_1462_;
v___y_1248_ = v___y_1463_;
v___y_1249_ = v___y_1464_;
v___y_1250_ = v___y_1465_;
v___y_1251_ = v___y_1466_;
v___y_1252_ = v___x_1477_;
v___y_1253_ = v___y_1467_;
v___y_1254_ = v___y_1468_;
v___y_1255_ = v___x_1479_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1480_; 
lean_dec(v___y_1470_);
v___x_1480_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1245_ = v___y_1459_;
v___y_1246_ = v___y_1461_;
v___y_1247_ = v___y_1462_;
v___y_1248_ = v___y_1463_;
v___y_1249_ = v___y_1464_;
v___y_1250_ = v___y_1465_;
v___y_1251_ = v___y_1466_;
v___y_1252_ = v___x_1477_;
v___y_1253_ = v___y_1467_;
v___y_1254_ = v___y_1468_;
v___y_1255_ = v___x_1480_;
goto v___jp_1244_;
}
}
v___jp_1481_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc_ref(v___y_1483_);
v___x_1495_ = l_Array_append___redArg(v___y_1483_, v___y_1494_);
lean_dec_ref(v___y_1494_);
lean_inc_n(v___y_1490_, 2);
lean_inc_n(v___y_1491_, 4);
v___x_1496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1491_);
lean_ctor_set(v___x_1496_, 1, v___y_1490_);
lean_ctor_set(v___x_1496_, 2, v___x_1495_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___y_1491_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = l_Lean_Syntax_node4(v___y_1491_, v___x_1457_, v___x_1496_, v___y_1484_, v___x_1498_, v___y_1488_);
v___x_1500_ = l_Lean_Syntax_node1(v___y_1491_, v___y_1490_, v___x_1499_);
if (lean_obj_tag(v___y_1486_) == 1)
{
lean_object* v_val_1501_; lean_object* v___x_1502_; 
v_val_1501_ = lean_ctor_get(v___y_1486_, 0);
lean_inc(v_val_1501_);
lean_dec_ref_known(v___y_1486_, 1);
v___x_1502_ = l_Array_mkArray1___redArg(v_val_1501_);
v___y_1211_ = v___y_1482_;
v___y_1212_ = v___y_1483_;
v___y_1213_ = v___y_1485_;
v___y_1214_ = v___y_1487_;
v___y_1215_ = v___x_1500_;
v___y_1216_ = v___y_1489_;
v___y_1217_ = v___y_1490_;
v___y_1218_ = v___y_1491_;
v___y_1219_ = v___y_1493_;
v___y_1220_ = v___y_1492_;
v___y_1221_ = v___x_1502_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1503_; 
lean_dec(v___y_1486_);
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1211_ = v___y_1482_;
v___y_1212_ = v___y_1483_;
v___y_1213_ = v___y_1485_;
v___y_1214_ = v___y_1487_;
v___y_1215_ = v___x_1500_;
v___y_1216_ = v___y_1489_;
v___y_1217_ = v___y_1490_;
v___y_1218_ = v___y_1491_;
v___y_1219_ = v___y_1493_;
v___y_1220_ = v___y_1492_;
v___y_1221_ = v___x_1503_;
goto v___jp_1210_;
}
}
v___jp_1504_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1515_ = lean_array_get_size(v___y_1509_);
v___x_1516_ = l_Array_toSubarray___redArg(v___y_1509_, v___x_1262_, v___x_1515_);
lean_inc_ref(v___y_1508_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___y_1508_);
lean_ctor_set(v___x_1517_, 1, v_body_1512_);
v___x_1518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v___x_1516_, v___x_1517_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_a_1520_; lean_object* v_fst_1521_; lean_object* v_snd_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1542_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
v_a_1520_ = lean_ctor_get(v___x_1518_, 1);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1518_, 2);
v_fst_1521_ = lean_ctor_get(v_a_1519_, 0);
v_snd_1522_ = lean_ctor_get(v_a_1519_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_a_1519_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1524_ = v_a_1519_;
v_isShared_1525_ = v_isSharedCheck_1542_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_snd_1522_);
lean_inc(v_fst_1521_);
lean_dec(v_a_1519_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1542_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_ref_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v_ref_1526_ = lean_ctor_get(v___y_1513_, 5);
v___x_1527_ = 0;
v___x_1528_ = l_Lean_SourceInfo_fromRef(v_ref_1526_, v___x_1527_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1530_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 2);
lean_ctor_set(v___x_1524_, 1, v___x_1531_);
lean_ctor_set(v___x_1524_, 0, v___x_1530_);
v___x_1533_ = v___x_1524_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1535_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1505_) == 1)
{
lean_object* v_val_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_val_1536_ = lean_ctor_get(v___y_1505_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___y_1505_, 1);
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1528_);
v___x_1538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1528_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Array_mkArray2___redArg(v_val_1536_, v___x_1538_);
v___y_1482_ = v___x_1529_;
v___y_1483_ = v___x_1535_;
v___y_1484_ = v_x_1511_;
v___y_1485_ = v___x_1533_;
v___y_1486_ = v___y_1506_;
v___y_1487_ = v_a_1520_;
v___y_1488_ = v___y_1507_;
v___y_1489_ = v_fst_1521_;
v___y_1490_ = v___x_1534_;
v___y_1491_ = v___x_1528_;
v___y_1492_ = v_snd_1522_;
v___y_1493_ = v___y_1510_;
v___y_1494_ = v___x_1539_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1540_; 
lean_dec(v___y_1505_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1482_ = v___x_1529_;
v___y_1483_ = v___x_1535_;
v___y_1484_ = v_x_1511_;
v___y_1485_ = v___x_1533_;
v___y_1486_ = v___y_1506_;
v___y_1487_ = v_a_1520_;
v___y_1488_ = v___y_1507_;
v___y_1489_ = v_fst_1521_;
v___y_1490_ = v___x_1534_;
v___y_1491_ = v___x_1528_;
v___y_1492_ = v_snd_1522_;
v___y_1493_ = v___y_1510_;
v___y_1494_ = v___x_1540_;
goto v___jp_1481_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_x_1511_);
lean_dec(v___y_1510_);
lean_dec(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec(v_tk_1261_);
v_a_1543_ = lean_ctor_get(v___x_1518_, 0);
v_a_1544_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1518_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_inc(v_a_1543_);
lean_dec(v___x_1518_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1543_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_a_1544_);
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
v___jp_1552_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_doElems_1564_; uint8_t v___x_1565_; 
v___x_1562_ = l_Lean_Syntax_getArg(v___y_1558_, v___x_1262_);
v___x_1563_ = l_Lean_Syntax_getArg(v___y_1558_, v___y_1553_);
lean_dec(v___y_1558_);
v_doElems_1564_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1565_ = l_Lean_Syntax_isIdent(v___x_1562_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1562_);
v___x_1567_ = l_Lean_Syntax_isOfKind(v___x_1562_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1562_, v___x_1567_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_a_1570_; lean_object* v_ref_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_n(v_a_1569_, 2);
v_a_1570_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1568_, 2);
v_ref_1571_ = lean_ctor_get(v___y_1560_, 5);
v___x_1572_ = l_Lean_SourceInfo_fromRef(v_ref_1571_, v___x_1567_);
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1574_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1577_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1572_, 15);
v___x_1578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1572_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1572_);
lean_ctor_set(v___x_1580_, 1, v___x_1574_);
lean_ctor_set(v___x_1580_, 2, v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1580_, 4);
v___x_1582_ = l_Lean_Syntax_node2(v___x_1572_, v___x_1581_, v___x_1580_, v_a_1569_);
v___x_1583_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1582_);
v___x_1584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1572_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1588_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1572_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1562_);
v___x_1591_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1590_);
v___x_1592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1572_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_Syntax_node4(v___x_1572_, v___x_1587_, v___x_1589_, v___x_1591_, v___x_1593_, v___y_1555_);
v___x_1595_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1594_);
v___x_1596_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1586_, v___x_1595_);
v___x_1597_ = l_Lean_Syntax_node7(v___x_1572_, v___x_1576_, v___x_1578_, v___x_1580_, v___x_1580_, v___x_1580_, v___x_1583_, v___x_1585_, v___x_1596_);
v___x_1598_ = l_Lean_Syntax_node2(v___x_1572_, v___x_1575_, v___x_1597_, v___x_1580_);
v___x_1599_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1598_);
v___x_1600_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1573_, v___x_1599_);
v___y_1505_ = v_h_x3f_1559_;
v___y_1506_ = v___y_1554_;
v___y_1507_ = v___x_1563_;
v___y_1508_ = v_doElems_1564_;
v___y_1509_ = v___y_1556_;
v___y_1510_ = v___y_1557_;
v_x_1511_ = v_a_1569_;
v_body_1512_ = v___x_1600_;
v___y_1513_ = v___y_1560_;
v___y_1514_ = v_a_1570_;
goto v___jp_1504_;
}
else
{
lean_object* v_a_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v___x_1563_);
lean_dec(v___x_1562_);
lean_dec(v_h_x3f_1559_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec(v_tk_1261_);
v_a_1601_ = lean_ctor_get(v___x_1568_, 0);
v_a_1602_ = lean_ctor_get(v___x_1568_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1568_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_inc(v_a_1601_);
lean_dec(v___x_1568_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1601_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1562_, v___x_1565_, v___y_1560_, v___y_1561_);
lean_dec(v___x_1562_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v_a_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
v_a_1612_ = lean_ctor_get(v___x_1610_, 1);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1610_, 2);
v___y_1505_ = v_h_x3f_1559_;
v___y_1506_ = v___y_1554_;
v___y_1507_ = v___x_1563_;
v___y_1508_ = v_doElems_1564_;
v___y_1509_ = v___y_1556_;
v___y_1510_ = v___y_1557_;
v_x_1511_ = v_a_1611_;
v_body_1512_ = v___y_1555_;
v___y_1513_ = v___y_1560_;
v___y_1514_ = v_a_1612_;
goto v___jp_1504_;
}
else
{
lean_object* v_a_1613_; lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v___x_1563_);
lean_dec(v_h_x3f_1559_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec(v_tk_1261_);
v_a_1613_ = lean_ctor_get(v___x_1610_, 0);
v_a_1614_ = lean_ctor_get(v___x_1610_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1610_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_inc(v_a_1613_);
lean_dec(v___x_1610_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1613_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
v___y_1505_ = v_h_x3f_1559_;
v___y_1506_ = v___y_1554_;
v___y_1507_ = v___x_1563_;
v___y_1508_ = v_doElems_1564_;
v___y_1509_ = v___y_1556_;
v___y_1510_ = v___y_1557_;
v_x_1511_ = v___x_1562_;
v_body_1512_ = v___y_1555_;
v___y_1513_ = v___y_1560_;
v___y_1514_ = v___y_1561_;
goto v___jp_1504_;
}
}
v___jp_1622_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_array_get(v___x_1631_, v___y_1627_, v___x_1151_);
lean_inc(v___x_1632_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v___x_1632_, v___x_1457_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v___x_1632_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v_tk_1261_);
v___x_1634_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1630_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = l_Lean_Syntax_getArg(v___x_1632_, v___x_1151_);
v___x_1636_ = l_Lean_Syntax_isNone(v___x_1635_);
if (v___x_1636_ == 0)
{
uint8_t v___x_1637_; 
lean_inc(v___x_1635_);
v___x_1637_ = l_Lean_Syntax_matchesNull(v___x_1635_, v___y_1623_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_dec(v___x_1635_);
lean_dec(v___x_1632_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec(v_tk_1261_);
v___x_1638_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1630_);
return v___x_1638_;
}
else
{
lean_object* v_h_x3f_1639_; lean_object* v___x_1640_; 
v_h_x3f_1639_ = l_Lean_Syntax_getArg(v___x_1635_, v___x_1151_);
lean_dec(v___x_1635_);
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_h_x3f_1639_);
v___y_1553_ = v___y_1624_;
v___y_1554_ = v___y_1625_;
v___y_1555_ = v___y_1626_;
v___y_1556_ = v___y_1627_;
v___y_1557_ = v___y_1628_;
v___y_1558_ = v___x_1632_;
v_h_x3f_1559_ = v___x_1640_;
v___y_1560_ = v___y_1629_;
v___y_1561_ = v___y_1630_;
goto v___jp_1552_;
}
}
else
{
lean_object* v___x_1641_; 
lean_dec(v___x_1635_);
v___x_1641_ = lean_box(0);
v___y_1553_ = v___y_1624_;
v___y_1554_ = v___y_1625_;
v___y_1555_ = v___y_1626_;
v___y_1556_ = v___y_1627_;
v___y_1557_ = v___y_1628_;
v___y_1558_ = v___x_1632_;
v_h_x3f_1559_ = v___x_1641_;
v___y_1560_ = v___y_1629_;
v___y_1561_ = v___y_1630_;
goto v___jp_1552_;
}
}
}
v___jp_1642_:
{
lean_object* v_decls_1650_; lean_object* v_decls_1651_; 
v_decls_1650_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_1651_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1650_);
lean_dec_ref(v_decls_1650_);
if (lean_obj_tag(v_inv_1645_) == 1)
{
lean_object* v_val_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_val_1652_ = lean_ctor_get(v_inv_1645_, 0);
v___x_1653_ = lean_array_get_size(v_decls_1651_);
v___x_1654_ = lean_nat_dec_lt(v___x_1262_, v___x_1653_);
if (v___x_1654_ == 0)
{
v___y_1623_ = v___y_1643_;
v___y_1624_ = v___y_1644_;
v___y_1625_ = v_inv_1645_;
v___y_1626_ = v_body_1647_;
v___y_1627_ = v_decls_1651_;
v___y_1628_ = v_dec_1646_;
v___y_1629_ = v___y_1648_;
v___y_1630_ = v___y_1649_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1656_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1652_, v___x_1655_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 1);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 2);
v___y_1623_ = v___y_1643_;
v___y_1624_ = v___y_1644_;
v___y_1625_ = v_inv_1645_;
v___y_1626_ = v_body_1647_;
v___y_1627_ = v_decls_1651_;
v___y_1628_ = v_dec_1646_;
v___y_1629_ = v___y_1648_;
v___y_1630_ = v_a_1657_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1658_; lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref_known(v_inv_1645_, 1);
lean_dec_ref(v_decls_1651_);
lean_dec(v_body_1647_);
lean_dec(v_dec_1646_);
lean_dec(v_tk_1261_);
v_a_1658_ = lean_ctor_get(v___x_1656_, 0);
v_a_1659_ = lean_ctor_get(v___x_1656_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1656_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_inc(v_a_1658_);
lean_dec(v___x_1656_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1658_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1659_);
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
else
{
v___y_1623_ = v___y_1643_;
v___y_1624_ = v___y_1644_;
v___y_1625_ = v_inv_1645_;
v___y_1626_ = v_body_1647_;
v___y_1627_ = v_decls_1651_;
v___y_1628_ = v_dec_1646_;
v___y_1629_ = v___y_1648_;
v___y_1630_ = v___y_1649_;
goto v___jp_1622_;
}
}
v___jp_1667_:
{
if (v___y_1673_ == 0)
{
if (v___y_1672_ == 0)
{
lean_object* v___x_1677_; 
lean_dec(v_inv_1674_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1677_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1676_);
return v___x_1677_;
}
else
{
lean_object* v_dec_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_dec_1678_ = l_Lean_Syntax_getArg(v___y_1670_, v___x_1151_);
lean_dec(v___y_1670_);
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1678_);
v___x_1680_ = l_Lean_Syntax_isOfKind(v_dec_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_dec(v_dec_1678_);
lean_dec(v_inv_1674_);
lean_dec(v___y_1669_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1681_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1676_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_dec_1678_);
v___y_1643_ = v___y_1668_;
v___y_1644_ = v___y_1671_;
v_inv_1645_ = v_inv_1674_;
v_dec_1646_ = v___x_1682_;
v_body_1647_ = v___y_1669_;
v___y_1648_ = v___y_1675_;
v___y_1649_ = v___y_1676_;
goto v___jp_1642_;
}
}
}
else
{
lean_object* v___x_1683_; 
lean_dec(v___y_1670_);
v___x_1683_ = lean_box(0);
v___y_1643_ = v___y_1668_;
v___y_1644_ = v___y_1671_;
v_inv_1645_ = v_inv_1674_;
v_dec_1646_ = v___x_1683_;
v_body_1647_ = v___y_1669_;
v___y_1648_ = v___y_1675_;
v___y_1649_ = v___y_1676_;
goto v___jp_1642_;
}
}
v___jp_1684_:
{
if (v___y_1690_ == 0)
{
if (v___y_1689_ == 0)
{
lean_object* v___x_1695_; 
lean_dec(v_inv_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1687_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1695_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1694_);
return v___x_1695_;
}
else
{
if (v___y_1686_ == 0)
{
lean_object* v___x_1696_; 
lean_dec(v_inv_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1687_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1696_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1694_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___y_1687_);
v___y_1643_ = v___y_1685_;
v___y_1644_ = v___y_1688_;
v_inv_1645_ = v_inv_1692_;
v_dec_1646_ = v___x_1697_;
v_body_1647_ = v___y_1691_;
v___y_1648_ = v___y_1693_;
v___y_1649_ = v___y_1694_;
goto v___jp_1642_;
}
}
}
else
{
lean_object* v___x_1698_; 
lean_dec(v___y_1687_);
v___x_1698_ = lean_box(0);
v___y_1643_ = v___y_1685_;
v___y_1644_ = v___y_1688_;
v_inv_1645_ = v_inv_1692_;
v_dec_1646_ = v___x_1698_;
v_body_1647_ = v___y_1691_;
v___y_1648_ = v___y_1693_;
v___y_1649_ = v___y_1694_;
goto v___jp_1642_;
}
}
v___jp_1699_:
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = l_Lean_Syntax_getArg(v_stx_1010_, v___y_1701_);
v___x_1706_ = l_Lean_Syntax_isNone(v___x_1705_);
if (v___x_1706_ == 0)
{
uint8_t v___x_1707_; 
lean_inc(v___x_1705_);
v___x_1707_ = l_Lean_Syntax_matchesNull(v___x_1705_, v___x_1262_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v_body_1709_; uint8_t v___x_1710_; 
v___x_1708_ = lean_unsigned_to_nat(5u);
v_body_1709_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1708_);
lean_dec(v_stx_1010_);
v___x_1710_ = l_Lean_Syntax_isNone(v___y_1702_);
if (v___x_1710_ == 0)
{
uint8_t v___x_1711_; 
lean_inc(v___y_1702_);
v___x_1711_ = l_Lean_Syntax_matchesNull(v___y_1702_, v___x_1262_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_dec(v_body_1709_);
lean_dec(v___x_1705_);
lean_dec(v___y_1702_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1712_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1712_;
}
else
{
lean_object* v_inv_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v_inv_1713_ = l_Lean_Syntax_getArg(v___y_1702_, v___x_1151_);
lean_dec(v___y_1702_);
v___x_1714_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1713_);
v___x_1715_ = l_Lean_Syntax_isOfKind(v_inv_1713_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_dec(v_inv_1713_);
lean_dec(v_body_1709_);
lean_dec(v___x_1705_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1716_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_inv_1713_);
v___y_1668_ = v___y_1700_;
v___y_1669_ = v_body_1709_;
v___y_1670_ = v___x_1705_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___x_1707_;
v___y_1673_ = v___x_1706_;
v_inv_1674_ = v___x_1717_;
v___y_1675_ = v___y_1703_;
v___y_1676_ = v___y_1704_;
goto v___jp_1667_;
}
}
}
else
{
lean_object* v___x_1718_; 
lean_dec(v___y_1702_);
v___x_1718_ = lean_box(0);
v___y_1668_ = v___y_1700_;
v___y_1669_ = v_body_1709_;
v___y_1670_ = v___x_1705_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___x_1707_;
v___y_1673_ = v___x_1706_;
v_inv_1674_ = v___x_1718_;
v___y_1675_ = v___y_1703_;
v___y_1676_ = v___y_1704_;
goto v___jp_1667_;
}
}
else
{
lean_object* v_dec_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v_dec_1719_ = l_Lean_Syntax_getArg(v___x_1705_, v___x_1151_);
lean_dec(v___x_1705_);
v___x_1720_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1719_);
v___x_1721_ = l_Lean_Syntax_isOfKind(v_dec_1719_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v_body_1723_; uint8_t v___x_1724_; 
v___x_1722_ = lean_unsigned_to_nat(5u);
v_body_1723_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1722_);
lean_dec(v_stx_1010_);
v___x_1724_ = l_Lean_Syntax_isNone(v___y_1702_);
if (v___x_1724_ == 0)
{
uint8_t v___x_1725_; 
lean_inc(v___y_1702_);
v___x_1725_ = l_Lean_Syntax_matchesNull(v___y_1702_, v___x_1262_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
lean_dec(v_body_1723_);
lean_dec(v_dec_1719_);
lean_dec(v___y_1702_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1726_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1726_;
}
else
{
lean_object* v_inv_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_inv_1727_ = l_Lean_Syntax_getArg(v___y_1702_, v___x_1151_);
lean_dec(v___y_1702_);
v___x_1728_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1727_);
v___x_1729_ = l_Lean_Syntax_isOfKind(v_inv_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec(v_inv_1727_);
lean_dec(v_body_1723_);
lean_dec(v_dec_1719_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1730_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_inv_1727_);
v___y_1685_ = v___y_1700_;
v___y_1686_ = v___x_1721_;
v___y_1687_ = v_dec_1719_;
v___y_1688_ = v___y_1701_;
v___y_1689_ = v___x_1707_;
v___y_1690_ = v___x_1706_;
v___y_1691_ = v_body_1723_;
v_inv_1692_ = v___x_1731_;
v___y_1693_ = v___y_1703_;
v___y_1694_ = v___y_1704_;
goto v___jp_1684_;
}
}
}
else
{
lean_object* v___x_1732_; 
lean_dec(v___y_1702_);
v___x_1732_ = lean_box(0);
v___y_1685_ = v___y_1700_;
v___y_1686_ = v___x_1721_;
v___y_1687_ = v_dec_1719_;
v___y_1688_ = v___y_1701_;
v___y_1689_ = v___x_1707_;
v___y_1690_ = v___x_1706_;
v___y_1691_ = v_body_1723_;
v_inv_1692_ = v___x_1732_;
v___y_1693_ = v___y_1703_;
v___y_1694_ = v___y_1704_;
goto v___jp_1684_;
}
}
else
{
lean_object* v___x_1733_; 
lean_dec(v_dec_1719_);
lean_dec(v___y_1702_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1733_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1733_;
}
}
}
else
{
lean_object* v___x_1734_; 
lean_dec(v___x_1705_);
lean_dec(v___y_1702_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1734_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1734_;
}
}
v___jp_1735_:
{
lean_object* v___x_1742_; lean_object* v_body_1743_; 
v___x_1742_ = lean_unsigned_to_nat(5u);
v_body_1743_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1742_);
lean_dec(v_stx_1010_);
v___y_1643_ = v___y_1736_;
v___y_1644_ = v___y_1737_;
v_inv_1645_ = v___y_1738_;
v_dec_1646_ = v_dec_1739_;
v_body_1647_ = v_body_1743_;
v___y_1648_ = v___y_1740_;
v___y_1649_ = v___y_1741_;
goto v___jp_1642_;
}
v___jp_1744_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_inc_ref(v___y_1748_);
v___x_1758_ = l_Array_append___redArg(v___y_1748_, v___y_1757_);
lean_dec_ref(v___y_1757_);
lean_inc_n(v___y_1751_, 2);
lean_inc_n(v___y_1746_, 4);
v___x_1759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1759_, 0, v___y_1746_);
lean_ctor_set(v___x_1759_, 1, v___y_1751_);
lean_ctor_set(v___x_1759_, 2, v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1746_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_Syntax_node4(v___y_1746_, v___x_1457_, v___x_1759_, v___y_1747_, v___x_1761_, v___y_1755_);
v___x_1763_ = l_Lean_Syntax_node1(v___y_1746_, v___y_1751_, v___x_1762_);
if (lean_obj_tag(v___y_1756_) == 1)
{
lean_object* v_val_1764_; lean_object* v___x_1765_; 
v_val_1764_ = lean_ctor_get(v___y_1756_, 0);
lean_inc(v_val_1764_);
lean_dec_ref_known(v___y_1756_, 1);
v___x_1765_ = l_Array_mkArray1___redArg(v_val_1764_);
v___y_1228_ = v___y_1745_;
v___y_1229_ = v___y_1746_;
v___y_1230_ = v___y_1748_;
v___y_1231_ = v___y_1750_;
v___y_1232_ = v___x_1763_;
v___y_1233_ = v___y_1749_;
v___y_1234_ = v___y_1751_;
v___y_1235_ = v___y_1754_;
v___y_1236_ = v___y_1753_;
v___y_1237_ = v___y_1752_;
v___y_1238_ = v___x_1765_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1766_; 
lean_dec(v___y_1756_);
v___x_1766_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1228_ = v___y_1745_;
v___y_1229_ = v___y_1746_;
v___y_1230_ = v___y_1748_;
v___y_1231_ = v___y_1750_;
v___y_1232_ = v___x_1763_;
v___y_1233_ = v___y_1749_;
v___y_1234_ = v___y_1751_;
v___y_1235_ = v___y_1754_;
v___y_1236_ = v___y_1753_;
v___y_1237_ = v___y_1752_;
v___y_1238_ = v___x_1766_;
goto v___jp_1227_;
}
}
v___jp_1767_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1779_ = lean_array_get_size(v___y_1770_);
v___x_1780_ = l_Array_toSubarray___redArg(v___y_1770_, v___x_1262_, v___x_1779_);
lean_inc_ref(v___y_1768_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___y_1768_);
lean_ctor_set(v___x_1781_, 1, v_body_1776_);
v___x_1782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_1771_, v___x_1780_, v___x_1781_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v_a_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1805_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
v_a_1784_ = lean_ctor_get(v___x_1782_, 1);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1782_, 2);
v_fst_1785_ = lean_ctor_get(v_a_1783_, 0);
v_snd_1786_ = lean_ctor_get(v_a_1783_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1788_ = v_a_1783_;
v_isShared_1789_ = v_isSharedCheck_1805_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_snd_1786_);
lean_inc(v_fst_1785_);
lean_dec(v_a_1783_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1805_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_ref_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v_ref_1790_ = lean_ctor_get(v___y_1777_, 5);
v___x_1791_ = l_Lean_SourceInfo_fromRef(v_ref_1790_, v___y_1771_);
v___x_1792_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1793_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_1794_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 2);
lean_ctor_set(v___x_1788_, 1, v___x_1794_);
lean_ctor_set(v___x_1788_, 0, v___x_1793_);
v___x_1796_ = v___x_1788_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1798_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1774_) == 1)
{
lean_object* v_val_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_val_1799_ = lean_ctor_get(v___y_1774_, 0);
lean_inc(v_val_1799_);
lean_dec_ref_known(v___y_1774_, 1);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1791_);
v___x_1801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1791_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = l_Array_mkArray2___redArg(v_val_1799_, v___x_1801_);
v___y_1745_ = v___x_1792_;
v___y_1746_ = v___x_1791_;
v___y_1747_ = v_x_1775_;
v___y_1748_ = v___x_1798_;
v___y_1749_ = v_snd_1786_;
v___y_1750_ = v___y_1769_;
v___y_1751_ = v___x_1797_;
v___y_1752_ = v_a_1784_;
v___y_1753_ = v_fst_1785_;
v___y_1754_ = v___x_1796_;
v___y_1755_ = v___y_1772_;
v___y_1756_ = v___y_1773_;
v___y_1757_ = v___x_1802_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1803_; 
lean_dec(v___y_1774_);
v___x_1803_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1745_ = v___x_1792_;
v___y_1746_ = v___x_1791_;
v___y_1747_ = v_x_1775_;
v___y_1748_ = v___x_1798_;
v___y_1749_ = v_snd_1786_;
v___y_1750_ = v___y_1769_;
v___y_1751_ = v___x_1797_;
v___y_1752_ = v_a_1784_;
v___y_1753_ = v_fst_1785_;
v___y_1754_ = v___x_1796_;
v___y_1755_ = v___y_1772_;
v___y_1756_ = v___y_1773_;
v___y_1757_ = v___x_1803_;
goto v___jp_1744_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_x_1775_);
lean_dec(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec(v___y_1769_);
lean_dec(v_tk_1261_);
v_a_1806_ = lean_ctor_get(v___x_1782_, 0);
v_a_1807_ = lean_ctor_get(v___x_1782_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1782_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_inc(v_a_1806_);
lean_dec(v___x_1782_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1806_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
v___jp_1815_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v_doElems_1828_; uint8_t v___x_1829_; 
v___x_1826_ = l_Lean_Syntax_getArg(v___y_1820_, v___x_1262_);
v___x_1827_ = l_Lean_Syntax_getArg(v___y_1820_, v___y_1818_);
lean_dec(v___y_1820_);
v_doElems_1828_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1829_ = l_Lean_Syntax_isIdent(v___x_1826_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1826_);
v___x_1831_ = l_Lean_Syntax_isOfKind(v___x_1826_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1826_, v___y_1821_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v_a_1834_; lean_object* v_ref_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc_n(v_a_1833_, 2);
v_a_1834_ = lean_ctor_get(v___x_1832_, 1);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1832_, 2);
v_ref_1835_ = lean_ctor_get(v___y_1824_, 5);
v___x_1836_ = l_Lean_SourceInfo_fromRef(v_ref_1835_, v___y_1821_);
v___x_1837_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1838_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1839_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1841_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1836_, 15);
v___x_1842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1836_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1836_);
lean_ctor_set(v___x_1844_, 1, v___x_1838_);
lean_ctor_set(v___x_1844_, 2, v___x_1843_);
v___x_1845_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1844_, 4);
v___x_1846_ = l_Lean_Syntax_node2(v___x_1836_, v___x_1845_, v___x_1844_, v_a_1833_);
v___x_1847_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1836_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1851_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1852_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1836_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1826_);
v___x_1855_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1854_);
v___x_1856_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1836_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = l_Lean_Syntax_node4(v___x_1836_, v___x_1851_, v___x_1853_, v___x_1855_, v___x_1857_, v___y_1816_);
v___x_1859_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1858_);
v___x_1860_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1850_, v___x_1859_);
v___x_1861_ = l_Lean_Syntax_node7(v___x_1836_, v___x_1840_, v___x_1842_, v___x_1844_, v___x_1844_, v___x_1844_, v___x_1847_, v___x_1849_, v___x_1860_);
v___x_1862_ = l_Lean_Syntax_node2(v___x_1836_, v___x_1839_, v___x_1861_, v___x_1844_);
v___x_1863_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1862_);
v___x_1864_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1837_, v___x_1863_);
v___y_1768_ = v_doElems_1828_;
v___y_1769_ = v___y_1817_;
v___y_1770_ = v___y_1819_;
v___y_1771_ = v___y_1821_;
v___y_1772_ = v___x_1827_;
v___y_1773_ = v___y_1822_;
v___y_1774_ = v_h_x3f_1823_;
v_x_1775_ = v_a_1833_;
v_body_1776_ = v___x_1864_;
v___y_1777_ = v___y_1824_;
v___y_1778_ = v_a_1834_;
goto v___jp_1767_;
}
else
{
lean_object* v_a_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v___x_1827_);
lean_dec(v___x_1826_);
lean_dec(v_h_x3f_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec(v_tk_1261_);
v_a_1865_ = lean_ctor_get(v___x_1832_, 0);
v_a_1866_ = lean_ctor_get(v___x_1832_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1832_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_inc(v_a_1865_);
lean_dec(v___x_1832_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1865_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_a_1866_);
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
v___x_1874_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1826_, v___y_1821_, v___y_1824_, v___y_1825_);
lean_dec(v___x_1826_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v_a_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
v_a_1876_ = lean_ctor_get(v___x_1874_, 1);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1874_, 2);
v___y_1768_ = v_doElems_1828_;
v___y_1769_ = v___y_1817_;
v___y_1770_ = v___y_1819_;
v___y_1771_ = v___y_1821_;
v___y_1772_ = v___x_1827_;
v___y_1773_ = v___y_1822_;
v___y_1774_ = v_h_x3f_1823_;
v_x_1775_ = v_a_1875_;
v_body_1776_ = v___y_1816_;
v___y_1777_ = v___y_1824_;
v___y_1778_ = v_a_1876_;
goto v___jp_1767_;
}
else
{
lean_object* v_a_1877_; lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v___x_1827_);
lean_dec(v_h_x3f_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec(v_tk_1261_);
v_a_1877_ = lean_ctor_get(v___x_1874_, 0);
v_a_1878_ = lean_ctor_get(v___x_1874_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1874_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_inc(v_a_1877_);
lean_dec(v___x_1874_);
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
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1877_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_a_1878_);
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
else
{
v___y_1768_ = v_doElems_1828_;
v___y_1769_ = v___y_1817_;
v___y_1770_ = v___y_1819_;
v___y_1771_ = v___y_1821_;
v___y_1772_ = v___x_1827_;
v___y_1773_ = v___y_1822_;
v___y_1774_ = v_h_x3f_1823_;
v_x_1775_ = v___x_1826_;
v_body_1776_ = v___y_1816_;
v___y_1777_ = v___y_1824_;
v___y_1778_ = v___y_1825_;
goto v___jp_1767_;
}
}
v___jp_1886_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_array_get(v___x_1896_, v___y_1891_, v___x_1151_);
lean_inc(v___x_1897_);
v___x_1898_ = l_Lean_Syntax_isOfKind(v___x_1897_, v___x_1457_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_dec(v___x_1897_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1889_);
lean_dec(v___y_1887_);
lean_dec(v_tk_1261_);
v___x_1899_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1895_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = l_Lean_Syntax_getArg(v___x_1897_, v___x_1151_);
v___x_1901_ = l_Lean_Syntax_isNone(v___x_1900_);
if (v___x_1901_ == 0)
{
uint8_t v___x_1902_; 
lean_inc(v___x_1900_);
v___x_1902_ = l_Lean_Syntax_matchesNull(v___x_1900_, v___y_1888_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_dec(v___x_1900_);
lean_dec(v___x_1897_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1889_);
lean_dec(v___y_1887_);
lean_dec(v_tk_1261_);
v___x_1903_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1895_);
return v___x_1903_;
}
else
{
lean_object* v_h_x3f_1904_; lean_object* v___x_1905_; 
v_h_x3f_1904_ = l_Lean_Syntax_getArg(v___x_1900_, v___x_1151_);
lean_dec(v___x_1900_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_h_x3f_1904_);
v___y_1816_ = v___y_1887_;
v___y_1817_ = v___y_1889_;
v___y_1818_ = v___y_1890_;
v___y_1819_ = v___y_1891_;
v___y_1820_ = v___x_1897_;
v___y_1821_ = v___y_1892_;
v___y_1822_ = v___y_1893_;
v_h_x3f_1823_ = v___x_1905_;
v___y_1824_ = v___y_1894_;
v___y_1825_ = v___y_1895_;
goto v___jp_1815_;
}
}
else
{
lean_object* v___x_1906_; 
lean_dec(v___x_1900_);
v___x_1906_ = lean_box(0);
v___y_1816_ = v___y_1887_;
v___y_1817_ = v___y_1889_;
v___y_1818_ = v___y_1890_;
v___y_1819_ = v___y_1891_;
v___y_1820_ = v___x_1897_;
v___y_1821_ = v___y_1892_;
v___y_1822_ = v___y_1893_;
v_h_x3f_1823_ = v___x_1906_;
v___y_1824_ = v___y_1894_;
v___y_1825_ = v___y_1895_;
goto v___jp_1815_;
}
}
}
v___jp_1907_:
{
lean_object* v___x_1915_; lean_object* v_body_1916_; lean_object* v_decls_1917_; lean_object* v_decls_1918_; 
v___x_1915_ = lean_unsigned_to_nat(5u);
v_body_1916_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1915_);
lean_dec(v_stx_1010_);
v_decls_1917_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_1918_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1917_);
lean_dec_ref(v_decls_1917_);
if (lean_obj_tag(v___y_1911_) == 1)
{
lean_object* v_val_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v_val_1919_ = lean_ctor_get(v___y_1911_, 0);
v___x_1920_ = lean_array_get_size(v_decls_1918_);
v___x_1921_ = lean_nat_dec_lt(v___x_1262_, v___x_1920_);
if (v___x_1921_ == 0)
{
v___y_1887_ = v_body_1916_;
v___y_1888_ = v___y_1908_;
v___y_1889_ = v_dec_1912_;
v___y_1890_ = v___y_1909_;
v___y_1891_ = v_decls_1918_;
v___y_1892_ = v___y_1910_;
v___y_1893_ = v___y_1911_;
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___y_1914_;
goto v___jp_1886_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1923_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1919_, v___x_1922_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 1);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 2);
v___y_1887_ = v_body_1916_;
v___y_1888_ = v___y_1908_;
v___y_1889_ = v_dec_1912_;
v___y_1890_ = v___y_1909_;
v___y_1891_ = v_decls_1918_;
v___y_1892_ = v___y_1910_;
v___y_1893_ = v___y_1911_;
v___y_1894_ = v___y_1913_;
v___y_1895_ = v_a_1924_;
goto v___jp_1886_;
}
else
{
lean_object* v_a_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref_known(v___y_1911_, 1);
lean_dec_ref(v_decls_1918_);
lean_dec(v_body_1916_);
lean_dec(v_dec_1912_);
lean_dec(v_tk_1261_);
v_a_1925_ = lean_ctor_get(v___x_1923_, 0);
v_a_1926_ = lean_ctor_get(v___x_1923_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1923_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_inc(v_a_1925_);
lean_dec(v___x_1923_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1925_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
else
{
v___y_1887_ = v_body_1916_;
v___y_1888_ = v___y_1908_;
v___y_1889_ = v_dec_1912_;
v___y_1890_ = v___y_1909_;
v___y_1891_ = v_decls_1918_;
v___y_1892_ = v___y_1910_;
v___y_1893_ = v___y_1911_;
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___y_1914_;
goto v___jp_1886_;
}
}
v___jp_1934_:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = l_Lean_Syntax_getArg(v_stx_1010_, v___y_1936_);
v___x_1942_ = l_Lean_Syntax_isNone(v___x_1941_);
if (v___x_1942_ == 0)
{
uint8_t v___x_1943_; 
lean_inc(v___x_1941_);
v___x_1943_ = l_Lean_Syntax_matchesNull(v___x_1941_, v___x_1262_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v___x_1941_);
lean_dec(v_inv_1938_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1944_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1940_);
return v___x_1944_;
}
else
{
lean_object* v_dec_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v_dec_1945_ = l_Lean_Syntax_getArg(v___x_1941_, v___x_1151_);
lean_dec(v___x_1941_);
v___x_1946_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1945_);
v___x_1947_ = l_Lean_Syntax_isOfKind(v_dec_1945_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; 
lean_dec(v_dec_1945_);
lean_dec(v_inv_1938_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1948_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1940_);
return v___x_1948_;
}
else
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_dec_1945_);
v___y_1908_ = v___y_1935_;
v___y_1909_ = v___y_1936_;
v___y_1910_ = v___y_1937_;
v___y_1911_ = v_inv_1938_;
v_dec_1912_ = v___x_1949_;
v___y_1913_ = v___y_1939_;
v___y_1914_ = v___y_1940_;
goto v___jp_1907_;
}
}
}
else
{
lean_object* v___x_1950_; 
lean_dec(v___x_1941_);
v___x_1950_ = lean_box(0);
v___y_1908_ = v___y_1935_;
v___y_1909_ = v___y_1936_;
v___y_1910_ = v___y_1937_;
v___y_1911_ = v_inv_1938_;
v_dec_1912_ = v___x_1950_;
v___y_1913_ = v___y_1939_;
v___y_1914_ = v___y_1940_;
goto v___jp_1907_;
}
}
v___jp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1954_ = l_Lean_Syntax_getArg(v___x_1456_, v___x_1262_);
lean_dec(v___x_1456_);
v___x_1955_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__21));
v___x_1956_ = l_Lean_Syntax_isOfKind(v___x_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1957_ = lean_unsigned_to_nat(2u);
v___x_1958_ = lean_unsigned_to_nat(3u);
v___x_1959_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1957_);
v___x_1960_ = l_Lean_Syntax_isNone(v___x_1959_);
if (v___x_1960_ == 0)
{
uint8_t v___x_1961_; 
lean_inc(v___x_1959_);
v___x_1961_ = l_Lean_Syntax_matchesNull(v___x_1959_, v___x_1262_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_dec(v___x_1959_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1962_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1962_;
}
else
{
lean_object* v_inv_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_inv_1963_ = l_Lean_Syntax_getArg(v___x_1959_, v___x_1151_);
lean_dec(v___x_1959_);
v___x_1964_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1963_);
v___x_1965_ = l_Lean_Syntax_isOfKind(v_inv_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec(v_inv_1963_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1966_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_inv_1963_);
v___y_1935_ = v___x_1957_;
v___y_1936_ = v___x_1958_;
v___y_1937_ = v___x_1956_;
v_inv_1938_ = v___x_1967_;
v___y_1939_ = v___y_1952_;
v___y_1940_ = v___y_1953_;
goto v___jp_1934_;
}
}
}
else
{
lean_object* v___x_1968_; 
lean_dec(v___x_1959_);
v___x_1968_ = lean_box(0);
v___y_1935_ = v___x_1957_;
v___y_1936_ = v___x_1958_;
v___y_1937_ = v___x_1956_;
v_inv_1938_ = v___x_1968_;
v___y_1939_ = v___y_1952_;
v___y_1940_ = v___y_1953_;
goto v___jp_1934_;
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1969_ = lean_unsigned_to_nat(2u);
v___x_1970_ = lean_unsigned_to_nat(3u);
v___x_1971_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1969_);
v___x_1972_ = l_Lean_Syntax_isNone(v___x_1971_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
lean_inc(v___x_1971_);
v___x_1973_ = l_Lean_Syntax_matchesNull(v___x_1971_, v___x_1262_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec(v___x_1971_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1974_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1974_;
}
else
{
lean_object* v_inv_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_inv_1975_ = l_Lean_Syntax_getArg(v___x_1971_, v___x_1151_);
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1975_);
v___x_1977_ = l_Lean_Syntax_isOfKind(v_inv_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_dec(v___x_1971_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_inv_1975_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1978_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_inv_1975_);
v___x_1980_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1970_);
v___x_1981_ = l_Lean_Syntax_isNone(v___x_1980_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
lean_inc(v___x_1980_);
v___x_1982_ = l_Lean_Syntax_matchesNull(v___x_1980_, v___x_1262_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_dec(v___x_1980_);
lean_dec_ref_known(v___x_1979_, 1);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1983_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1983_;
}
else
{
lean_object* v_dec_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_dec_1984_ = l_Lean_Syntax_getArg(v___x_1980_, v___x_1151_);
lean_dec(v___x_1980_);
v___x_1985_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1984_);
v___x_1986_ = l_Lean_Syntax_isOfKind(v_dec_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
lean_dec(v_dec_1984_);
lean_dec_ref_known(v___x_1979_, 1);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1987_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_dec_1984_);
v___y_1736_ = v___x_1969_;
v___y_1737_ = v___x_1970_;
v___y_1738_ = v___x_1979_;
v_dec_1739_ = v___x_1988_;
v___y_1740_ = v___y_1952_;
v___y_1741_ = v___y_1953_;
goto v___jp_1735_;
}
}
}
else
{
lean_object* v___x_1989_; 
lean_dec(v___x_1980_);
v___x_1989_ = lean_box(0);
v___y_1736_ = v___x_1969_;
v___y_1737_ = v___x_1970_;
v___y_1738_ = v___x_1979_;
v_dec_1739_ = v___x_1989_;
v___y_1740_ = v___y_1952_;
v___y_1741_ = v___y_1953_;
goto v___jp_1735_;
}
}
}
else
{
lean_dec(v_inv_1975_);
v___y_1700_ = v___x_1969_;
v___y_1701_ = v___x_1970_;
v___y_1702_ = v___x_1971_;
v___y_1703_ = v___y_1952_;
v___y_1704_ = v___y_1953_;
goto v___jp_1699_;
}
}
}
else
{
v___y_1700_ = v___x_1969_;
v___y_1701_ = v___x_1970_;
v___y_1702_ = v___x_1971_;
v___y_1703_ = v___y_1952_;
v___y_1704_ = v___y_1953_;
goto v___jp_1699_;
}
}
}
v___jp_1990_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_inc_ref(v___y_2001_);
v___x_2004_ = l_Array_append___redArg(v___y_2001_, v___y_2003_);
lean_dec_ref(v___y_2003_);
lean_inc_n(v___y_1997_, 2);
lean_inc_n(v___y_2000_, 4);
v___x_2005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2005_, 0, v___y_2000_);
lean_ctor_set(v___x_2005_, 1, v___y_1997_);
lean_ctor_set(v___x_2005_, 2, v___x_2004_);
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_2007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___y_2000_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_Syntax_node4(v___y_2000_, v___x_1457_, v___x_2005_, v___y_1992_, v___x_2007_, v___y_2002_);
v___x_2009_ = l_Lean_Syntax_node1(v___y_2000_, v___y_1997_, v___x_2008_);
if (lean_obj_tag(v___y_1996_) == 1)
{
lean_object* v_val_2010_; lean_object* v___x_2011_; 
v_val_2010_ = lean_ctor_get(v___y_1996_, 0);
lean_inc(v_val_2010_);
lean_dec_ref_known(v___y_1996_, 1);
v___x_2011_ = l_Array_mkArray1___redArg(v_val_2010_);
v___y_1153_ = v___y_1991_;
v___y_1154_ = v___y_1993_;
v___y_1155_ = v___y_1994_;
v___y_1156_ = v___y_1995_;
v___y_1157_ = v___x_2009_;
v___y_1158_ = v___y_1997_;
v___y_1159_ = v___y_1998_;
v___y_1160_ = v___y_1999_;
v___y_1161_ = v___y_2000_;
v___y_1162_ = v___y_2001_;
v___y_1163_ = v___x_2011_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_2012_; 
lean_dec(v___y_1996_);
v___x_2012_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1153_ = v___y_1991_;
v___y_1154_ = v___y_1993_;
v___y_1155_ = v___y_1994_;
v___y_1156_ = v___y_1995_;
v___y_1157_ = v___x_2009_;
v___y_1158_ = v___y_1997_;
v___y_1159_ = v___y_1998_;
v___y_1160_ = v___y_1999_;
v___y_1161_ = v___y_2000_;
v___y_1162_ = v___y_2001_;
v___y_1163_ = v___x_2012_;
goto v___jp_1152_;
}
}
v___jp_2014_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2025_ = lean_array_get_size(v___y_2015_);
v___x_2026_ = l_Array_toSubarray___redArg(v___y_2015_, v___x_1262_, v___x_2025_);
lean_inc_ref(v___y_2017_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___y_2017_);
lean_ctor_set(v___x_2027_, 1, v_body_2022_);
v___x_2028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_2013_, v___x_2026_, v___x_2027_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v_a_2030_; lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2051_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
v_a_2030_ = lean_ctor_get(v___x_2028_, 1);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2028_, 2);
v_fst_2031_ = lean_ctor_get(v_a_2029_, 0);
v_snd_2032_ = lean_ctor_get(v_a_2029_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_2029_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2034_ = v_a_2029_;
v_isShared_2035_ = v_isSharedCheck_2051_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_snd_2032_);
lean_inc(v_fst_2031_);
lean_dec(v_a_2029_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2051_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_ref_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v_ref_2036_ = lean_ctor_get(v___y_2023_, 5);
v___x_2037_ = l_Lean_SourceInfo_fromRef(v_ref_2036_, v___x_2013_);
v___x_2038_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_2039_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_2040_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 2);
lean_ctor_set(v___x_2034_, 1, v___x_2040_);
lean_ctor_set(v___x_2034_, 0, v___x_2039_);
v___x_2042_ = v___x_2034_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2044_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_2018_) == 1)
{
lean_object* v_val_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_val_2045_ = lean_ctor_get(v___y_2018_, 0);
lean_inc(v_val_2045_);
lean_dec_ref_known(v___y_2018_, 1);
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_2037_);
v___x_2047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2037_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = l_Array_mkArray2___redArg(v_val_2045_, v___x_2047_);
v___y_1991_ = v_fst_2031_;
v___y_1992_ = v_x_2021_;
v___y_1993_ = v___x_2042_;
v___y_1994_ = v___y_2016_;
v___y_1995_ = v_a_2030_;
v___y_1996_ = v___y_2019_;
v___y_1997_ = v___x_2043_;
v___y_1998_ = v_snd_2032_;
v___y_1999_ = v___x_2038_;
v___y_2000_ = v___x_2037_;
v___y_2001_ = v___x_2044_;
v___y_2002_ = v___y_2020_;
v___y_2003_ = v___x_2048_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2049_; 
lean_dec(v___y_2018_);
v___x_2049_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1991_ = v_fst_2031_;
v___y_1992_ = v_x_2021_;
v___y_1993_ = v___x_2042_;
v___y_1994_ = v___y_2016_;
v___y_1995_ = v_a_2030_;
v___y_1996_ = v___y_2019_;
v___y_1997_ = v___x_2043_;
v___y_1998_ = v_snd_2032_;
v___y_1999_ = v___x_2038_;
v___y_2000_ = v___x_2037_;
v___y_2001_ = v___x_2044_;
v___y_2002_ = v___y_2020_;
v___y_2003_ = v___x_2049_;
goto v___jp_1990_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_x_2021_);
lean_dec(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec(v___y_2016_);
lean_dec(v_tk_1261_);
v_a_2052_ = lean_ctor_get(v___x_2028_, 0);
v_a_2053_ = lean_ctor_get(v___x_2028_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2028_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_inc(v_a_2052_);
lean_dec(v___x_2028_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2052_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
v___jp_2061_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_doElems_2073_; uint8_t v___x_2074_; 
v___x_2071_ = l_Lean_Syntax_getArg(v___y_2066_, v___x_1262_);
v___x_2072_ = l_Lean_Syntax_getArg(v___y_2066_, v___y_2067_);
lean_dec(v___y_2066_);
v_doElems_2073_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_2074_ = l_Lean_Syntax_isIdent(v___x_2071_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_2071_);
v___x_2076_ = l_Lean_Syntax_isOfKind(v___x_2071_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_2071_, v___x_2076_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v_a_2079_; lean_object* v_ref_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc_n(v_a_2078_, 2);
v_a_2079_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2077_, 2);
v_ref_2080_ = lean_ctor_get(v___y_2069_, 5);
v___x_2081_ = l_Lean_SourceInfo_fromRef(v_ref_2080_, v___x_2076_);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_2083_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2084_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_2085_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_2086_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_2081_, 15);
v___x_2087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2081_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2081_);
lean_ctor_set(v___x_2089_, 1, v___x_2083_);
lean_ctor_set(v___x_2089_, 2, v___x_2088_);
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_2089_, 4);
v___x_2091_ = l_Lean_Syntax_node2(v___x_2081_, v___x_2090_, v___x_2089_, v_a_2078_);
v___x_2092_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2091_);
v___x_2093_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2081_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_2096_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_2097_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_2098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2081_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2071_);
v___x_2100_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2099_);
v___x_2101_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2081_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = l_Lean_Syntax_node4(v___x_2081_, v___x_2096_, v___x_2098_, v___x_2100_, v___x_2102_, v___y_2063_);
v___x_2104_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2103_);
v___x_2105_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2095_, v___x_2104_);
v___x_2106_ = l_Lean_Syntax_node7(v___x_2081_, v___x_2085_, v___x_2087_, v___x_2089_, v___x_2089_, v___x_2089_, v___x_2092_, v___x_2094_, v___x_2105_);
v___x_2107_ = l_Lean_Syntax_node2(v___x_2081_, v___x_2084_, v___x_2106_, v___x_2089_);
v___x_2108_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2107_);
v___x_2109_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2082_, v___x_2108_);
v___y_2015_ = v___y_2062_;
v___y_2016_ = v___y_2064_;
v___y_2017_ = v_doElems_2073_;
v___y_2018_ = v_h_x3f_2068_;
v___y_2019_ = v___y_2065_;
v___y_2020_ = v___x_2072_;
v_x_2021_ = v_a_2078_;
v_body_2022_ = v___x_2109_;
v___y_2023_ = v___y_2069_;
v___y_2024_ = v_a_2079_;
goto v___jp_2014_;
}
else
{
lean_object* v_a_2110_; lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v___x_2072_);
lean_dec(v___x_2071_);
lean_dec(v_h_x3f_2068_);
lean_dec(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v_tk_1261_);
v_a_2110_ = lean_ctor_get(v___x_2077_, 0);
v_a_2111_ = lean_ctor_get(v___x_2077_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2077_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_inc(v_a_2110_);
lean_dec(v___x_2077_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2110_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_2071_, v___x_2074_, v___y_2069_, v___y_2070_);
lean_dec(v___x_2071_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v_a_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
v_a_2121_ = lean_ctor_get(v___x_2119_, 1);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2119_, 2);
v___y_2015_ = v___y_2062_;
v___y_2016_ = v___y_2064_;
v___y_2017_ = v_doElems_2073_;
v___y_2018_ = v_h_x3f_2068_;
v___y_2019_ = v___y_2065_;
v___y_2020_ = v___x_2072_;
v_x_2021_ = v_a_2120_;
v_body_2022_ = v___y_2063_;
v___y_2023_ = v___y_2069_;
v___y_2024_ = v_a_2121_;
goto v___jp_2014_;
}
else
{
lean_object* v_a_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v___x_2072_);
lean_dec(v_h_x3f_2068_);
lean_dec(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v_tk_1261_);
v_a_2122_ = lean_ctor_get(v___x_2119_, 0);
v_a_2123_ = lean_ctor_get(v___x_2119_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2119_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_inc(v_a_2122_);
lean_dec(v___x_2119_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2122_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
else
{
v___y_2015_ = v___y_2062_;
v___y_2016_ = v___y_2064_;
v___y_2017_ = v_doElems_2073_;
v___y_2018_ = v_h_x3f_2068_;
v___y_2019_ = v___y_2065_;
v___y_2020_ = v___x_2072_;
v_x_2021_ = v___x_2071_;
v_body_2022_ = v___y_2063_;
v___y_2023_ = v___y_2069_;
v___y_2024_ = v___y_2070_;
goto v___jp_2014_;
}
}
}
v___jp_1152_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_inc_ref(v___y_1162_);
v___x_1164_ = l_Array_append___redArg(v___y_1162_, v___y_1163_);
lean_dec_ref(v___y_1163_);
lean_inc(v___y_1158_);
lean_inc(v___y_1161_);
v___x_1165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1165_, 0, v___y_1161_);
lean_ctor_set(v___x_1165_, 1, v___y_1158_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
if (lean_obj_tag(v___y_1155_) == 1)
{
lean_object* v_val_1166_; lean_object* v___x_1167_; 
v_val_1166_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v___y_1155_, 1);
v___x_1167_ = l_Array_mkArray1___redArg(v_val_1166_);
v___y_1123_ = v___y_1153_;
v___y_1124_ = v___y_1154_;
v___y_1125_ = v___x_1165_;
v___y_1126_ = v___y_1156_;
v___y_1127_ = v___y_1157_;
v___y_1128_ = v___y_1158_;
v___y_1129_ = v___y_1159_;
v___y_1130_ = v___y_1160_;
v___y_1131_ = v___y_1161_;
v___y_1132_ = v___y_1162_;
v___y_1133_ = v___x_1167_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1168_; 
lean_dec(v___y_1155_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1123_ = v___y_1153_;
v___y_1124_ = v___y_1154_;
v___y_1125_ = v___x_1165_;
v___y_1126_ = v___y_1156_;
v___y_1127_ = v___y_1157_;
v___y_1128_ = v___y_1158_;
v___y_1129_ = v___y_1159_;
v___y_1130_ = v___y_1160_;
v___y_1131_ = v___y_1161_;
v___y_1132_ = v___y_1162_;
v___y_1133_ = v___x_1168_;
goto v___jp_1122_;
}
}
v___jp_1169_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_inc_ref(v___y_1177_);
v___x_1181_ = l_Array_append___redArg(v___y_1177_, v___y_1180_);
lean_dec_ref(v___y_1180_);
lean_inc(v___y_1174_);
lean_inc(v___y_1173_);
v___x_1182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1182_, 0, v___y_1173_);
lean_ctor_set(v___x_1182_, 1, v___y_1174_);
lean_ctor_set(v___x_1182_, 2, v___x_1181_);
if (lean_obj_tag(v___y_1176_) == 1)
{
lean_object* v_val_1183_; lean_object* v___x_1184_; 
v_val_1183_ = lean_ctor_get(v___y_1176_, 0);
lean_inc(v_val_1183_);
lean_dec_ref_known(v___y_1176_, 1);
v___x_1184_ = l_Array_mkArray1___redArg(v_val_1183_);
v___y_1096_ = v___y_1170_;
v___y_1097_ = v___y_1171_;
v___y_1098_ = v___y_1172_;
v___y_1099_ = v___x_1182_;
v___y_1100_ = v___y_1173_;
v___y_1101_ = v___y_1174_;
v___y_1102_ = v___y_1175_;
v___y_1103_ = v___y_1177_;
v___y_1104_ = v___y_1178_;
v___y_1105_ = v___y_1179_;
v___y_1106_ = v___x_1184_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1185_; 
lean_dec(v___y_1176_);
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1096_ = v___y_1170_;
v___y_1097_ = v___y_1171_;
v___y_1098_ = v___y_1172_;
v___y_1099_ = v___x_1182_;
v___y_1100_ = v___y_1173_;
v___y_1101_ = v___y_1174_;
v___y_1102_ = v___y_1175_;
v___y_1103_ = v___y_1177_;
v___y_1104_ = v___y_1178_;
v___y_1105_ = v___y_1179_;
v___y_1106_ = v___x_1185_;
goto v___jp_1095_;
}
}
v___jp_1186_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc_ref(v___y_1196_);
v___x_1201_ = l_Array_append___redArg(v___y_1196_, v___y_1200_);
lean_dec_ref(v___y_1200_);
lean_inc_n(v___y_1188_, 2);
lean_inc_n(v___y_1193_, 4);
v___x_1202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1193_);
lean_ctor_set(v___x_1202_, 1, v___y_1188_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___y_1193_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
lean_inc(v___y_1194_);
v___x_1205_ = l_Lean_Syntax_node4(v___y_1193_, v___y_1194_, v___x_1202_, v___y_1197_, v___x_1204_, v___y_1195_);
v___x_1206_ = l_Lean_Syntax_node1(v___y_1193_, v___y_1188_, v___x_1205_);
if (lean_obj_tag(v___y_1198_) == 1)
{
lean_object* v_val_1207_; lean_object* v___x_1208_; 
v_val_1207_ = lean_ctor_get(v___y_1198_, 0);
lean_inc(v_val_1207_);
lean_dec_ref_known(v___y_1198_, 1);
v___x_1208_ = l_Array_mkArray1___redArg(v_val_1207_);
v___y_1170_ = v___x_1206_;
v___y_1171_ = v___y_1187_;
v___y_1172_ = v___y_1192_;
v___y_1173_ = v___y_1193_;
v___y_1174_ = v___y_1188_;
v___y_1175_ = v___y_1189_;
v___y_1176_ = v___y_1190_;
v___y_1177_ = v___y_1196_;
v___y_1178_ = v___y_1191_;
v___y_1179_ = v___y_1199_;
v___y_1180_ = v___x_1208_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1209_; 
lean_dec(v___y_1198_);
v___x_1209_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1170_ = v___x_1206_;
v___y_1171_ = v___y_1187_;
v___y_1172_ = v___y_1192_;
v___y_1173_ = v___y_1193_;
v___y_1174_ = v___y_1188_;
v___y_1175_ = v___y_1189_;
v___y_1176_ = v___y_1190_;
v___y_1177_ = v___y_1196_;
v___y_1178_ = v___y_1191_;
v___y_1179_ = v___y_1199_;
v___y_1180_ = v___x_1209_;
goto v___jp_1169_;
}
}
v___jp_1210_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_inc_ref(v___y_1212_);
v___x_1222_ = l_Array_append___redArg(v___y_1212_, v___y_1221_);
lean_dec_ref(v___y_1221_);
lean_inc(v___y_1217_);
lean_inc(v___y_1218_);
v___x_1223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1223_, 0, v___y_1218_);
lean_ctor_set(v___x_1223_, 1, v___y_1217_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
if (lean_obj_tag(v___y_1219_) == 1)
{
lean_object* v_val_1224_; lean_object* v___x_1225_; 
v_val_1224_ = lean_ctor_get(v___y_1219_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v___y_1219_, 1);
v___x_1225_ = l_Array_mkArray1___redArg(v_val_1224_);
v___y_1042_ = v___y_1211_;
v___y_1043_ = v___x_1223_;
v___y_1044_ = v___y_1212_;
v___y_1045_ = v___y_1213_;
v___y_1046_ = v___y_1214_;
v___y_1047_ = v___y_1215_;
v___y_1048_ = v___y_1216_;
v___y_1049_ = v___y_1217_;
v___y_1050_ = v___y_1218_;
v___y_1051_ = v___y_1220_;
v___y_1052_ = v___x_1225_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1226_; 
lean_dec(v___y_1219_);
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1042_ = v___y_1211_;
v___y_1043_ = v___x_1223_;
v___y_1044_ = v___y_1212_;
v___y_1045_ = v___y_1213_;
v___y_1046_ = v___y_1214_;
v___y_1047_ = v___y_1215_;
v___y_1048_ = v___y_1216_;
v___y_1049_ = v___y_1217_;
v___y_1050_ = v___y_1218_;
v___y_1051_ = v___y_1220_;
v___y_1052_ = v___x_1226_;
goto v___jp_1041_;
}
}
v___jp_1227_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_inc_ref(v___y_1230_);
v___x_1239_ = l_Array_append___redArg(v___y_1230_, v___y_1238_);
lean_dec_ref(v___y_1238_);
lean_inc(v___y_1234_);
lean_inc(v___y_1229_);
v___x_1240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1229_);
lean_ctor_set(v___x_1240_, 1, v___y_1234_);
lean_ctor_set(v___x_1240_, 2, v___x_1239_);
if (lean_obj_tag(v___y_1231_) == 1)
{
lean_object* v_val_1241_; lean_object* v___x_1242_; 
v_val_1241_ = lean_ctor_get(v___y_1231_, 0);
lean_inc(v_val_1241_);
lean_dec_ref_known(v___y_1231_, 1);
v___x_1242_ = l_Array_mkArray1___redArg(v_val_1241_);
v___y_1069_ = v___y_1228_;
v___y_1070_ = v___y_1229_;
v___y_1071_ = v___x_1240_;
v___y_1072_ = v___y_1230_;
v___y_1073_ = v___y_1233_;
v___y_1074_ = v___y_1232_;
v___y_1075_ = v___y_1234_;
v___y_1076_ = v___y_1237_;
v___y_1077_ = v___y_1236_;
v___y_1078_ = v___y_1235_;
v___y_1079_ = v___x_1242_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1243_; 
lean_dec(v___y_1231_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1069_ = v___y_1228_;
v___y_1070_ = v___y_1229_;
v___y_1071_ = v___x_1240_;
v___y_1072_ = v___y_1230_;
v___y_1073_ = v___y_1233_;
v___y_1074_ = v___y_1232_;
v___y_1075_ = v___y_1234_;
v___y_1076_ = v___y_1237_;
v___y_1077_ = v___y_1236_;
v___y_1078_ = v___y_1235_;
v___y_1079_ = v___x_1243_;
goto v___jp_1068_;
}
}
v___jp_1244_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc_ref(v___y_1249_);
v___x_1256_ = l_Array_append___redArg(v___y_1249_, v___y_1255_);
lean_dec_ref(v___y_1255_);
lean_inc(v___y_1245_);
lean_inc(v___y_1250_);
v___x_1257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1250_);
lean_ctor_set(v___x_1257_, 1, v___y_1245_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
if (lean_obj_tag(v___y_1254_) == 1)
{
lean_object* v_val_1258_; lean_object* v___x_1259_; 
v_val_1258_ = lean_ctor_get(v___y_1254_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v___y_1254_, 1);
v___x_1259_ = l_Array_mkArray1___redArg(v_val_1258_);
v___y_1015_ = v___y_1245_;
v___y_1016_ = v___x_1257_;
v___y_1017_ = v___y_1246_;
v___y_1018_ = v___y_1247_;
v___y_1019_ = v___y_1248_;
v___y_1020_ = v___y_1249_;
v___y_1021_ = v___y_1250_;
v___y_1022_ = v___y_1251_;
v___y_1023_ = v___y_1253_;
v___y_1024_ = v___y_1252_;
v___y_1025_ = v___x_1259_;
goto v___jp_1014_;
}
else
{
lean_object* v___x_1260_; 
lean_dec(v___y_1254_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1015_ = v___y_1245_;
v___y_1016_ = v___x_1257_;
v___y_1017_ = v___y_1246_;
v___y_1018_ = v___y_1247_;
v___y_1019_ = v___y_1248_;
v___y_1020_ = v___y_1249_;
v___y_1021_ = v___y_1250_;
v___y_1022_ = v___y_1251_;
v___y_1023_ = v___y_1253_;
v___y_1024_ = v___y_1252_;
v___y_1025_ = v___x_1260_;
goto v___jp_1014_;
}
}
v___jp_1265_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = lean_array_get_size(v___y_1268_);
v___x_1278_ = l_Array_toSubarray___redArg(v___y_1268_, v___x_1262_, v___x_1277_);
lean_inc_ref(v___y_1267_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___y_1267_);
lean_ctor_set(v___x_1279_, 1, v_body_1274_);
v___x_1280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1264_, v___x_1278_, v___x_1279_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v_fst_1283_; lean_object* v_snd_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1303_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
v_a_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1280_, 2);
v_fst_1283_ = lean_ctor_get(v_a_1281_, 0);
v_snd_1284_ = lean_ctor_get(v_a_1281_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_a_1281_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1286_ = v_a_1281_;
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_snd_1284_);
lean_inc(v_fst_1283_);
lean_dec(v_a_1281_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_ref_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v_ref_1288_ = lean_ctor_get(v___y_1275_, 5);
v___x_1289_ = l_Lean_SourceInfo_fromRef(v_ref_1288_, v___x_1264_);
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1291_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 2);
lean_ctor_set(v___x_1286_, 1, v___x_1292_);
lean_ctor_set(v___x_1286_, 0, v___x_1291_);
v___x_1294_ = v___x_1286_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1296_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1266_) == 1)
{
lean_object* v_val_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_val_1297_ = lean_ctor_get(v___y_1266_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___y_1266_, 1);
v___x_1298_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1289_);
v___x_1299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1289_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = l_Array_mkArray2___redArg(v_val_1297_, v___x_1299_);
v___y_1187_ = v_fst_1283_;
v___y_1188_ = v___x_1295_;
v___y_1189_ = v_snd_1284_;
v___y_1190_ = v___y_1271_;
v___y_1191_ = v___x_1294_;
v___y_1192_ = v_a_1282_;
v___y_1193_ = v___x_1289_;
v___y_1194_ = v___y_1269_;
v___y_1195_ = v___y_1270_;
v___y_1196_ = v___x_1296_;
v___y_1197_ = v_x_1273_;
v___y_1198_ = v___y_1272_;
v___y_1199_ = v___x_1290_;
v___y_1200_ = v___x_1300_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1301_; 
lean_dec(v___y_1266_);
v___x_1301_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1187_ = v_fst_1283_;
v___y_1188_ = v___x_1295_;
v___y_1189_ = v_snd_1284_;
v___y_1190_ = v___y_1271_;
v___y_1191_ = v___x_1294_;
v___y_1192_ = v_a_1282_;
v___y_1193_ = v___x_1289_;
v___y_1194_ = v___y_1269_;
v___y_1195_ = v___y_1270_;
v___y_1196_ = v___x_1296_;
v___y_1197_ = v_x_1273_;
v___y_1198_ = v___y_1272_;
v___y_1199_ = v___x_1290_;
v___y_1200_ = v___x_1301_;
goto v___jp_1186_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_x_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec(v___y_1266_);
lean_dec(v_tk_1261_);
v_a_1304_ = lean_ctor_get(v___x_1280_, 0);
v_a_1305_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1280_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_inc(v_a_1304_);
lean_dec(v___x_1280_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1304_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_doElems_1326_; uint8_t v___x_1327_; 
v___x_1324_ = l_Lean_Syntax_getArg(v___y_1316_, v___x_1262_);
v___x_1325_ = l_Lean_Syntax_getArg(v___y_1316_, v___y_1317_);
lean_dec(v___y_1316_);
v_doElems_1326_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1327_ = l_Lean_Syntax_isIdent(v___x_1324_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1324_);
v___x_1329_ = l_Lean_Syntax_isOfKind(v___x_1324_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1324_, v___x_1329_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v_a_1332_; lean_object* v_ref_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc_n(v_a_1331_, 2);
v_a_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1330_, 2);
v_ref_1333_ = lean_ctor_get(v___y_1322_, 5);
v___x_1334_ = l_Lean_SourceInfo_fromRef(v_ref_1333_, v___x_1329_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1336_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1337_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1339_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1334_, 15);
v___x_1340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1334_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1334_);
lean_ctor_set(v___x_1342_, 1, v___x_1336_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1342_, 4);
v___x_1344_ = l_Lean_Syntax_node2(v___x_1334_, v___x_1343_, v___x_1342_, v_a_1331_);
v___x_1345_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1344_);
v___x_1346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1334_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1349_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1350_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1334_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1324_);
v___x_1353_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1352_);
v___x_1354_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1334_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_Syntax_node4(v___x_1334_, v___x_1349_, v___x_1351_, v___x_1353_, v___x_1355_, v___y_1314_);
v___x_1357_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1356_);
v___x_1358_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1348_, v___x_1357_);
v___x_1359_ = l_Lean_Syntax_node7(v___x_1334_, v___x_1338_, v___x_1340_, v___x_1342_, v___x_1342_, v___x_1342_, v___x_1345_, v___x_1347_, v___x_1358_);
v___x_1360_ = l_Lean_Syntax_node2(v___x_1334_, v___x_1337_, v___x_1359_, v___x_1342_);
v___x_1361_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1360_);
v___x_1362_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1335_, v___x_1361_);
v___y_1266_ = v_h_x3f_1321_;
v___y_1267_ = v_doElems_1326_;
v___y_1268_ = v___y_1315_;
v___y_1269_ = v___y_1318_;
v___y_1270_ = v___x_1325_;
v___y_1271_ = v___y_1319_;
v___y_1272_ = v___y_1320_;
v_x_1273_ = v_a_1331_;
v_body_1274_ = v___x_1362_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v_a_1332_;
goto v___jp_1265_;
}
else
{
lean_object* v_a_1363_; lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v___x_1325_);
lean_dec(v___x_1324_);
lean_dec(v_h_x3f_1321_);
lean_dec(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v_tk_1261_);
v_a_1363_ = lean_ctor_get(v___x_1330_, 0);
v_a_1364_ = lean_ctor_get(v___x_1330_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1330_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_inc(v_a_1363_);
lean_dec(v___x_1330_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1363_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1324_, v___x_1327_, v___y_1322_, v___y_1323_);
lean_dec(v___x_1324_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v_a_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
v_a_1374_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1372_, 2);
v___y_1266_ = v_h_x3f_1321_;
v___y_1267_ = v_doElems_1326_;
v___y_1268_ = v___y_1315_;
v___y_1269_ = v___y_1318_;
v___y_1270_ = v___x_1325_;
v___y_1271_ = v___y_1319_;
v___y_1272_ = v___y_1320_;
v_x_1273_ = v_a_1373_;
v_body_1274_ = v___y_1314_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v_a_1374_;
goto v___jp_1265_;
}
else
{
lean_object* v_a_1375_; lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v___x_1325_);
lean_dec(v_h_x3f_1321_);
lean_dec(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v_tk_1261_);
v_a_1375_ = lean_ctor_get(v___x_1372_, 0);
v_a_1376_ = lean_ctor_get(v___x_1372_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1372_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_inc(v_a_1375_);
lean_dec(v___x_1372_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1375_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
else
{
v___y_1266_ = v_h_x3f_1321_;
v___y_1267_ = v_doElems_1326_;
v___y_1268_ = v___y_1315_;
v___y_1269_ = v___y_1318_;
v___y_1270_ = v___x_1325_;
v___y_1271_ = v___y_1319_;
v___y_1272_ = v___y_1320_;
v_x_1273_ = v___x_1324_;
v_body_1274_ = v___y_1314_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v___y_1323_;
goto v___jp_1265_;
}
}
}
v___jp_1014_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_inc_ref_n(v___y_1020_, 3);
v___x_1026_ = l_Array_append___redArg(v___y_1020_, v___y_1025_);
lean_dec_ref(v___y_1025_);
lean_inc_n(v___y_1015_, 3);
lean_inc_n(v___y_1021_, 7);
v___x_1027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1027_, 0, v___y_1021_);
lean_ctor_set(v___x_1027_, 1, v___y_1015_);
lean_ctor_set(v___x_1027_, 2, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___y_1021_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
lean_inc_ref(v___x_1029_);
v___x_1030_ = l_Lean_Syntax_node6(v___y_1021_, v___x_1013_, v___y_1019_, v___y_1024_, v___y_1016_, v___x_1027_, v___x_1029_, v___y_1018_);
v___x_1031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1031_, 0, v___y_1021_);
lean_ctor_set(v___x_1031_, 1, v___y_1015_);
lean_ctor_set(v___x_1031_, 2, v___y_1020_);
lean_inc(v___y_1022_);
v___x_1032_ = l_Lean_Syntax_node2(v___y_1021_, v___y_1022_, v___x_1030_, v___x_1031_);
v___x_1033_ = lean_array_push(v___y_1023_, v___x_1032_);
v___x_1034_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1036_ = l_Array_append___redArg(v___y_1020_, v___x_1033_);
lean_dec_ref(v___x_1033_);
v___x_1037_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1037_, 0, v___y_1021_);
lean_ctor_set(v___x_1037_, 1, v___y_1015_);
lean_ctor_set(v___x_1037_, 2, v___x_1036_);
v___x_1038_ = l_Lean_Syntax_node1(v___y_1021_, v___x_1035_, v___x_1037_);
v___x_1039_ = l_Lean_Syntax_node2(v___y_1021_, v___x_1034_, v___x_1029_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___y_1017_);
return v___x_1040_;
}
v___jp_1041_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_inc_ref_n(v___y_1044_, 3);
v___x_1053_ = l_Array_append___redArg(v___y_1044_, v___y_1052_);
lean_dec_ref(v___y_1052_);
lean_inc_n(v___y_1049_, 3);
lean_inc_n(v___y_1050_, 7);
v___x_1054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1054_, 0, v___y_1050_);
lean_ctor_set(v___x_1054_, 1, v___y_1049_);
lean_ctor_set(v___x_1054_, 2, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___y_1050_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
lean_inc_ref(v___x_1056_);
v___x_1057_ = l_Lean_Syntax_node6(v___y_1050_, v___x_1013_, v___y_1045_, v___y_1047_, v___y_1043_, v___x_1054_, v___x_1056_, v___y_1051_);
v___x_1058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1058_, 0, v___y_1050_);
lean_ctor_set(v___x_1058_, 1, v___y_1049_);
lean_ctor_set(v___x_1058_, 2, v___y_1044_);
lean_inc(v___y_1042_);
v___x_1059_ = l_Lean_Syntax_node2(v___y_1050_, v___y_1042_, v___x_1057_, v___x_1058_);
v___x_1060_ = lean_array_push(v___y_1048_, v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1063_ = l_Array_append___redArg(v___y_1044_, v___x_1060_);
lean_dec_ref(v___x_1060_);
v___x_1064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1064_, 0, v___y_1050_);
lean_ctor_set(v___x_1064_, 1, v___y_1049_);
lean_ctor_set(v___x_1064_, 2, v___x_1063_);
v___x_1065_ = l_Lean_Syntax_node1(v___y_1050_, v___x_1062_, v___x_1064_);
v___x_1066_ = l_Lean_Syntax_node2(v___y_1050_, v___x_1061_, v___x_1056_, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___y_1046_);
return v___x_1067_;
}
v___jp_1068_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc_ref_n(v___y_1072_, 3);
v___x_1080_ = l_Array_append___redArg(v___y_1072_, v___y_1079_);
lean_dec_ref(v___y_1079_);
lean_inc_n(v___y_1075_, 3);
lean_inc_n(v___y_1070_, 7);
v___x_1081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1070_);
lean_ctor_set(v___x_1081_, 1, v___y_1075_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___y_1070_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
lean_inc_ref(v___x_1083_);
v___x_1084_ = l_Lean_Syntax_node6(v___y_1070_, v___x_1013_, v___y_1078_, v___y_1074_, v___y_1071_, v___x_1081_, v___x_1083_, v___y_1073_);
v___x_1085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1085_, 0, v___y_1070_);
lean_ctor_set(v___x_1085_, 1, v___y_1075_);
lean_ctor_set(v___x_1085_, 2, v___y_1072_);
lean_inc(v___y_1069_);
v___x_1086_ = l_Lean_Syntax_node2(v___y_1070_, v___y_1069_, v___x_1084_, v___x_1085_);
v___x_1087_ = lean_array_push(v___y_1077_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1090_ = l_Array_append___redArg(v___y_1072_, v___x_1087_);
lean_dec_ref(v___x_1087_);
v___x_1091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1091_, 0, v___y_1070_);
lean_ctor_set(v___x_1091_, 1, v___y_1075_);
lean_ctor_set(v___x_1091_, 2, v___x_1090_);
v___x_1092_ = l_Lean_Syntax_node1(v___y_1070_, v___x_1089_, v___x_1091_);
v___x_1093_ = l_Lean_Syntax_node2(v___y_1070_, v___x_1088_, v___x_1083_, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___y_1076_);
return v___x_1094_;
}
v___jp_1095_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_inc_ref_n(v___y_1103_, 3);
v___x_1107_ = l_Array_append___redArg(v___y_1103_, v___y_1106_);
lean_dec_ref(v___y_1106_);
lean_inc_n(v___y_1101_, 3);
lean_inc_n(v___y_1100_, 7);
v___x_1108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1108_, 0, v___y_1100_);
lean_ctor_set(v___x_1108_, 1, v___y_1101_);
lean_ctor_set(v___x_1108_, 2, v___x_1107_);
v___x_1109_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___y_1100_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
lean_inc_ref(v___x_1110_);
v___x_1111_ = l_Lean_Syntax_node6(v___y_1100_, v___x_1013_, v___y_1104_, v___y_1096_, v___y_1099_, v___x_1108_, v___x_1110_, v___y_1102_);
v___x_1112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1100_);
lean_ctor_set(v___x_1112_, 1, v___y_1101_);
lean_ctor_set(v___x_1112_, 2, v___y_1103_);
lean_inc(v___y_1105_);
v___x_1113_ = l_Lean_Syntax_node2(v___y_1100_, v___y_1105_, v___x_1111_, v___x_1112_);
v___x_1114_ = lean_array_push(v___y_1097_, v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1116_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1117_ = l_Array_append___redArg(v___y_1103_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1118_, 0, v___y_1100_);
lean_ctor_set(v___x_1118_, 1, v___y_1101_);
lean_ctor_set(v___x_1118_, 2, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node1(v___y_1100_, v___x_1116_, v___x_1118_);
v___x_1120_ = l_Lean_Syntax_node2(v___y_1100_, v___x_1115_, v___x_1110_, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v___y_1098_);
return v___x_1121_;
}
v___jp_1122_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_inc_ref_n(v___y_1132_, 3);
v___x_1134_ = l_Array_append___redArg(v___y_1132_, v___y_1133_);
lean_dec_ref(v___y_1133_);
lean_inc_n(v___y_1128_, 3);
lean_inc_n(v___y_1131_, 7);
v___x_1135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1135_, 0, v___y_1131_);
lean_ctor_set(v___x_1135_, 1, v___y_1128_);
lean_ctor_set(v___x_1135_, 2, v___x_1134_);
v___x_1136_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1131_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
lean_inc_ref(v___x_1137_);
v___x_1138_ = l_Lean_Syntax_node6(v___y_1131_, v___x_1013_, v___y_1124_, v___y_1127_, v___y_1125_, v___x_1135_, v___x_1137_, v___y_1129_);
v___x_1139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1131_);
lean_ctor_set(v___x_1139_, 1, v___y_1128_);
lean_ctor_set(v___x_1139_, 2, v___y_1132_);
lean_inc(v___y_1130_);
v___x_1140_ = l_Lean_Syntax_node2(v___y_1131_, v___y_1130_, v___x_1138_, v___x_1139_);
v___x_1141_ = lean_array_push(v___y_1123_, v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1144_ = l_Array_append___redArg(v___y_1132_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1145_, 0, v___y_1131_);
lean_ctor_set(v___x_1145_, 1, v___y_1128_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_node1(v___y_1131_, v___x_1143_, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_node2(v___y_1131_, v___x_1142_, v___x_1137_, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v___y_1126_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object* v_stx_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Elab_Do_expandDoFor(v_stx_2388_, v_a_2389_, v_a_2390_);
lean_dec_ref(v_a_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_2392_, lean_object* v_inst_2393_, lean_object* v_R_2394_, lean_object* v_a_2395_, lean_object* v_b_2396_, lean_object* v_c_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_2392_, v_a_2395_, v_b_2396_, v___y_2398_, v___y_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_2401_, lean_object* v_inst_2402_, lean_object* v_R_2403_, lean_object* v_a_2404_, lean_object* v_b_2405_, lean_object* v_c_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v___x_208112__boxed_2409_; lean_object* v_res_2410_; 
v___x_208112__boxed_2409_ = lean_unbox(v___x_2401_);
v_res_2410_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_208112__boxed_2409_, v_inst_2402_, v_R_2403_, v_a_2404_, v_b_2405_, v_c_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(lean_object* v_inst_2411_, lean_object* v_R_2412_, lean_object* v_a_2413_, lean_object* v_b_2414_, lean_object* v_c_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v_a_2413_, v_b_2414_, v___y_2416_, v___y_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___boxed(lean_object* v_inst_2419_, lean_object* v_R_2420_, lean_object* v_a_2421_, lean_object* v_b_2422_, lean_object* v_c_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(v_inst_2419_, v_R_2420_, v_a_2421_, v_b_2422_, v_c_2423_, v___y_2424_, v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2434_ = l_Lean_Elab_macroAttribute;
v___x_2435_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_2436_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_2437_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor___boxed), 3, 0);
v___x_2438_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2434_, v___x_2435_, v___x_2436_, v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_2440_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1));
v___x_2448_ = l_Lean_stringToMessageData(v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2);
v___x_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(lean_object* v_invClause_2462_, lean_object* v_h_x3f_2463_, lean_object* v_xs_2464_, lean_object* v_00_u03b1_2465_, lean_object* v_mi_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
uint8_t v___y_2475_; lean_object* v___y_2476_; 
if (lean_obj_tag(v_h_x3f_2463_) == 0)
{
uint8_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = 1;
v___x_2578_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6));
v___y_2475_ = v___x_2577_;
v___y_2476_ = v___x_2578_;
goto v___jp_2474_;
}
else
{
uint8_t v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = 1;
v___x_2580_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8));
v___y_2475_ = v___x_2579_;
v___y_2476_ = v___x_2580_;
goto v___jp_2474_;
}
v___jp_2474_:
{
lean_object* v___x_2477_; lean_object* v_env_2478_; uint8_t v___x_2479_; 
v___x_2477_ = lean_st_ref_get(v_a_2472_);
v_env_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_ref(v_env_2478_);
lean_dec(v___x_2477_);
lean_inc(v___y_2476_);
v___x_2479_ = l_Lean_Environment_contains(v_env_2478_, v___y_2476_, v___y_2475_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec_ref(v_mi_2466_);
lean_dec_ref(v_00_u03b1_2465_);
lean_dec_ref(v_xs_2464_);
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
else
{
lean_object* v_fileName_2482_; lean_object* v_fileMap_2483_; lean_object* v_options_2484_; lean_object* v_currRecDepth_2485_; lean_object* v_maxRecDepth_2486_; lean_object* v_ref_2487_; lean_object* v_currNamespace_2488_; lean_object* v_openDecls_2489_; lean_object* v_initHeartbeats_2490_; lean_object* v_maxHeartbeats_2491_; lean_object* v_quotContext_2492_; lean_object* v_currMacroScope_2493_; uint8_t v_diag_2494_; lean_object* v_cancelTk_x3f_2495_; uint8_t v_suppressElabErrors_2496_; lean_object* v_inheritedTraceOptions_2497_; lean_object* v_m_2498_; lean_object* v_ref_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_fileName_2482_ = lean_ctor_get(v_a_2471_, 0);
v_fileMap_2483_ = lean_ctor_get(v_a_2471_, 1);
v_options_2484_ = lean_ctor_get(v_a_2471_, 2);
v_currRecDepth_2485_ = lean_ctor_get(v_a_2471_, 3);
v_maxRecDepth_2486_ = lean_ctor_get(v_a_2471_, 4);
v_ref_2487_ = lean_ctor_get(v_a_2471_, 5);
v_currNamespace_2488_ = lean_ctor_get(v_a_2471_, 6);
v_openDecls_2489_ = lean_ctor_get(v_a_2471_, 7);
v_initHeartbeats_2490_ = lean_ctor_get(v_a_2471_, 8);
v_maxHeartbeats_2491_ = lean_ctor_get(v_a_2471_, 9);
v_quotContext_2492_ = lean_ctor_get(v_a_2471_, 10);
v_currMacroScope_2493_ = lean_ctor_get(v_a_2471_, 11);
v_diag_2494_ = lean_ctor_get_uint8(v_a_2471_, sizeof(void*)*14);
v_cancelTk_x3f_2495_ = lean_ctor_get(v_a_2471_, 12);
v_suppressElabErrors_2496_ = lean_ctor_get_uint8(v_a_2471_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2497_ = lean_ctor_get(v_a_2471_, 13);
v_m_2498_ = lean_ctor_get(v_mi_2466_, 0);
lean_inc_ref(v_m_2498_);
lean_dec_ref(v_mi_2466_);
v_ref_2499_ = l_Lean_replaceRef(v_invClause_2462_, v_ref_2487_);
lean_inc_ref(v_inheritedTraceOptions_2497_);
lean_inc(v_cancelTk_x3f_2495_);
lean_inc(v_currMacroScope_2493_);
lean_inc(v_quotContext_2492_);
lean_inc(v_maxHeartbeats_2491_);
lean_inc(v_initHeartbeats_2490_);
lean_inc(v_openDecls_2489_);
lean_inc(v_currNamespace_2488_);
lean_inc(v_ref_2499_);
lean_inc(v_maxRecDepth_2486_);
lean_inc(v_currRecDepth_2485_);
lean_inc_ref(v_options_2484_);
lean_inc_ref(v_fileMap_2483_);
lean_inc_ref(v_fileName_2482_);
v___x_2500_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2500_, 0, v_fileName_2482_);
lean_ctor_set(v___x_2500_, 1, v_fileMap_2483_);
lean_ctor_set(v___x_2500_, 2, v_options_2484_);
lean_ctor_set(v___x_2500_, 3, v_currRecDepth_2485_);
lean_ctor_set(v___x_2500_, 4, v_maxRecDepth_2486_);
lean_ctor_set(v___x_2500_, 5, v_ref_2499_);
lean_ctor_set(v___x_2500_, 6, v_currNamespace_2488_);
lean_ctor_set(v___x_2500_, 7, v_openDecls_2489_);
lean_ctor_set(v___x_2500_, 8, v_initHeartbeats_2490_);
lean_ctor_set(v___x_2500_, 9, v_maxHeartbeats_2491_);
lean_ctor_set(v___x_2500_, 10, v_quotContext_2492_);
lean_ctor_set(v___x_2500_, 11, v_currMacroScope_2493_);
lean_ctor_set(v___x_2500_, 12, v_cancelTk_x3f_2495_);
lean_ctor_set(v___x_2500_, 13, v_inheritedTraceOptions_2497_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*14, v_diag_2494_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*14 + 1, v_suppressElabErrors_2496_);
v___x_2501_ = l_Lean_Elab_Term_exprToSyntax(v_m_2498_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2503_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
lean_inc(v_a_2472_);
lean_inc_ref(v___x_2500_);
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
v___x_2503_ = lean_infer_type(v_xs_2464_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = l_Lean_Elab_Term_exprToSyntax(v_a_2504_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = l_Lean_Elab_Term_exprToSyntax(v_00_u03b1_2465_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2509_ = 0;
v___x_2510_ = l_Lean_SourceInfo_fromRef(v_ref_2499_, v___x_2509_);
lean_dec(v_ref_2499_);
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0));
lean_inc(v___y_2476_);
v___x_2512_ = l_Lean_mkIdent(v___y_2476_);
v___x_2513_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
lean_inc(v___x_2510_);
v___x_2514_ = l_Lean_Syntax_node3(v___x_2510_, v___x_2513_, v_a_2502_, v_a_2506_, v_a_2508_);
v___x_2515_ = l_Lean_Syntax_node2(v___x_2510_, v___x_2511_, v___x_2512_, v___x_2514_);
v___x_2516_ = l_Lean_Elab_Term_elabType(v___x_2515_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3);
v___x_2519_ = l_Lean_Elab_Term_mkInstMVar(v_a_2517_, v___x_2518_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
lean_dec_ref_known(v___x_2500_, 14);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2527_; 
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; 
v_unused_2528_ = lean_ctor_get(v___x_2519_, 0);
lean_dec(v_unused_2528_);
v___x_2521_ = v___x_2519_;
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v___x_2519_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2523_ = lean_box(0);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2523_);
v___x_2525_ = v___x_2521_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_a_2529_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2519_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2519_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref_known(v___x_2500_, 14);
v_a_2537_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2516_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2516_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2506_);
lean_dec(v_a_2502_);
lean_dec_ref_known(v___x_2500_, 14);
lean_dec(v_ref_2499_);
v_a_2545_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2507_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2507_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_a_2502_);
lean_dec_ref_known(v___x_2500_, 14);
lean_dec(v_ref_2499_);
lean_dec_ref(v_00_u03b1_2465_);
v_a_2553_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2505_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2505_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_a_2502_);
lean_dec_ref_known(v___x_2500_, 14);
lean_dec(v_ref_2499_);
lean_dec_ref(v_00_u03b1_2465_);
v_a_2561_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2503_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2503_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref_known(v___x_2500_, 14);
lean_dec(v_ref_2499_);
lean_dec_ref(v_00_u03b1_2465_);
lean_dec_ref(v_xs_2464_);
v_a_2569_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2501_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2501_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___boxed(lean_object* v_invClause_2581_, lean_object* v_h_x3f_2582_, lean_object* v_xs_2583_, lean_object* v_00_u03b1_2584_, lean_object* v_mi_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_2581_, v_h_x3f_2582_, v_xs_2583_, v_00_u03b1_2584_, v_mi_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_h_x3f_2582_);
lean_dec(v_invClause_2581_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn(lean_object* v_invClause_2594_, lean_object* v_h_x3f_2595_, lean_object* v_xs_2596_, lean_object* v_00_u03b1_2597_, lean_object* v_mi_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_2594_, v_h_x3f_2595_, v_xs_2596_, v_00_u03b1_2597_, v_mi_2598_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___boxed(lean_object* v_invClause_2608_, lean_object* v_h_x3f_2609_, lean_object* v_xs_2610_, lean_object* v_00_u03b1_2611_, lean_object* v_mi_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn(v_invClause_2608_, v_h_x3f_2609_, v_xs_2610_, v_00_u03b1_2611_, v_mi_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec_ref(v_a_2613_);
lean_dec(v_h_x3f_2609_);
lean_dec(v_invClause_2608_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(lean_object* v_e_2622_, lean_object* v___y_2623_){
_start:
{
uint8_t v___x_2625_; 
v___x_2625_ = l_Lean_Expr_hasMVar(v_e_2622_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_e_2622_);
return v___x_2626_;
}
else
{
lean_object* v___x_2627_; lean_object* v_mctx_2628_; lean_object* v___x_2629_; lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v___x_2632_; lean_object* v_cache_2633_; lean_object* v_zetaDeltaFVarIds_2634_; lean_object* v_postponed_2635_; lean_object* v_diag_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2645_; 
v___x_2627_ = lean_st_ref_get(v___y_2623_);
v_mctx_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc_ref(v_mctx_2628_);
lean_dec(v___x_2627_);
v___x_2629_ = l_Lean_instantiateMVarsCore(v_mctx_2628_, v_e_2622_);
v_fst_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_fst_2630_);
v_snd_2631_ = lean_ctor_get(v___x_2629_, 1);
lean_inc(v_snd_2631_);
lean_dec_ref(v___x_2629_);
v___x_2632_ = lean_st_ref_take(v___y_2623_);
v_cache_2633_ = lean_ctor_get(v___x_2632_, 1);
v_zetaDeltaFVarIds_2634_ = lean_ctor_get(v___x_2632_, 2);
v_postponed_2635_ = lean_ctor_get(v___x_2632_, 3);
v_diag_2636_ = lean_ctor_get(v___x_2632_, 4);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v___x_2632_, 0);
lean_dec(v_unused_2646_);
v___x_2638_ = v___x_2632_;
v_isShared_2639_ = v_isSharedCheck_2645_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_diag_2636_);
lean_inc(v_postponed_2635_);
lean_inc(v_zetaDeltaFVarIds_2634_);
lean_inc(v_cache_2633_);
lean_dec(v___x_2632_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2645_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v_snd_2631_);
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_snd_2631_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_cache_2633_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_zetaDeltaFVarIds_2634_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_postponed_2635_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v_diag_2636_);
v___x_2641_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_st_ref_put(v___y_2623_, v___x_2641_);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_fst_2630_);
return v___x_2643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg___boxed(lean_object* v_e_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(v_e_2647_, v___y_2648_);
lean_dec(v___y_2648_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0(lean_object* v_e_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(v_e_2651_, v___y_2656_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___boxed(lean_object* v_e_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0(v_e_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2670_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__3(void){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2));
v___x_2678_ = l_Lean_mkIdent(v___x_2677_);
return v___x_2678_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__4(void){
_start:
{
lean_object* v___x_2679_; lean_object* v_dummy_2680_; 
v___x_2679_ = lean_box(0);
v_dummy_2680_ = l_Lean_Expr_sort___override(v___x_2679_);
return v_dummy_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v___x_2689_; lean_object* v_env_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; uint8_t v___x_2693_; 
v___x_2689_ = lean_st_ref_get(v_a_2687_);
v_env_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc_ref(v_env_2690_);
lean_dec(v___x_2689_);
v___x_2691_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2));
v___x_2692_ = 1;
v___x_2693_ = l_Lean_Environment_contains(v_env_2690_, v___x_2691_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
else
{
lean_object* v_monadInfo_2696_; lean_object* v_m_2697_; lean_object* v___x_2698_; 
v_monadInfo_2696_ = lean_ctor_get(v_a_2681_, 0);
v_m_2697_ = lean_ctor_get(v_monadInfo_2696_, 0);
lean_inc_ref(v_m_2697_);
v___x_2698_ = l_Lean_Elab_Term_exprToSyntax(v_m_2697_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v_ref_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v_ref_2700_ = lean_ctor_get(v_a_2686_, 5);
v___x_2701_ = 0;
v___x_2702_ = l_Lean_SourceInfo_fromRef(v_ref_2700_, v___x_2701_);
v___x_2703_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0));
v___x_2704_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__3);
v___x_2705_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2706_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_2707_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
lean_inc_n(v___x_2702_, 3);
v___x_2708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2702_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = l_Lean_Syntax_node1(v___x_2702_, v___x_2706_, v___x_2708_);
lean_inc(v___x_2709_);
v___x_2710_ = l_Lean_Syntax_node3(v___x_2702_, v___x_2705_, v_a_2699_, v___x_2709_, v___x_2709_);
v___x_2711_ = l_Lean_Syntax_node2(v___x_2702_, v___x_2703_, v___x_2704_, v___x_2710_);
v___x_2712_ = l_Lean_Elab_Term_elabType(v___x_2711_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc_n(v_a_2713_, 2);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2714_ = lean_box(0);
v___x_2715_ = l_Lean_Meta_trySynthInstance(v_a_2713_, v___x_2714_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2756_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2756_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2756_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
if (lean_obj_tag(v_a_2716_) == 1)
{
lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2751_; 
v_isSharedCheck_2751_ = !lean_is_exclusive(v_a_2716_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; 
v_unused_2752_ = lean_ctor_get(v_a_2716_, 0);
lean_dec(v_unused_2752_);
v___x_2721_ = v_a_2716_;
v_isShared_2722_ = v_isSharedCheck_2751_;
goto v_resetjp_2720_;
}
else
{
lean_dec(v_a_2716_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2751_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v_dummy_2723_; lean_object* v_nargs_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_dummy_2723_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__4, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__4_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__4);
v_nargs_2724_ = l_Lean_Expr_getAppNumArgs(v_a_2713_);
lean_inc(v_nargs_2724_);
v___x_2725_ = lean_mk_array(v_nargs_2724_, v_dummy_2723_);
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_sub(v_nargs_2724_, v___x_2726_);
lean_dec(v_nargs_2724_);
v___x_2728_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2713_, v___x_2725_, v___x_2727_);
v___x_2729_ = lean_array_get_size(v___x_2728_);
v___x_2730_ = lean_nat_dec_lt(v___x_2726_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2732_; 
lean_dec_ref(v___x_2728_);
lean_del_object(v___x_2721_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2714_);
v___x_2732_ = v___x_2718_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2714_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2750_; 
lean_del_object(v___x_2718_);
v___x_2734_ = lean_array_fget(v___x_2728_, v___x_2726_);
lean_dec_ref(v___x_2728_);
v___x_2735_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(v___x_2734_, v_a_2685_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2750_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2750_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
uint8_t v___x_2740_; 
v___x_2740_ = l_Lean_Expr_hasExprMVar(v_a_2736_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2742_; 
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 0, v_a_2736_);
v___x_2742_ = v___x_2721_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2736_);
v___x_2742_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2744_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2742_);
v___x_2744_ = v___x_2738_;
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
else
{
lean_object* v___x_2748_; 
lean_dec(v_a_2736_);
lean_del_object(v___x_2721_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2714_);
v___x_2748_ = v___x_2738_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2714_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
}
else
{
lean_object* v___x_2754_; 
lean_dec(v_a_2716_);
lean_dec(v_a_2713_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2714_);
v___x_2754_ = v___x_2718_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2714_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec(v_a_2713_);
v_a_2757_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2715_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2715_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2712_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2712_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
v_a_2773_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2698_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2698_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___boxed(lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(lean_object* v_msgData_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; lean_object* v_env_2797_; lean_object* v___x_2798_; lean_object* v_mctx_2799_; lean_object* v_lctx_2800_; lean_object* v_options_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2796_ = lean_st_ref_get(v___y_2794_);
v_env_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc_ref(v_env_2797_);
lean_dec(v___x_2796_);
v___x_2798_ = lean_st_ref_get(v___y_2792_);
v_mctx_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc_ref(v_mctx_2799_);
lean_dec(v___x_2798_);
v_lctx_2800_ = lean_ctor_get(v___y_2791_, 2);
v_options_2801_ = lean_ctor_get(v___y_2793_, 2);
lean_inc_ref(v_options_2801_);
lean_inc_ref(v_lctx_2800_);
v___x_2802_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2802_, 0, v_env_2797_);
lean_ctor_set(v___x_2802_, 1, v_mctx_2799_);
lean_ctor_set(v___x_2802_, 2, v_lctx_2800_);
lean_ctor_set(v___x_2802_, 3, v_options_2801_);
v___x_2803_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v_msgData_2790_);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(v_msgData_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(lean_object* v_msg_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_ref_2818_; lean_object* v___x_2819_; lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2828_; 
v_ref_2818_ = lean_ctor_get(v___y_2815_, 5);
v___x_2819_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(v_msg_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2822_ = v___x_2819_;
v_isShared_2823_ = v_isSharedCheck_2828_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2828_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
lean_inc(v_ref_2818_);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_ref_2818_);
lean_ctor_set(v___x_2824_, 1, v_a_2820_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set_tag(v___x_2822_, 1);
lean_ctor_set(v___x_2822_, 0, v___x_2824_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(v_msg_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(lean_object* v_ref_2836_, lean_object* v_msg_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_fileName_2846_; lean_object* v_fileMap_2847_; lean_object* v_options_2848_; lean_object* v_currRecDepth_2849_; lean_object* v_maxRecDepth_2850_; lean_object* v_ref_2851_; lean_object* v_currNamespace_2852_; lean_object* v_openDecls_2853_; lean_object* v_initHeartbeats_2854_; lean_object* v_maxHeartbeats_2855_; lean_object* v_quotContext_2856_; lean_object* v_currMacroScope_2857_; uint8_t v_diag_2858_; lean_object* v_cancelTk_x3f_2859_; uint8_t v_suppressElabErrors_2860_; lean_object* v_inheritedTraceOptions_2861_; lean_object* v_ref_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_fileName_2846_ = lean_ctor_get(v___y_2843_, 0);
v_fileMap_2847_ = lean_ctor_get(v___y_2843_, 1);
v_options_2848_ = lean_ctor_get(v___y_2843_, 2);
v_currRecDepth_2849_ = lean_ctor_get(v___y_2843_, 3);
v_maxRecDepth_2850_ = lean_ctor_get(v___y_2843_, 4);
v_ref_2851_ = lean_ctor_get(v___y_2843_, 5);
v_currNamespace_2852_ = lean_ctor_get(v___y_2843_, 6);
v_openDecls_2853_ = lean_ctor_get(v___y_2843_, 7);
v_initHeartbeats_2854_ = lean_ctor_get(v___y_2843_, 8);
v_maxHeartbeats_2855_ = lean_ctor_get(v___y_2843_, 9);
v_quotContext_2856_ = lean_ctor_get(v___y_2843_, 10);
v_currMacroScope_2857_ = lean_ctor_get(v___y_2843_, 11);
v_diag_2858_ = lean_ctor_get_uint8(v___y_2843_, sizeof(void*)*14);
v_cancelTk_x3f_2859_ = lean_ctor_get(v___y_2843_, 12);
v_suppressElabErrors_2860_ = lean_ctor_get_uint8(v___y_2843_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2861_ = lean_ctor_get(v___y_2843_, 13);
v_ref_2862_ = l_Lean_replaceRef(v_ref_2836_, v_ref_2851_);
lean_inc_ref(v_inheritedTraceOptions_2861_);
lean_inc(v_cancelTk_x3f_2859_);
lean_inc(v_currMacroScope_2857_);
lean_inc(v_quotContext_2856_);
lean_inc(v_maxHeartbeats_2855_);
lean_inc(v_initHeartbeats_2854_);
lean_inc(v_openDecls_2853_);
lean_inc(v_currNamespace_2852_);
lean_inc(v_maxRecDepth_2850_);
lean_inc(v_currRecDepth_2849_);
lean_inc_ref(v_options_2848_);
lean_inc_ref(v_fileMap_2847_);
lean_inc_ref(v_fileName_2846_);
v___x_2863_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2863_, 0, v_fileName_2846_);
lean_ctor_set(v___x_2863_, 1, v_fileMap_2847_);
lean_ctor_set(v___x_2863_, 2, v_options_2848_);
lean_ctor_set(v___x_2863_, 3, v_currRecDepth_2849_);
lean_ctor_set(v___x_2863_, 4, v_maxRecDepth_2850_);
lean_ctor_set(v___x_2863_, 5, v_ref_2862_);
lean_ctor_set(v___x_2863_, 6, v_currNamespace_2852_);
lean_ctor_set(v___x_2863_, 7, v_openDecls_2853_);
lean_ctor_set(v___x_2863_, 8, v_initHeartbeats_2854_);
lean_ctor_set(v___x_2863_, 9, v_maxHeartbeats_2855_);
lean_ctor_set(v___x_2863_, 10, v_quotContext_2856_);
lean_ctor_set(v___x_2863_, 11, v_currMacroScope_2857_);
lean_ctor_set(v___x_2863_, 12, v_cancelTk_x3f_2859_);
lean_ctor_set(v___x_2863_, 13, v_inheritedTraceOptions_2861_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*14, v_diag_2858_);
lean_ctor_set_uint8(v___x_2863_, sizeof(void*)*14 + 1, v_suppressElabErrors_2860_);
v___x_2864_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(v_msg_2837_, v___y_2841_, v___y_2842_, v___x_2863_, v___y_2844_);
lean_dec_ref_known(v___x_2863_, 14);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg___boxed(lean_object* v_ref_2865_, lean_object* v_msg_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_ref_2865_, v_msg_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v_ref_2865_);
return v_res_2875_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__0));
v___x_2878_ = l_Lean_stringToMessageData(v___x_2877_);
return v___x_2878_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__2));
v___x_2881_ = l_Lean_stringToMessageData(v___x_2880_);
return v___x_2881_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__4));
v___x_2884_ = l_Lean_stringToMessageData(v___x_2883_);
return v___x_2884_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__6));
v___x_2887_ = l_Lean_stringToMessageData(v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__8));
v___x_2890_ = l_Lean_stringToMessageData(v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__10));
v___x_2893_ = l_Lean_stringToMessageData(v___x_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__12));
v___x_2896_ = l_Lean_stringToMessageData(v___x_2895_);
return v___x_2896_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__14));
v___x_2899_ = l_Lean_stringToMessageData(v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(lean_object* v_ref_2900_, lean_object* v_what_2901_, lean_object* v_binders_2902_, lean_object* v_pred_x3f_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v___x_2927_ = lean_unsigned_to_nat(0u);
v___x_2928_ = lean_nat_dec_eq(v_binders_2902_, v___x_2927_);
if (v___x_2928_ == 0)
{
if (lean_obj_tag(v_pred_x3f_2903_) == 1)
{
lean_object* v_val_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2958_; 
v_val_2929_ = lean_ctor_get(v_pred_x3f_2903_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_pred_x3f_2903_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2931_ = v_pred_x3f_2903_;
v_isShared_2932_ = v_isSharedCheck_2958_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_val_2929_);
lean_dec(v_pred_x3f_2903_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2958_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v_arity_2933_; uint8_t v___x_2934_; 
v_arity_2933_ = l_Lean_Expr_getForallArity(v_val_2929_);
v___x_2934_ = lean_nat_dec_lt(v_arity_2933_, v_binders_2902_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
lean_dec(v_arity_2933_);
lean_dec(v_binders_2902_);
lean_dec_ref(v_what_2901_);
v___x_2935_ = lean_box(0);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2935_);
v___x_2937_ = v___x_2931_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
else
{
lean_object* v___x_2939_; lean_object* v___y_2941_; uint8_t v___x_2951_; 
v___x_2939_ = lean_unsigned_to_nat(1u);
v___x_2951_ = lean_nat_dec_eq(v_arity_2933_, v___x_2939_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2952_ = l_Nat_reprFast(v_arity_2933_);
v___x_2953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
v___x_2954_ = l_Lean_MessageData_ofFormat(v___x_2953_);
v___x_2955_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___y_2941_ = v___x_2956_;
goto v___jp_2940_;
}
else
{
lean_object* v___x_2957_; 
lean_dec(v_arity_2933_);
v___x_2957_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15);
v___y_2941_ = v___x_2957_;
goto v___jp_2940_;
}
v___jp_2940_:
{
uint8_t v___x_2942_; 
v___x_2942_ = lean_nat_dec_eq(v_binders_2902_, v___x_2939_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2943_ = l_Nat_reprFast(v_binders_2902_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 3);
lean_ctor_set(v___x_2931_, 0, v___x_2943_);
v___x_2945_ = v___x_2931_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = l_Lean_MessageData_ofFormat(v___x_2945_);
v___x_2947_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9);
v___x_2948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___y_2913_ = v___y_2941_;
v___y_2914_ = v___x_2948_;
goto v___jp_2912_;
}
}
else
{
lean_object* v___x_2950_; 
lean_del_object(v___x_2931_);
lean_dec(v_binders_2902_);
v___x_2950_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11);
v___y_2913_ = v___y_2941_;
v___y_2914_ = v___x_2950_;
goto v___jp_2912_;
}
}
}
}
}
else
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec(v_pred_x3f_2903_);
lean_dec(v_binders_2902_);
lean_dec_ref(v_what_2901_);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
else
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_dec(v_pred_x3f_2903_);
lean_dec(v_binders_2902_);
lean_dec_ref(v_what_2901_);
v___x_2961_ = lean_box(0);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
v___jp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2915_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1);
v___x_2916_ = l_Lean_stringToMessageData(v_what_2901_);
v___x_2917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2915_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v___x_2918_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3);
v___x_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2917_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2919_);
lean_ctor_set(v___x_2920_, 1, v___y_2913_);
v___x_2921_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5);
v___x_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v___y_2914_);
v___x_2924_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7);
v___x_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_ref_2900_, v___x_2925_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_);
return v___x_2926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___boxed(lean_object* v_ref_2963_, lean_object* v_what_2964_, lean_object* v_binders_2965_, lean_object* v_pred_x3f_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(v_ref_2963_, v_what_2964_, v_binders_2965_, v_pred_x3f_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
lean_dec(v_a_2973_);
lean_dec_ref(v_a_2972_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_ref_2963_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0(lean_object* v_00_u03b1_2976_, lean_object* v_ref_2977_, lean_object* v_msg_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_ref_2977_, v_msg_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___boxed(lean_object* v_00_u03b1_2988_, lean_object* v_ref_2989_, lean_object* v_msg_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0(v_00_u03b1_2988_, v_ref_2989_, v_msg_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v_ref_2989_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0(lean_object* v_00_u03b1_3000_, lean_object* v_msg_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(v_msg_3001_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0(v_00_u03b1_3011_, v_msg_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec_ref(v___y_3013_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg(lean_object* v_binders_3034_, lean_object* v_body_3035_, lean_object* v_a_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v___x_3038_ = lean_array_get_size(v_binders_3034_);
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = lean_nat_dec_eq(v___x_3038_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v_ref_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_ref_3041_ = lean_ctor_get(v_a_3036_, 5);
v___x_3042_ = l_Lean_SourceInfo_fromRef(v_ref_3041_, v___x_3040_);
v___x_3043_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__0));
v___x_3044_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1));
lean_inc_n(v___x_3042_, 5);
v___x_3045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3042_);
lean_ctor_set(v___x_3045_, 1, v___x_3043_);
v___x_3046_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3));
v___x_3047_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3048_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3049_ = l_Array_append___redArg(v___x_3048_, v_binders_3034_);
v___x_3050_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3042_);
lean_ctor_set(v___x_3050_, 1, v___x_3047_);
lean_ctor_set(v___x_3050_, 2, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3042_);
lean_ctor_set(v___x_3051_, 1, v___x_3047_);
lean_ctor_set(v___x_3051_, 2, v___x_3048_);
v___x_3052_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_3053_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3042_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = l_Lean_Syntax_node4(v___x_3042_, v___x_3046_, v___x_3050_, v___x_3051_, v___x_3053_, v_body_3035_);
v___x_3055_ = l_Lean_Syntax_node2(v___x_3042_, v___x_3044_, v___x_3045_, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_body_3035_);
return v___x_3057_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___boxed(lean_object* v_binders_3058_, lean_object* v_body_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg(v_binders_3058_, v_body_3059_, v_a_3060_);
lean_dec_ref(v_a_3060_);
lean_dec_ref(v_binders_3058_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(lean_object* v_binders_3063_, lean_object* v_body_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg(v_binders_3063_, v_body_3064_, v_a_3070_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___boxed(lean_object* v_binders_3074_, lean_object* v_body_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(v_binders_3074_, v_body_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec_ref(v_binders_3074_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(lean_object* v_____do__lift_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
uint8_t v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = 0;
v___x_3095_ = l_Lean_SourceInfo_fromRef(v_____do__lift_3085_, v___x_3094_);
v___x_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0___boxed(lean_object* v_____do__lift_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(v_____do__lift_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v_____do__lift_3097_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(lean_object* v_as_3107_, size_t v_sz_3108_, size_t v_i_3109_, lean_object* v_b_3110_){
_start:
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_usize_dec_lt(v_i_3109_, v_sz_3108_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3113_, 0, v_b_3110_);
return v___x_3113_;
}
else
{
lean_object* v_a_3114_; lean_object* v_ident_3115_; lean_object* v___x_3116_; size_t v___x_3117_; size_t v___x_3118_; 
v_a_3114_ = lean_array_uget_borrowed(v_as_3107_, v_i_3109_);
v_ident_3115_ = lean_ctor_get(v_a_3114_, 0);
lean_inc(v_ident_3115_);
v___x_3116_ = lean_array_push(v_b_3110_, v_ident_3115_);
v___x_3117_ = ((size_t)1ULL);
v___x_3118_ = lean_usize_add(v_i_3109_, v___x_3117_);
v_i_3109_ = v___x_3118_;
v_b_3110_ = v___x_3116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg___boxed(lean_object* v_as_3120_, lean_object* v_sz_3121_, lean_object* v_i_3122_, lean_object* v_b_3123_, lean_object* v___y_3124_){
_start:
{
size_t v_sz_boxed_3125_; size_t v_i_boxed_3126_; lean_object* v_res_3127_; 
v_sz_boxed_3125_ = lean_unbox_usize(v_sz_3121_);
lean_dec(v_sz_3121_);
v_i_boxed_3126_ = lean_unbox_usize(v_i_3122_);
lean_dec(v_i_3122_);
v_res_3127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(v_as_3120_, v_sz_boxed_3125_, v_i_boxed_3126_, v_b_3123_);
lean_dec_ref(v_as_3120_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat(lean_object* v_loopMutVars_3136_, uint8_t v_returnsEarly_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v_ref_3146_; lean_object* v_binders_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___x_3193_; lean_object* v_a_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v_binders_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___x_3225_; 
v_ref_3146_ = lean_ctor_get(v_a_3143_, 5);
v___x_3193_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(v_ref_3146_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc_n(v_a_3194_, 2);
lean_dec_ref(v___x_3193_);
v___x_3195_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_3196_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_3197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_a_3194_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = l_Lean_Syntax_node1(v_a_3194_, v___x_3195_, v___x_3197_);
v___x_3225_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
if (v_returnsEarly_3137_ == 0)
{
v_binders_3200_ = v___x_3225_;
v___y_3201_ = v_a_3138_;
v___y_3202_ = v_a_3139_;
v___y_3203_ = v_a_3140_;
v___y_3204_ = v_a_3141_;
v___y_3205_ = v_a_3142_;
v___y_3206_ = v_a_3143_;
v___y_3207_ = v_a_3144_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3226_; 
lean_inc(v___x_3198_);
v___x_3226_ = lean_array_push(v___x_3225_, v___x_3198_);
v_binders_3200_ = v___x_3226_;
v___y_3201_ = v_a_3138_;
v___y_3202_ = v_a_3139_;
v___y_3203_ = v_a_3140_;
v___y_3204_ = v_a_3141_;
v___y_3205_ = v_a_3142_;
v___y_3206_ = v_a_3143_;
v___y_3207_ = v_a_3144_;
goto v___jp_3199_;
}
v___jp_3147_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3156_ = lean_array_get_size(v_binders_3148_);
v___x_3157_ = lean_unsigned_to_nat(0u);
v___x_3158_ = lean_nat_dec_eq(v___x_3156_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = lean_nat_dec_eq(v___x_3156_, v___x_3159_);
if (v___x_3160_ == 0)
{
lean_object* v_ref_3161_; lean_object* v___x_3162_; lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3182_; 
v_ref_3161_ = lean_ctor_get(v___y_3154_, 5);
v___x_3162_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(v_ref_3161_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3165_ = v___x_3162_;
v_isShared_3166_ = v_isSharedCheck_3182_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3162_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3182_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3167_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1));
v___x_3168_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__2));
lean_inc_n(v_a_3163_, 3);
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v_a_3163_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3171_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3172_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_3173_ = l_Lean_Syntax_SepArray_ofElems(v___x_3172_, v_binders_3148_);
lean_dec_ref(v_binders_3148_);
v___x_3174_ = l_Array_append___redArg(v___x_3171_, v___x_3173_);
lean_dec_ref(v___x_3173_);
v___x_3175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3175_, 0, v_a_3163_);
lean_ctor_set(v___x_3175_, 1, v___x_3170_);
lean_ctor_set(v___x_3175_, 2, v___x_3174_);
v___x_3176_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__3));
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v_a_3163_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = l_Lean_Syntax_node3(v_a_3163_, v___x_3167_, v___x_3169_, v___x_3175_, v___x_3177_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v___x_3178_);
v___x_3180_ = v___x_3165_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = lean_array_fget(v_binders_3148_, v___x_3157_);
lean_dec_ref(v_binders_3148_);
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
return v___x_3184_;
}
}
else
{
lean_object* v_ref_3185_; uint8_t v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec_ref(v_binders_3148_);
v_ref_3185_ = lean_ctor_get(v___y_3154_, 5);
v___x_3186_ = 0;
v___x_3187_ = l_Lean_SourceInfo_fromRef(v_ref_3185_, v___x_3186_);
v___x_3188_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_3189_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
lean_inc(v___x_3187_);
v___x_3190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3187_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = l_Lean_Syntax_node1(v___x_3187_, v___x_3188_, v___x_3190_);
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
return v___x_3192_;
}
}
v___jp_3199_:
{
size_t v_sz_3208_; size_t v___x_3209_; lean_object* v___x_3210_; 
v_sz_3208_ = lean_array_size(v_loopMutVars_3136_);
v___x_3209_ = ((size_t)0ULL);
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(v_loopMutVars_3136_, v_sz_3208_, v___x_3209_, v_binders_3200_);
if (lean_obj_tag(v___x_3210_) == 0)
{
if (v_returnsEarly_3137_ == 0)
{
lean_object* v_a_3211_; 
lean_dec(v___x_3198_);
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v_binders_3148_ = v_a_3211_;
v___y_3149_ = v___y_3201_;
v___y_3150_ = v___y_3202_;
v___y_3151_ = v___y_3203_;
v___y_3152_ = v___y_3204_;
v___y_3153_ = v___y_3205_;
v___y_3154_ = v___y_3206_;
v___y_3155_ = v___y_3207_;
goto v___jp_3147_;
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; 
v_a_3212_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3213_ = lean_array_get_size(v_loopMutVars_3136_);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = lean_nat_dec_eq(v___x_3213_, v___x_3214_);
if (v___x_3215_ == 0)
{
lean_dec(v___x_3198_);
v_binders_3148_ = v_a_3212_;
v___y_3149_ = v___y_3201_;
v___y_3150_ = v___y_3202_;
v___y_3151_ = v___y_3203_;
v___y_3152_ = v___y_3204_;
v___y_3153_ = v___y_3205_;
v___y_3154_ = v___y_3206_;
v___y_3155_ = v___y_3207_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_array_push(v_a_3212_, v___x_3198_);
v_binders_3148_ = v___x_3216_;
v___y_3149_ = v___y_3201_;
v___y_3150_ = v___y_3202_;
v___y_3151_ = v___y_3203_;
v___y_3152_ = v___y_3204_;
v___y_3153_ = v___y_3205_;
v___y_3154_ = v___y_3206_;
v___y_3155_ = v___y_3207_;
goto v___jp_3147_;
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v___x_3198_);
v_a_3217_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3210_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3210_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___boxed(lean_object* v_loopMutVars_3227_, lean_object* v_returnsEarly_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
uint8_t v_returnsEarly_boxed_3237_; lean_object* v_res_3238_; 
v_returnsEarly_boxed_3237_ = lean_unbox(v_returnsEarly_3228_);
v_res_3238_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat(v_loopMutVars_3227_, v_returnsEarly_boxed_3237_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec_ref(v_loopMutVars_3227_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0(lean_object* v_as_3239_, size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_b_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(v_as_3239_, v_sz_3240_, v_i_3241_, v_b_3242_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___boxed(lean_object* v_as_3252_, lean_object* v_sz_3253_, lean_object* v_i_3254_, lean_object* v_b_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
size_t v_sz_boxed_3264_; size_t v_i_boxed_3265_; lean_object* v_res_3266_; 
v_sz_boxed_3264_ = lean_unbox_usize(v_sz_3253_);
lean_dec(v_sz_3253_);
v_i_boxed_3265_ = lean_unbox_usize(v_i_3254_);
lean_dec(v_i_3254_);
v_res_3266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0(v_as_3252_, v_sz_boxed_3264_, v_i_boxed_3265_, v_b_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec_ref(v_as_3252_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(lean_object* v_g_3267_, lean_object* v_e_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_ref_3271_; lean_object* v_statePat_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v_ref_3271_ = lean_ctor_get(v_a_3269_, 5);
v_statePat_3272_ = lean_ctor_get(v_g_3267_, 4);
lean_inc(v_statePat_3272_);
lean_dec_ref(v_g_3267_);
v___x_3273_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__0));
v___x_3274_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1));
v___x_3275_ = 0;
v___x_3276_ = l_Lean_SourceInfo_fromRef(v_ref_3271_, v___x_3275_);
lean_inc_n(v___x_3276_, 5);
v___x_3277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v___x_3273_);
v___x_3278_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3));
v___x_3279_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3280_ = l_Lean_Syntax_node1(v___x_3276_, v___x_3279_, v_statePat_3272_);
v___x_3281_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3276_);
lean_ctor_set(v___x_3282_, 1, v___x_3279_);
lean_ctor_set(v___x_3282_, 2, v___x_3281_);
v___x_3283_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_3284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3276_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = l_Lean_Syntax_node4(v___x_3276_, v___x_3278_, v___x_3280_, v___x_3282_, v___x_3284_, v_e_3268_);
v___x_3286_ = l_Lean_Syntax_node2(v___x_3276_, v___x_3274_, v___x_3277_, v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg___boxed(lean_object* v_g_3288_, lean_object* v_e_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(v_g_3288_, v_e_3289_, v_a_3290_);
lean_dec_ref(v_a_3290_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun(lean_object* v_g_3293_, lean_object* v_e_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(v_g_3293_, v_e_3294_, v_a_3300_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___boxed(lean_object* v_g_3304_, lean_object* v_e_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun(v_g_3304_, v_e_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
lean_dec_ref(v_a_3306_);
return v_res_3314_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__2));
v___x_3323_ = l_String_toRawSubstring_x27(v___x_3322_);
return v___x_3323_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__8(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__7));
v___x_3334_ = l_String_toRawSubstring_x27(v___x_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg(lean_object* v_g_3337_, lean_object* v_cursor_3338_, lean_object* v_e_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_ref_3342_; lean_object* v_quotContext_3343_; lean_object* v_currMacroScope_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v_statePat_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v_ref_3342_ = lean_ctor_get(v_a_3340_, 5);
v_quotContext_3343_ = lean_ctor_get(v_a_3340_, 10);
v_currMacroScope_3344_ = lean_ctor_get(v_a_3340_, 11);
v___x_3345_ = 0;
v___x_3346_ = l_Lean_SourceInfo_fromRef(v_ref_3342_, v___x_3345_);
v___x_3347_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__0));
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1));
lean_inc_n(v___x_3346_, 25);
v___x_3349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3346_);
lean_ctor_set(v___x_3349_, 1, v___x_3347_);
v___x_3350_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3));
v___x_3351_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
lean_inc(v_cursor_3338_);
v___x_3352_ = l_Lean_Syntax_node1(v___x_3346_, v___x_3351_, v_cursor_3338_);
v___x_3353_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3346_);
lean_ctor_set(v___x_3354_, 1, v___x_3351_);
lean_ctor_set(v___x_3354_, 2, v___x_3353_);
v___x_3355_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_3356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3346_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0));
v___x_3359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3346_);
lean_ctor_set(v___x_3359_, 1, v___x_3357_);
v___x_3360_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_3354_, 3);
v___x_3361_ = l_Lean_Syntax_node2(v___x_3346_, v___x_3360_, v___x_3354_, v_cursor_3338_);
v___x_3362_ = l_Lean_Syntax_node1(v___x_3346_, v___x_3351_, v___x_3361_);
v___x_3363_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_3364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3346_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_3366_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_3367_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_3368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3346_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__1));
v___x_3370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3346_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__3);
v_statePat_3372_ = lean_ctor_get(v_g_3337_, 4);
lean_inc(v_statePat_3372_);
lean_dec_ref(v_g_3337_);
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0));
v___x_3374_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3344_, 2);
lean_inc_n(v_quotContext_3343_, 2);
v___x_3375_ = l_Lean_addMacroScope(v_quotContext_3343_, v___x_3374_, v_currMacroScope_3344_);
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3346_);
lean_ctor_set(v___x_3377_, 1, v___x_3371_);
lean_ctor_set(v___x_3377_, 2, v___x_3375_);
lean_ctor_set(v___x_3377_, 3, v___x_3376_);
v___x_3378_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__6));
lean_inc_ref(v___x_3370_);
v___x_3379_ = l_Lean_Syntax_node2(v___x_3346_, v___x_3378_, v___x_3370_, v___x_3377_);
v___x_3380_ = l_Lean_Syntax_node1(v___x_3346_, v___x_3351_, v_statePat_3372_);
lean_inc(v___x_3380_);
v___x_3381_ = l_Lean_Syntax_node2(v___x_3346_, v___x_3373_, v___x_3379_, v___x_3380_);
v___x_3382_ = l_Lean_Syntax_node1(v___x_3346_, v___x_3351_, v___x_3381_);
v___x_3383_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__8, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__8_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__8);
v___x_3384_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__9));
v___x_3385_ = l_Lean_addMacroScope(v_quotContext_3343_, v___x_3384_, v_currMacroScope_3344_);
v___x_3386_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3346_);
lean_ctor_set(v___x_3386_, 1, v___x_3383_);
lean_ctor_set(v___x_3386_, 2, v___x_3385_);
lean_ctor_set(v___x_3386_, 3, v___x_3376_);
v___x_3387_ = l_Lean_Syntax_node2(v___x_3346_, v___x_3378_, v___x_3370_, v___x_3386_);
v___x_3388_ = l_Lean_Syntax_node2(v___x_3346_, v___x_3373_, v___x_3387_, v___x_3380_);
v___x_3389_ = l_Lean_Syntax_node1(v___x_3346_, v___x_3351_, v___x_3388_);
lean_inc_ref(v___x_3368_);
v___x_3390_ = l_Lean_Syntax_node3(v___x_3346_, v___x_3351_, v___x_3382_, v___x_3368_, v___x_3389_);
lean_inc_ref(v___x_3356_);
v___x_3391_ = l_Lean_Syntax_node4(v___x_3346_, v___x_3366_, v___x_3368_, v___x_3390_, v___x_3356_, v_e_3339_);
v___x_3392_ = l_Lean_Syntax_node1(v___x_3346_, v___x_3351_, v___x_3391_);
v___x_3393_ = l_Lean_Syntax_node1(v___x_3346_, v___x_3365_, v___x_3392_);
v___x_3394_ = l_Lean_Syntax_node6(v___x_3346_, v___x_3358_, v___x_3359_, v___x_3354_, v___x_3354_, v___x_3362_, v___x_3364_, v___x_3393_);
v___x_3395_ = l_Lean_Syntax_node4(v___x_3346_, v___x_3350_, v___x_3352_, v___x_3354_, v___x_3356_, v___x_3394_);
v___x_3396_ = l_Lean_Syntax_node2(v___x_3346_, v___x_3348_, v___x_3349_, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___boxed(lean_object* v_g_3398_, lean_object* v_cursor_3399_, lean_object* v_e_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg(v_g_3398_, v_cursor_3399_, v_e_3400_, v_a_3401_);
lean_dec_ref(v_a_3401_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun(lean_object* v_g_3404_, lean_object* v_cursor_3405_, lean_object* v_e_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg(v_g_3404_, v_cursor_3405_, v_e_3406_, v_a_3412_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___boxed(lean_object* v_g_3416_, lean_object* v_cursor_3417_, lean_object* v_e_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun(v_g_3416_, v_cursor_3417_, v_e_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
lean_dec(v_a_3425_);
lean_dec_ref(v_a_3424_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec_ref(v_a_3419_);
return v_res_3427_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0));
v___x_3430_ = l_Lean_stringToMessageData(v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(lean_object* v_g_3431_, lean_object* v_ref_3432_, lean_object* v_gadget_3433_, lean_object* v_annotations_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___x_3502_; lean_object* v_env_3503_; uint8_t v___x_3504_; uint8_t v___x_3505_; 
v___x_3502_ = lean_st_ref_get(v_a_3441_);
v_env_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc_ref(v_env_3503_);
lean_dec(v___x_3502_);
v___x_3504_ = 1;
lean_inc(v_gadget_3433_);
v___x_3505_ = l_Lean_Environment_contains(v_env_3503_, v_gadget_3433_, v___x_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v_gadget_3433_);
lean_dec_ref(v_g_3431_);
v___x_3506_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1);
v___x_3507_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_ref_3432_, v___x_3506_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
else
{
v___y_3444_ = v_a_3435_;
v___y_3445_ = v_a_3436_;
v___y_3446_ = v_a_3437_;
v___y_3447_ = v_a_3438_;
v___y_3448_ = v_a_3439_;
v___y_3449_ = v_a_3440_;
v___y_3450_ = v_a_3441_;
goto v___jp_3443_;
}
v___jp_3443_:
{
lean_object* v_xs_3451_; lean_object* v_init_3452_; lean_object* v_body_3453_; lean_object* v_00_u03c3_3454_; lean_object* v___x_3455_; 
v_xs_3451_ = lean_ctor_get(v_g_3431_, 0);
lean_inc_ref(v_xs_3451_);
v_init_3452_ = lean_ctor_get(v_g_3431_, 1);
lean_inc_ref(v_init_3452_);
v_body_3453_ = lean_ctor_get(v_g_3431_, 2);
lean_inc_ref(v_body_3453_);
v_00_u03c3_3454_ = lean_ctor_get(v_g_3431_, 3);
lean_inc_ref(v_00_u03c3_3454_);
lean_dec_ref(v_g_3431_);
v___x_3455_ = l_Lean_Elab_Term_exprToSyntax(v_xs_3451_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3457_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3457_ = l_Lean_Elab_Term_exprToSyntax(v_init_3452_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l_Lean_Elab_Term_exprToSyntax(v_body_3453_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_monadInfo_3460_; lean_object* v_a_3461_; lean_object* v_ref_3462_; lean_object* v_m_3463_; uint8_t v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_monadInfo_3460_ = lean_ctor_get(v___y_3444_, 0);
v_a_3461_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3459_, 1);
v_ref_3462_ = lean_ctor_get(v___y_3449_, 5);
v_m_3463_ = lean_ctor_get(v_monadInfo_3460_, 0);
v___x_3464_ = 0;
v___x_3465_ = l_Lean_SourceInfo_fromRef(v_ref_3462_, v___x_3464_);
v___x_3466_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3467_ = l_Array_mkArray3___redArg(v_a_3456_, v_a_3458_, v_a_3461_);
v___x_3468_ = l_Array_append___redArg(v___x_3467_, v_annotations_3434_);
lean_inc(v___x_3465_);
v___x_3469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3465_);
lean_ctor_set(v___x_3469_, 1, v___x_3466_);
lean_ctor_set(v___x_3469_, 2, v___x_3468_);
v___x_3470_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0));
v___x_3471_ = l_Lean_mkIdent(v_gadget_3433_);
v___x_3472_ = l_Lean_Syntax_node2(v___x_3465_, v___x_3470_, v___x_3471_, v___x_3469_);
lean_inc_ref(v_m_3463_);
v___x_3473_ = l_Lean_Expr_app___override(v_m_3463_, v_00_u03c3_3454_);
v___x_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
v___x_3475_ = 1;
v___x_3476_ = lean_box(0);
v___x_3477_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_3472_, v___x_3474_, v___x_3475_, v___x_3475_, v___x_3476_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
return v___x_3477_;
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec(v_a_3458_);
lean_dec(v_a_3456_);
lean_dec_ref(v_00_u03c3_3454_);
lean_dec(v_gadget_3433_);
v_a_3478_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3459_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3459_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec(v_a_3456_);
lean_dec_ref(v_00_u03c3_3454_);
lean_dec_ref(v_body_3453_);
lean_dec(v_gadget_3433_);
v_a_3486_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3457_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3457_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v_00_u03c3_3454_);
lean_dec_ref(v_body_3453_);
lean_dec_ref(v_init_3452_);
lean_dec(v_gadget_3433_);
v_a_3494_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3455_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3455_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___boxed(lean_object* v_g_3516_, lean_object* v_ref_3517_, lean_object* v_gadget_3518_, lean_object* v_annotations_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v_res_3528_; 
v_res_3528_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(v_g_3516_, v_ref_3517_, v_gadget_3518_, v_annotations_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec_ref(v_annotations_3519_);
lean_dec(v_ref_3517_);
return v_res_3528_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3529_ = lean_box(0);
v___x_3530_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v___x_3529_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg(){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0);
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___boxed(lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0(lean_object* v_00_u03b1_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___boxed(lean_object* v_00_u03b1_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0(v_00_u03b1_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3548_);
return v_res_3556_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__2));
v___x_3565_ = l_Lean_stringToMessageData(v___x_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(lean_object* v_invClause_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_invClause_3566_);
v___x_3602_ = l_Lean_Syntax_isOfKind(v_invClause_3566_, v___x_3601_);
if (v___x_3602_ == 0)
{
v___y_3576_ = v_a_3567_;
v___y_3577_ = v_a_3568_;
v___y_3578_ = v_a_3569_;
v___y_3579_ = v_a_3570_;
v___y_3580_ = v_a_3571_;
v___y_3581_ = v_a_3572_;
v___y_3582_ = v_a_3573_;
goto v___jp_3575_;
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3603_ = lean_unsigned_to_nat(1u);
v___x_3604_ = l_Lean_Syntax_getArg(v_invClause_3566_, v___x_3603_);
v___x_3605_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3));
lean_inc(v___x_3604_);
v___x_3606_ = l_Lean_Syntax_isOfKind(v___x_3604_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_dec(v___x_3604_);
v___y_3576_ = v_a_3567_;
v___y_3577_ = v_a_3568_;
v___y_3578_ = v_a_3569_;
v___y_3579_ = v_a_3570_;
v___y_3580_ = v_a_3571_;
v___y_3581_ = v_a_3572_;
v___y_3582_ = v_a_3573_;
goto v___jp_3575_;
}
else
{
lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3607_ = l_Lean_Syntax_getArg(v___x_3604_, v___x_3603_);
lean_dec(v___x_3604_);
lean_inc(v___x_3607_);
v___x_3608_ = l_Lean_Syntax_matchesNull(v___x_3607_, v___x_3603_);
if (v___x_3608_ == 0)
{
lean_dec(v___x_3607_);
v___y_3576_ = v_a_3567_;
v___y_3577_ = v_a_3568_;
v___y_3578_ = v_a_3569_;
v___y_3579_ = v_a_3570_;
v___y_3580_ = v_a_3571_;
v___y_3581_ = v_a_3572_;
v___y_3582_ = v_a_3573_;
goto v___jp_3575_;
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3610_ = l_Lean_Syntax_getArg(v___x_3607_, v___x_3609_);
lean_dec(v___x_3607_);
v___x_3611_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1));
lean_inc(v___x_3610_);
v___x_3612_ = l_Lean_Syntax_isOfKind(v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_dec(v___x_3610_);
v___y_3576_ = v_a_3567_;
v___y_3577_ = v_a_3568_;
v___y_3578_ = v_a_3569_;
v___y_3579_ = v_a_3570_;
v___y_3580_ = v_a_3571_;
v___y_3581_ = v_a_3572_;
v___y_3582_ = v_a_3573_;
goto v___jp_3575_;
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_invClause_3566_);
v___x_3613_ = l_Lean_Syntax_getArg(v___x_3610_, v___x_3603_);
lean_dec(v___x_3610_);
v___x_3614_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3);
v___x_3615_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v___x_3613_, v___x_3614_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
lean_dec(v___x_3613_);
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3615_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3615_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
}
v___jp_3575_:
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_invClause_3566_);
v___x_3584_ = l_Lean_Syntax_isOfKind(v_invClause_3566_, v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3585_; 
lean_dec(v_invClause_3566_);
v___x_3585_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_3585_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v___x_3586_ = lean_unsigned_to_nat(1u);
v___x_3587_ = l_Lean_Syntax_getArg(v_invClause_3566_, v___x_3586_);
lean_dec(v_invClause_3566_);
v___x_3588_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3));
lean_inc(v___x_3587_);
v___x_3589_ = l_Lean_Syntax_isOfKind(v___x_3587_, v___x_3588_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; 
lean_dec(v___x_3587_);
v___x_3590_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_3590_;
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v___x_3591_ = lean_unsigned_to_nat(0u);
v___x_3592_ = l_Lean_Syntax_getArg(v___x_3587_, v___x_3586_);
v___x_3593_ = l_Lean_Syntax_matchesNull(v___x_3592_, v___x_3591_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; 
lean_dec(v___x_3587_);
v___x_3594_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_3594_;
}
else
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_body_3597_; lean_object* v_binders_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3595_ = l_Lean_Syntax_getArg(v___x_3587_, v___x_3591_);
v___x_3596_ = lean_unsigned_to_nat(3u);
v_body_3597_ = l_Lean_Syntax_getArg(v___x_3587_, v___x_3596_);
lean_dec(v___x_3587_);
v_binders_3598_ = l_Lean_Syntax_getArgs(v___x_3595_);
lean_dec(v___x_3595_);
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v_binders_3598_);
lean_ctor_set(v___x_3599_, 1, v_body_3597_);
v___x_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
return v___x_3600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___boxed(lean_object* v_invClause_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_res_3633_; 
v_res_3633_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(v_invClause_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec_ref(v_a_3628_);
lean_dec(v_a_3627_);
lean_dec_ref(v_a_3626_);
lean_dec_ref(v_a_3625_);
return v_res_3633_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__6));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant(lean_object* v_g_3651_, lean_object* v_invClause_3652_, lean_object* v_h_x3f_3653_, lean_object* v_00_u03b1_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___x_3677_; 
lean_inc(v_invClause_3652_);
v___x_3677_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(v_invClause_3652_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v_fst_3679_; lean_object* v_snd_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3771_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
v_fst_3679_ = lean_ctor_get(v_a_3678_, 0);
v_snd_3680_ = lean_ctor_get(v_a_3678_, 1);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_a_3678_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3682_ = v_a_3678_;
v_isShared_3683_ = v_isSharedCheck_3771_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_snd_3680_);
lean_inc(v_fst_3679_);
lean_dec(v_a_3678_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3771_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3743_; 
if (lean_obj_tag(v_h_x3f_3653_) == 0)
{
lean_object* v___x_3768_; 
v___x_3768_ = lean_box(0);
v___y_3743_ = v___x_3768_;
goto v___jp_3742_;
}
else
{
lean_object* v_val_3769_; lean_object* v___x_3770_; 
v_val_3769_ = lean_ctor_get(v_h_x3f_3653_, 0);
lean_inc(v_val_3769_);
v___x_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3770_, 0, v_val_3769_);
v___y_3743_ = v___x_3770_;
goto v___jp_3742_;
}
v___jp_3684_:
{
lean_object* v___x_3692_; 
v___x_3692_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_a_3693_);
lean_dec_ref_known(v___x_3692_, 1);
v___x_3694_ = lean_unsigned_to_nat(2u);
v___x_3695_ = lean_unsigned_to_nat(0u);
v___x_3696_ = l_Array_extract___redArg(v_fst_3679_, v___x_3695_, v___x_3694_);
v___x_3697_ = lean_array_get_size(v_fst_3679_);
v___x_3698_ = l_Array_extract___redArg(v_fst_3679_, v___x_3694_, v___x_3697_);
lean_dec(v_fst_3679_);
v___x_3699_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0));
v___x_3700_ = lean_array_get_size(v___x_3698_);
v___x_3701_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(v_invClause_3652_, v___x_3699_, v___x_3700_, v_a_3693_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v___x_3702_; lean_object* v_a_3703_; lean_object* v___x_3704_; lean_object* v_a_3705_; lean_object* v_ref_3706_; uint8_t v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
lean_dec_ref_known(v___x_3701_, 1);
v___x_3702_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg(v___x_3698_, v_snd_3680_, v___y_3690_);
lean_dec_ref(v___x_3698_);
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
lean_dec_ref(v___x_3702_);
lean_inc_ref(v_g_3651_);
v___x_3704_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(v_g_3651_, v_a_3703_, v___y_3690_);
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref(v___x_3704_);
v_ref_3706_ = lean_ctor_get(v___y_3690_, 5);
v___x_3707_ = 0;
v___x_3708_ = l_Lean_SourceInfo_fromRef(v_ref_3706_, v___x_3707_);
v___x_3709_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__0));
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__1));
lean_inc(v___x_3708_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 2);
lean_ctor_set(v___x_3682_, 1, v___x_3709_);
lean_ctor_set(v___x_3682_, 0, v___x_3708_);
v___x_3712_ = v___x_3682_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3708_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3709_);
v___x_3712_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3713_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3));
v___x_3714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3715_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3716_ = l_Array_append___redArg(v___x_3715_, v___x_3696_);
lean_dec_ref(v___x_3696_);
lean_inc_n(v___x_3708_, 4);
v___x_3717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3708_);
lean_ctor_set(v___x_3717_, 1, v___x_3714_);
lean_ctor_set(v___x_3717_, 2, v___x_3716_);
v___x_3718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3708_);
lean_ctor_set(v___x_3718_, 1, v___x_3714_);
lean_ctor_set(v___x_3718_, 2, v___x_3715_);
v___x_3719_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_3720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3708_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = l_Lean_Syntax_node4(v___x_3708_, v___x_3713_, v___x_3717_, v___x_3718_, v___x_3720_, v_a_3705_);
v___x_3722_ = l_Lean_Syntax_node2(v___x_3708_, v___x_3710_, v___x_3712_, v___x_3721_);
if (lean_obj_tag(v_h_x3f_3653_) == 0)
{
lean_object* v___x_3723_; 
v___x_3723_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3));
v___y_3664_ = v___y_3688_;
v___y_3665_ = v___y_3685_;
v___y_3666_ = v___y_3687_;
v___y_3667_ = v___y_3691_;
v___y_3668_ = v___x_3722_;
v___y_3669_ = v___y_3689_;
v___y_3670_ = v___y_3686_;
v___y_3671_ = v___y_3690_;
v___y_3672_ = v___x_3723_;
goto v___jp_3663_;
}
else
{
lean_object* v___x_3724_; 
v___x_3724_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5));
v___y_3664_ = v___y_3688_;
v___y_3665_ = v___y_3685_;
v___y_3666_ = v___y_3687_;
v___y_3667_ = v___y_3691_;
v___y_3668_ = v___x_3722_;
v___y_3669_ = v___y_3689_;
v___y_3670_ = v___y_3686_;
v___y_3671_ = v___y_3690_;
v___y_3672_ = v___x_3724_;
goto v___jp_3663_;
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec_ref(v___x_3698_);
lean_dec_ref(v___x_3696_);
lean_del_object(v___x_3682_);
lean_dec(v_snd_3680_);
lean_dec(v_invClause_3652_);
lean_dec_ref(v_g_3651_);
v_a_3726_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3701_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3701_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_del_object(v___x_3682_);
lean_dec(v_snd_3680_);
lean_dec(v_fst_3679_);
lean_dec(v_invClause_3652_);
lean_dec_ref(v_g_3651_);
v_a_3734_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3692_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3692_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
v___jp_3742_:
{
lean_object* v_xs_3744_; lean_object* v_monadInfo_3745_; lean_object* v___x_3746_; 
v_xs_3744_ = lean_ctor_get(v_g_3651_, 0);
v_monadInfo_3745_ = lean_ctor_get(v_a_3655_, 0);
lean_inc_ref(v_monadInfo_3745_);
lean_inc_ref(v_xs_3744_);
v___x_3746_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_3652_, v___y_3743_, v_xs_3744_, v_00_u03b1_3654_, v_monadInfo_3745_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
lean_dec(v___y_3743_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v___x_3749_; 
lean_dec_ref_known(v___x_3746_, 1);
v___x_3747_ = lean_unsigned_to_nat(2u);
v___x_3748_ = lean_array_get_size(v_fst_3679_);
v___x_3749_ = lean_nat_dec_le(v___x_3747_, v___x_3748_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_del_object(v___x_3682_);
lean_dec(v_snd_3680_);
lean_dec(v_fst_3679_);
lean_dec_ref(v_g_3651_);
v___x_3750_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7);
v___x_3751_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_invClause_3652_, v___x_3750_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
lean_dec(v_invClause_3652_);
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
else
{
v___y_3685_ = v_a_3655_;
v___y_3686_ = v_a_3656_;
v___y_3687_ = v_a_3657_;
v___y_3688_ = v_a_3658_;
v___y_3689_ = v_a_3659_;
v___y_3690_ = v_a_3660_;
v___y_3691_ = v_a_3661_;
goto v___jp_3684_;
}
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
lean_del_object(v___x_3682_);
lean_dec(v_snd_3680_);
lean_dec(v_fst_3679_);
lean_dec(v_invClause_3652_);
lean_dec_ref(v_g_3651_);
v_a_3760_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3746_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3746_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec_ref(v_00_u03b1_3654_);
lean_dec(v_invClause_3652_);
lean_dec_ref(v_g_3651_);
v_a_3772_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3677_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3677_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
v___jp_3663_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3673_);
v___x_3675_ = lean_array_push(v___x_3674_, v___y_3668_);
lean_inc(v___y_3672_);
v___x_3676_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(v_g_3651_, v_invClause_3652_, v___y_3672_, v___x_3675_, v___y_3665_, v___y_3670_, v___y_3666_, v___y_3664_, v___y_3669_, v___y_3671_, v___y_3667_);
lean_dec_ref(v___x_3675_);
lean_dec(v_invClause_3652_);
return v___x_3676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___boxed(lean_object* v_g_3780_, lean_object* v_invClause_3781_, lean_object* v_h_x3f_3782_, lean_object* v_00_u03b1_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant(v_g_3780_, v_invClause_3781_, v_h_x3f_3782_, v_00_u03b1_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
lean_dec_ref(v_a_3784_);
lean_dec(v_h_x3f_3782_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(lean_object* v_val_3794_, lean_object* v_a_3795_, lean_object* v_g_3796_, lean_object* v_____x_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v_fst_3806_; lean_object* v_snd_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3836_; 
v_fst_3806_ = lean_ctor_get(v_____x_3797_, 0);
v_snd_3807_ = lean_ctor_get(v_____x_3797_, 1);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_____x_3797_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3809_ = v_____x_3797_;
v_isShared_3810_ = v_isSharedCheck_3836_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_snd_3807_);
lean_inc(v_fst_3806_);
lean_dec(v_____x_3797_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3836_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___closed__0));
v___x_3812_ = lean_array_get_size(v_fst_3806_);
v___x_3813_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(v_val_3794_, v___x_3811_, v___x_3812_, v_a_3795_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v___x_3814_; lean_object* v_a_3815_; lean_object* v___x_3816_; lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3827_; 
lean_dec_ref_known(v___x_3813_, 1);
v___x_3814_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg(v_fst_3806_, v_snd_3807_, v___y_3803_);
lean_dec(v_fst_3806_);
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref(v___x_3814_);
v___x_3816_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(v_g_3796_, v_a_3815_, v___y_3803_);
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3827_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3827_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 1, v_a_3817_);
lean_ctor_set(v___x_3809_, 0, v_val_3794_);
v___x_3822_ = v___x_3809_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_val_3794_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3824_; 
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 0, v___x_3822_);
v___x_3824_ = v___x_3819_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3822_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3809_);
lean_dec(v_snd_3807_);
lean_dec(v_fst_3806_);
lean_dec_ref(v_g_3796_);
lean_dec(v_val_3794_);
v_a_3828_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3813_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3813_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___boxed(lean_object* v_val_3837_, lean_object* v_a_3838_, lean_object* v_g_3839_, lean_object* v_____x_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(v_val_3837_, v_a_3838_, v_g_3839_, v_____x_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
return v_res_3849_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2));
v___x_3858_ = l_Lean_mkIdent(v___x_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(lean_object* v_g_3859_, lean_object* v___x_3860_, uint8_t v___x_3861_, lean_object* v___x_3862_, lean_object* v___x_3863_, lean_object* v___x_3864_, lean_object* v_val_3865_, lean_object* v_invBody_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3892_; 
v___x_3875_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg(v_g_3859_, v___x_3860_, v_invBody_3866_, v___y_3872_);
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3878_ = v___x_3875_;
v_isShared_3879_ = v_isSharedCheck_3892_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3875_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3892_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v_ref_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3890_; 
v_ref_3880_ = lean_ctor_get(v___y_3872_, 5);
v___x_3881_ = l_Lean_SourceInfo_fromRef(v_ref_3880_, v___x_3861_);
v___x_3882_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
v___x_3883_ = l_Lean_Name_mkStr4(v___x_3862_, v___x_3863_, v___x_3864_, v___x_3882_);
v___x_3884_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3);
v___x_3885_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
lean_inc(v___x_3881_);
v___x_3886_ = l_Lean_Syntax_node1(v___x_3881_, v___x_3885_, v_a_3876_);
v___x_3887_ = l_Lean_Syntax_node2(v___x_3881_, v___x_3883_, v___x_3884_, v___x_3886_);
v___x_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3888_, 0, v_val_3865_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v___x_3888_);
v___x_3890_ = v___x_3878_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3888_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___boxed(lean_object* v_g_3893_, lean_object* v___x_3894_, lean_object* v___x_3895_, lean_object* v___x_3896_, lean_object* v___x_3897_, lean_object* v___x_3898_, lean_object* v_val_3899_, lean_object* v_invBody_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
uint8_t v___x_19202__boxed_3909_; lean_object* v_res_3910_; 
v___x_19202__boxed_3909_ = lean_unbox(v___x_3895_);
v_res_3910_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(v_g_3893_, v___x_3894_, v___x_19202__boxed_3909_, v___x_3896_, v___x_3897_, v___x_3898_, v_val_3899_, v_invBody_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec_ref(v___y_3901_);
return v_res_3910_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__11(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__10));
v___x_3938_ = l_Lean_mkIdent(v___x_3937_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget(lean_object* v_g_3939_, lean_object* v_inv_x3f_3940_, lean_object* v_dec_x3f_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v_fst_3951_; lean_object* v_fst_3952_; lean_object* v_snd_3953_; lean_object* v___y_3973_; lean_object* v_a_3974_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___x_4013_; 
v___x_4013_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4154_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4016_ = v___x_4013_;
v_isShared_4017_ = v_isSharedCheck_4154_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4013_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4154_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v_a_4019_; lean_object* v___y_4053_; 
if (lean_obj_tag(v_inv_x3f_3940_) == 0)
{
lean_object* v___x_4066_; 
lean_del_object(v___x_4016_);
v___x_4066_ = lean_box(0);
v_a_4019_ = v___x_4066_;
goto v___jp_4018_;
}
else
{
lean_object* v_val_4067_; lean_object* v___x_4068_; 
v_val_4067_ = lean_ctor_get(v_inv_x3f_3940_, 0);
lean_inc_n(v_val_4067_, 2);
lean_dec_ref_known(v_inv_x3f_3940_, 1);
v___x_4068_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(v_val_4067_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; lean_object* v_fst_4070_; lean_object* v_snd_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4145_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v_fst_4070_ = lean_ctor_get(v_a_4069_, 0);
v_snd_4071_ = lean_ctor_get(v_a_4069_, 1);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_a_4069_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4073_ = v_a_4069_;
v_isShared_4074_ = v_isSharedCheck_4145_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_snd_4071_);
lean_inc(v_fst_4070_);
lean_dec(v_a_4069_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4145_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4075_ = lean_unsigned_to_nat(1u);
v___x_4076_ = lean_array_get_size(v_fst_4070_);
v___x_4077_ = l_Array_extract___redArg(v_fst_4070_, v___x_4075_, v___x_4076_);
v___x_4078_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0));
v___x_4079_ = lean_array_get_size(v___x_4077_);
lean_inc(v_a_4014_);
v___x_4080_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(v_val_4067_, v___x_4078_, v___x_4079_, v_a_4014_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v___x_4081_; lean_object* v_a_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_dec_ref_known(v___x_4080_, 1);
v___x_4081_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg(v___x_4077_, v_snd_4071_, v_a_3947_);
lean_dec_ref(v___x_4077_);
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref(v___x_4081_);
v___x_4083_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__7));
v___x_4084_ = l_Lean_Core_mkFreshUserName(v___x_4083_, v_a_3947_, v_a_3948_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
v___x_4086_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_4087_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_4088_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_4089_ = lean_box(0);
v___x_4090_ = lean_unsigned_to_nat(0u);
v___x_4091_ = lean_array_get(v___x_4089_, v_fst_4070_, v___x_4090_);
lean_dec(v_fst_4070_);
v___x_4092_ = 0;
v___x_4093_ = l_Lean_mkIdentFrom(v_val_4067_, v_a_4085_, v___x_4092_);
v___x_4094_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_4091_);
v___x_4095_ = l_Lean_Syntax_isOfKind(v___x_4091_, v___x_4094_);
if (v___x_4095_ == 0)
{
lean_object* v_ref_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4106_; 
v_ref_4096_ = lean_ctor_get(v_a_3947_, 5);
v___x_4097_ = l_Lean_SourceInfo_fromRef(v_ref_4096_, v___x_4095_);
v___x_4098_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0));
v___x_4099_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__11, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__11_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__11);
v___x_4100_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
lean_inc(v___x_4093_);
lean_inc_n(v___x_4097_, 3);
v___x_4101_ = l_Lean_Syntax_node1(v___x_4097_, v___x_4100_, v___x_4093_);
v___x_4102_ = l_Lean_Syntax_node2(v___x_4097_, v___x_4098_, v___x_4099_, v___x_4101_);
v___x_4103_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
v___x_4104_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCursorFun___redArg___closed__0));
if (v_isShared_4074_ == 0)
{
lean_ctor_set_tag(v___x_4073_, 2);
lean_ctor_set(v___x_4073_, 1, v___x_4103_);
lean_ctor_set(v___x_4073_, 0, v___x_4097_);
v___x_4106_ = v___x_4073_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4097_);
lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4103_);
v___x_4106_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4107_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
lean_inc_n(v___x_4097_, 11);
v___x_4108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4097_);
lean_ctor_set(v___x_4108_, 1, v___x_4100_);
lean_ctor_set(v___x_4108_, 2, v___x_4107_);
v___x_4109_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_4108_, 2);
v___x_4110_ = l_Lean_Syntax_node2(v___x_4097_, v___x_4109_, v___x_4108_, v___x_4102_);
v___x_4111_ = l_Lean_Syntax_node1(v___x_4097_, v___x_4100_, v___x_4110_);
v___x_4112_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_4113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4097_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_4115_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_4116_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_4117_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4097_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = l_Lean_Syntax_node1(v___x_4097_, v___x_4100_, v___x_4091_);
v___x_4119_ = l_Lean_Syntax_node1(v___x_4097_, v___x_4100_, v___x_4118_);
v___x_4120_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_4121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4097_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = l_Lean_Syntax_node4(v___x_4097_, v___x_4115_, v___x_4117_, v___x_4119_, v___x_4121_, v_a_4082_);
v___x_4123_ = l_Lean_Syntax_node1(v___x_4097_, v___x_4100_, v___x_4122_);
v___x_4124_ = l_Lean_Syntax_node1(v___x_4097_, v___x_4114_, v___x_4123_);
v___x_4125_ = l_Lean_Syntax_node6(v___x_4097_, v___x_4104_, v___x_4106_, v___x_4108_, v___x_4108_, v___x_4111_, v___x_4113_, v___x_4124_);
lean_inc_ref(v_g_3939_);
v___x_4126_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(v_g_3939_, v___x_4093_, v___x_4092_, v___x_4086_, v___x_4087_, v___x_4088_, v_val_4067_, v___x_4125_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
v___y_4053_ = v___x_4126_;
goto v___jp_4052_;
}
}
else
{
lean_object* v___x_4128_; 
lean_dec(v___x_4091_);
lean_del_object(v___x_4073_);
lean_inc_ref(v_g_3939_);
v___x_4128_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(v_g_3939_, v___x_4093_, v___x_4092_, v___x_4086_, v___x_4087_, v___x_4088_, v_val_4067_, v_a_4082_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
v___y_4053_ = v___x_4128_;
goto v___jp_4052_;
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec(v_a_4082_);
lean_del_object(v___x_4073_);
lean_dec(v_fst_4070_);
lean_dec(v_val_4067_);
lean_del_object(v___x_4016_);
lean_dec(v_a_4014_);
lean_dec(v_dec_x3f_3941_);
lean_dec_ref(v_g_3939_);
v_a_4129_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4084_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4084_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec_ref(v___x_4077_);
lean_del_object(v___x_4073_);
lean_dec(v_snd_4071_);
lean_dec(v_fst_4070_);
lean_dec(v_val_4067_);
lean_del_object(v___x_4016_);
lean_dec(v_a_4014_);
lean_dec(v_dec_x3f_3941_);
lean_dec_ref(v_g_3939_);
v_a_4137_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4080_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4080_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec(v_val_4067_);
lean_del_object(v___x_4016_);
lean_dec(v_a_4014_);
lean_dec(v_dec_x3f_3941_);
lean_dec_ref(v_g_3939_);
v_a_4146_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4068_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4068_);
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
v___jp_4018_:
{
if (lean_obj_tag(v_dec_x3f_3941_) == 0)
{
lean_object* v___x_4020_; 
lean_dec(v_a_4014_);
v___x_4020_ = lean_box(0);
v___y_3973_ = v_a_4019_;
v_a_3974_ = v___x_4020_;
goto v___jp_3972_;
}
else
{
lean_object* v_val_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v_val_4021_ = lean_ctor_get(v_dec_x3f_3941_, 0);
lean_inc_n(v_val_4021_, 2);
lean_dec_ref_known(v_dec_x3f_3941_, 1);
v___x_4022_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
v___x_4023_ = l_Lean_Syntax_isOfKind(v_val_4021_, v___x_4022_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec(v_val_4021_);
lean_dec(v_a_4019_);
lean_dec(v_a_4014_);
lean_dec_ref(v_g_3939_);
v___x_4024_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4024_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4024_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
else
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4033_ = lean_unsigned_to_nat(1u);
v___x_4034_ = l_Lean_Syntax_getArg(v_val_4021_, v___x_4033_);
v___x_4035_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___redArg___closed__3));
lean_inc(v___x_4034_);
v___x_4036_ = l_Lean_Syntax_isOfKind(v___x_4034_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4037_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
lean_ctor_set(v___x_4038_, 1, v___x_4034_);
lean_inc_ref(v_g_3939_);
v___x_4039_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(v_val_4021_, v_a_4014_, v_g_3939_, v___x_4038_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
v___y_4001_ = v_a_4019_;
v___y_4002_ = v___x_4039_;
goto v___jp_4000_;
}
else
{
lean_object* v___x_4040_; lean_object* v___x_4041_; uint8_t v___x_4042_; 
v___x_4040_ = lean_unsigned_to_nat(0u);
v___x_4041_ = l_Lean_Syntax_getArg(v___x_4034_, v___x_4033_);
v___x_4042_ = l_Lean_Syntax_matchesNull(v___x_4041_, v___x_4040_);
if (v___x_4042_ == 0)
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set(v___x_4044_, 1, v___x_4034_);
lean_inc_ref(v_g_3939_);
v___x_4045_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(v_val_4021_, v_a_4014_, v_g_3939_, v___x_4044_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
v___y_4001_ = v_a_4019_;
v___y_4002_ = v___x_4045_;
goto v___jp_4000_;
}
else
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4046_ = l_Lean_Syntax_getArg(v___x_4034_, v___x_4040_);
v___x_4047_ = lean_unsigned_to_nat(3u);
v___x_4048_ = l_Lean_Syntax_getArg(v___x_4034_, v___x_4047_);
lean_dec(v___x_4034_);
v___x_4049_ = l_Lean_Syntax_getArgs(v___x_4046_);
lean_dec(v___x_4046_);
v___x_4050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
lean_ctor_set(v___x_4050_, 1, v___x_4048_);
lean_inc_ref(v_g_3939_);
v___x_4051_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(v_val_4021_, v_a_4014_, v_g_3939_, v___x_4050_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
v___y_4001_ = v_a_4019_;
v___y_4002_ = v___x_4051_;
goto v___jp_4000_;
}
}
}
}
}
v___jp_4052_:
{
if (lean_obj_tag(v___y_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4056_; 
v_a_4054_ = lean_ctor_get(v___y_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref_known(v___y_4053_, 1);
if (v_isShared_4017_ == 0)
{
lean_ctor_set_tag(v___x_4016_, 1);
lean_ctor_set(v___x_4016_, 0, v_a_4054_);
v___x_4056_ = v___x_4016_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4054_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
v_a_4019_ = v___x_4056_;
goto v___jp_4018_;
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_del_object(v___x_4016_);
lean_dec(v_a_4014_);
lean_dec(v_dec_x3f_3941_);
lean_dec_ref(v_g_3939_);
v_a_4058_ = lean_ctor_get(v___y_4053_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___y_4053_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___y_4053_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___y_4053_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
}
else
{
lean_dec(v_dec_x3f_3941_);
lean_dec(v_inv_x3f_3940_);
lean_dec_ref(v_g_3939_);
return v___x_4013_;
}
v___jp_3950_:
{
lean_object* v___x_3954_; 
lean_inc(v_fst_3952_);
v___x_3954_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(v_g_3939_, v_fst_3951_, v_fst_3952_, v_snd_3953_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
lean_dec_ref(v_snd_3953_);
lean_dec(v_fst_3951_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3963_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3963_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3963_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3959_, 0, v_a_3955_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v___x_3959_);
v___x_3961_ = v___x_3957_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3959_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
v_a_3964_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3954_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3954_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
v___jp_3972_:
{
if (lean_obj_tag(v___y_3973_) == 0)
{
if (lean_obj_tag(v_a_3974_) == 0)
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
lean_dec_ref(v_g_3939_);
v___x_3975_ = lean_box(0);
v___x_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
return v___x_3976_;
}
else
{
lean_object* v_val_3977_; lean_object* v_fst_3978_; lean_object* v_snd_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v_val_3977_ = lean_ctor_get(v_a_3974_, 0);
lean_inc(v_val_3977_);
lean_dec_ref_known(v_a_3974_, 1);
v_fst_3978_ = lean_ctor_get(v_val_3977_, 0);
lean_inc(v_fst_3978_);
v_snd_3979_ = lean_ctor_get(v_val_3977_, 1);
lean_inc(v_snd_3979_);
lean_dec(v_val_3977_);
v___x_3980_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1));
v___x_3981_ = lean_unsigned_to_nat(1u);
v___x_3982_ = lean_mk_empty_array_with_capacity(v___x_3981_);
v___x_3983_ = lean_array_push(v___x_3982_, v_snd_3979_);
v_fst_3951_ = v_fst_3978_;
v_fst_3952_ = v___x_3980_;
v_snd_3953_ = v___x_3983_;
goto v___jp_3950_;
}
}
else
{
lean_object* v_val_3984_; 
v_val_3984_ = lean_ctor_get(v___y_3973_, 0);
lean_inc(v_val_3984_);
lean_dec_ref_known(v___y_3973_, 1);
if (lean_obj_tag(v_a_3974_) == 0)
{
lean_object* v_fst_3985_; lean_object* v_snd_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_fst_3985_ = lean_ctor_get(v_val_3984_, 0);
lean_inc(v_fst_3985_);
v_snd_3986_ = lean_ctor_get(v_val_3984_, 1);
lean_inc(v_snd_3986_);
lean_dec(v_val_3984_);
v___x_3987_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3));
v___x_3988_ = lean_unsigned_to_nat(1u);
v___x_3989_ = lean_mk_empty_array_with_capacity(v___x_3988_);
v___x_3990_ = lean_array_push(v___x_3989_, v_snd_3986_);
v_fst_3951_ = v_fst_3985_;
v_fst_3952_ = v___x_3987_;
v_snd_3953_ = v___x_3990_;
goto v___jp_3950_;
}
else
{
lean_object* v_val_3991_; lean_object* v_fst_3992_; lean_object* v_snd_3993_; lean_object* v_snd_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_val_3991_ = lean_ctor_get(v_a_3974_, 0);
lean_inc(v_val_3991_);
lean_dec_ref_known(v_a_3974_, 1);
v_fst_3992_ = lean_ctor_get(v_val_3984_, 0);
lean_inc(v_fst_3992_);
v_snd_3993_ = lean_ctor_get(v_val_3984_, 1);
lean_inc(v_snd_3993_);
lean_dec(v_val_3984_);
v_snd_3994_ = lean_ctor_get(v_val_3991_, 1);
lean_inc(v_snd_3994_);
lean_dec(v_val_3991_);
v___x_3995_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5));
v___x_3996_ = lean_unsigned_to_nat(2u);
v___x_3997_ = lean_mk_empty_array_with_capacity(v___x_3996_);
v___x_3998_ = lean_array_push(v___x_3997_, v_snd_3993_);
v___x_3999_ = lean_array_push(v___x_3998_, v_snd_3994_);
v_fst_3951_ = v_fst_3992_;
v_fst_3952_ = v___x_3995_;
v_snd_3953_ = v___x_3999_;
goto v___jp_3950_;
}
}
}
v___jp_4000_:
{
if (lean_obj_tag(v___y_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4004_; 
v_a_4003_ = lean_ctor_get(v___y_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref_known(v___y_4002_, 1);
v___x_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4004_, 0, v_a_4003_);
v___y_3973_ = v___y_4001_;
v_a_3974_ = v___x_4004_;
goto v___jp_3972_;
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_dec(v___y_4001_);
lean_dec_ref(v_g_3939_);
v_a_4005_ = lean_ctor_get(v___y_4002_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___y_4002_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___y_4002_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___y_4002_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___boxed(lean_object* v_g_4155_, lean_object* v_inv_x3f_4156_, lean_object* v_dec_x3f_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget(v_g_4155_, v_inv_x3f_4156_, v_dec_x3f_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec_ref(v_a_4158_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v_b_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v___x_4177_; 
lean_inc(v___y_4175_);
lean_inc_ref(v___y_4174_);
lean_inc(v___y_4173_);
lean_inc_ref(v___y_4172_);
lean_inc(v___y_4170_);
lean_inc_ref(v___y_4169_);
lean_inc_ref(v___y_4168_);
v___x_4177_ = lean_apply_9(v_k_4167_, v_b_4171_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, lean_box(0));
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v_b_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v_b_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec_ref(v___y_4179_);
return v_res_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_4189_, uint8_t v_bi_4190_, lean_object* v_type_4191_, lean_object* v_k_4192_, uint8_t v_kind_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v___f_4202_; lean_object* v___x_4203_; 
lean_inc(v___y_4196_);
lean_inc_ref(v___y_4195_);
lean_inc_ref(v___y_4194_);
v___f_4202_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_4202_, 0, v_k_4192_);
lean_closure_set(v___f_4202_, 1, v___y_4194_);
lean_closure_set(v___f_4202_, 2, v___y_4195_);
lean_closure_set(v___f_4202_, 3, v___y_4196_);
v___x_4203_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4189_, v_bi_4190_, v_type_4191_, v___f_4202_, v_kind_4193_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4203_) == 0)
{
return v___x_4203_;
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_4212_, lean_object* v_bi_4213_, lean_object* v_type_4214_, lean_object* v_k_4215_, lean_object* v_kind_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
uint8_t v_bi_boxed_4225_; uint8_t v_kind_boxed_4226_; lean_object* v_res_4227_; 
v_bi_boxed_4225_ = lean_unbox(v_bi_4213_);
v_kind_boxed_4226_ = lean_unbox(v_kind_4216_);
v_res_4227_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_4212_, v_bi_boxed_4225_, v_type_4214_, v_k_4215_, v_kind_boxed_4226_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec_ref(v___y_4217_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_4228_, lean_object* v_name_4229_, uint8_t v_bi_4230_, lean_object* v_type_4231_, lean_object* v_k_4232_, uint8_t v_kind_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_4229_, v_bi_4230_, v_type_4231_, v_k_4232_, v_kind_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_4243_, lean_object* v_name_4244_, lean_object* v_bi_4245_, lean_object* v_type_4246_, lean_object* v_k_4247_, lean_object* v_kind_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
uint8_t v_bi_boxed_4257_; uint8_t v_kind_boxed_4258_; lean_object* v_res_4259_; 
v_bi_boxed_4257_ = lean_unbox(v_bi_4245_);
v_kind_boxed_4258_ = lean_unbox(v_kind_4248_);
v_res_4259_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_4243_, v_name_4244_, v_bi_boxed_4257_, v_type_4246_, v_k_4247_, v_kind_boxed_4258_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec_ref(v___y_4249_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_4260_, lean_object* v_x_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v___x_4270_; 
v___x_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4270_, 0, v_a_4260_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_4271_, lean_object* v_x_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_4271_, v_x_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec_ref(v_x_4272_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v_x_4282_, lean_object* v___f_4283_, lean_object* v___x_4284_, lean_object* v_x_4285_, lean_object* v_x_4286_){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4287_ = l_Lean_TSyntax_getId(v_x_4282_);
v___x_4288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4287_);
lean_ctor_set(v___x_4288_, 1, v___f_4283_);
v___x_4289_ = lean_mk_empty_array_with_capacity(v___x_4284_);
v___x_4290_ = lean_array_push(v___x_4289_, v___x_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v_x_4291_, lean_object* v___f_4292_, lean_object* v___x_4293_, lean_object* v_x_4294_, lean_object* v_x_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l_Lean_Elab_Do_elabDoFor___lam__2(v_x_4291_, v___f_4292_, v___x_4293_, v_x_4294_, v_x_4295_);
lean_dec(v_x_4295_);
lean_dec(v_x_4294_);
lean_dec(v___x_4293_);
lean_dec(v_x_4291_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_a_4297_, lean_object* v___x_4298_, uint8_t v___x_4299_, lean_object* v_r_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_k_4309_; lean_object* v___x_4310_; 
v_k_4309_ = lean_ctor_get(v_a_4297_, 1);
lean_inc_ref(v_k_4309_);
lean_dec_ref(v_a_4297_);
lean_inc(v___y_4307_);
lean_inc_ref(v___y_4306_);
lean_inc(v___y_4305_);
lean_inc_ref(v___y_4304_);
lean_inc(v___y_4303_);
lean_inc_ref(v___y_4302_);
lean_inc_ref(v___y_4301_);
lean_inc_ref(v_r_4300_);
v___x_4310_ = lean_apply_9(v_k_4309_, v_r_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, lean_box(0));
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; uint8_t v___x_4315_; lean_object* v___x_4316_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
v___x_4312_ = lean_mk_empty_array_with_capacity(v___x_4298_);
v___x_4313_ = lean_array_push(v___x_4312_, v_r_4300_);
v___x_4314_ = 0;
v___x_4315_ = 1;
v___x_4316_ = l_Lean_Meta_mkLambdaFVars(v___x_4313_, v_a_4311_, v___x_4314_, v___x_4299_, v___x_4314_, v___x_4299_, v___x_4315_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec_ref(v___x_4313_);
return v___x_4316_;
}
else
{
lean_dec_ref(v_r_4300_);
return v___x_4310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_a_4317_, lean_object* v___x_4318_, lean_object* v___x_4319_, lean_object* v_r_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
uint8_t v___x_82366__boxed_4329_; lean_object* v_res_4330_; 
v___x_82366__boxed_4329_ = lean_unbox(v___x_4319_);
v_res_4330_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_a_4317_, v___x_4318_, v___x_82366__boxed_4329_, v_r_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___x_4318_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v___x_4331_, lean_object* v_as_4332_, size_t v_sz_4333_, size_t v_i_4334_, lean_object* v_b_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
uint8_t v___x_4343_; 
v___x_4343_ = lean_usize_dec_lt(v_i_4334_, v_sz_4333_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; 
lean_dec_ref(v___x_4331_);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_b_4335_);
return v___x_4344_;
}
else
{
lean_object* v_a_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v_a_4345_ = lean_array_uget_borrowed(v_as_4332_, v_i_4334_);
v___x_4346_ = l_Lean_Elab_Do_MutVar_getId(v_a_4345_);
v___x_4347_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4346_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; lean_object* v_ident_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; lean_object* v___x_4354_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc_n(v_a_4348_, 2);
lean_dec_ref_known(v___x_4347_, 1);
v_ident_4349_ = lean_ctor_get(v_a_4345_, 0);
v___x_4350_ = l_Lean_LocalDecl_toExpr(v_a_4348_);
v___x_4351_ = lean_box(0);
v___x_4352_ = lean_box(0);
v___x_4353_ = 0;
lean_inc_ref(v___x_4350_);
lean_inc(v_ident_4349_);
v___x_4354_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_4349_, v___x_4350_, v___x_4351_, v___x_4351_, v___x_4352_, v___x_4353_, v___x_4353_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
lean_dec_ref_known(v___x_4354_, 1);
v___x_4355_ = l_Lean_LocalDecl_type(v_a_4348_);
lean_dec(v_a_4348_);
v___x_4356_ = l_Lean_Meta_getDecLevel(v___x_4355_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v_u_4358_; lean_object* v___x_4359_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
v_u_4358_ = lean_ctor_get(v___x_4331_, 1);
lean_inc(v_u_4358_);
v___x_4359_ = l_Lean_Meta_isLevelDefEq(v_a_4357_, v_u_4358_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v___x_4360_; size_t v___x_4361_; size_t v___x_4362_; 
lean_dec_ref_known(v___x_4359_, 1);
v___x_4360_ = lean_array_push(v_b_4335_, v___x_4350_);
v___x_4361_ = ((size_t)1ULL);
v___x_4362_ = lean_usize_add(v_i_4334_, v___x_4361_);
v_i_4334_ = v___x_4362_;
v_b_4335_ = v___x_4360_;
goto _start;
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
lean_dec_ref(v___x_4350_);
lean_dec_ref(v_b_4335_);
lean_dec_ref(v___x_4331_);
v_a_4364_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4359_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4359_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec_ref(v___x_4350_);
lean_dec_ref(v_b_4335_);
lean_dec_ref(v___x_4331_);
v_a_4372_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4356_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4356_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec_ref(v___x_4350_);
lean_dec(v_a_4348_);
lean_dec_ref(v_b_4335_);
lean_dec_ref(v___x_4331_);
v_a_4380_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4354_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4354_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec_ref(v_b_4335_);
lean_dec_ref(v___x_4331_);
v_a_4388_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4347_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4347_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v___x_4396_, lean_object* v_as_4397_, lean_object* v_sz_4398_, lean_object* v_i_4399_, lean_object* v_b_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
size_t v_sz_boxed_4408_; size_t v_i_boxed_4409_; lean_object* v_res_4410_; 
v_sz_boxed_4408_ = lean_unbox_usize(v_sz_4398_);
lean_dec(v_sz_4398_);
v_i_boxed_4409_ = lean_unbox_usize(v_i_4399_);
lean_dec(v_i_4399_);
v_res_4410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v___x_4396_, v_as_4397_, v_sz_boxed_4408_, v_i_boxed_4409_, v_b_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec_ref(v_as_4397_);
return v_res_4410_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_box(1);
v___x_4412_ = l_Lean_MessageData_ofFormat(v___x_4411_);
return v___x_4412_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4416_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2));
v___x_4417_ = l_Lean_MessageData_ofFormat(v___x_4416_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(lean_object* v_x_4418_, lean_object* v_x_4419_){
_start:
{
if (lean_obj_tag(v_x_4419_) == 0)
{
return v_x_4418_;
}
else
{
lean_object* v_head_4420_; lean_object* v_tail_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4443_; 
v_head_4420_ = lean_ctor_get(v_x_4419_, 0);
v_tail_4421_ = lean_ctor_get(v_x_4419_, 1);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_x_4419_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4423_ = v_x_4419_;
v_isShared_4424_ = v_isSharedCheck_4443_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_tail_4421_);
lean_inc(v_head_4420_);
lean_dec(v_x_4419_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4443_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v_before_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4441_; 
v_before_4425_ = lean_ctor_get(v_head_4420_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v_head_4420_);
if (v_isSharedCheck_4441_ == 0)
{
lean_object* v_unused_4442_; 
v_unused_4442_ = lean_ctor_get(v_head_4420_, 1);
lean_dec(v_unused_4442_);
v___x_4427_ = v_head_4420_;
v_isShared_4428_ = v_isSharedCheck_4441_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_before_4425_);
lean_dec(v_head_4420_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4441_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
v___x_4429_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_4428_ == 0)
{
lean_ctor_set_tag(v___x_4427_, 7);
lean_ctor_set(v___x_4427_, 1, v___x_4429_);
lean_ctor_set(v___x_4427_, 0, v_x_4418_);
v___x_4431_ = v___x_4427_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_x_4418_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4432_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3);
if (v_isShared_4424_ == 0)
{
lean_ctor_set_tag(v___x_4423_, 7);
lean_ctor_set(v___x_4423_, 1, v___x_4432_);
lean_ctor_set(v___x_4423_, 0, v___x_4431_);
v___x_4434_ = v___x_4423_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4439_, 1, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4435_ = l_Lean_MessageData_ofSyntax(v_before_4425_);
v___x_4436_ = l_Lean_indentD(v___x_4435_);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4434_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v_x_4418_ = v___x_4437_;
v_x_4419_ = v_tail_4421_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(lean_object* v_opts_4444_, lean_object* v_opt_4445_){
_start:
{
lean_object* v_name_4446_; lean_object* v_defValue_4447_; lean_object* v_map_4448_; lean_object* v___x_4449_; 
v_name_4446_ = lean_ctor_get(v_opt_4445_, 0);
v_defValue_4447_ = lean_ctor_get(v_opt_4445_, 1);
v_map_4448_ = lean_ctor_get(v_opts_4444_, 0);
v___x_4449_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4448_, v_name_4446_);
if (lean_obj_tag(v___x_4449_) == 0)
{
uint8_t v___x_4450_; 
v___x_4450_ = lean_unbox(v_defValue_4447_);
return v___x_4450_;
}
else
{
lean_object* v_val_4451_; 
v_val_4451_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_val_4451_);
lean_dec_ref_known(v___x_4449_, 1);
if (lean_obj_tag(v_val_4451_) == 1)
{
uint8_t v_v_4452_; 
v_v_4452_ = lean_ctor_get_uint8(v_val_4451_, 0);
lean_dec_ref_known(v_val_4451_, 0);
return v_v_4452_;
}
else
{
uint8_t v___x_4453_; 
lean_dec(v_val_4451_);
v___x_4453_ = lean_unbox(v_defValue_4447_);
return v___x_4453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_4454_, lean_object* v_opt_4455_){
_start:
{
uint8_t v_res_4456_; lean_object* v_r_4457_; 
v_res_4456_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_opts_4454_, v_opt_4455_);
lean_dec_ref(v_opt_4455_);
lean_dec_ref(v_opts_4454_);
v_r_4457_ = lean_box(v_res_4456_);
return v_r_4457_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4461_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1));
v___x_4462_ = l_Lean_MessageData_ofFormat(v___x_4461_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(lean_object* v_msgData_4463_, lean_object* v_macroStack_4464_, lean_object* v___y_4465_){
_start:
{
lean_object* v_options_4467_; lean_object* v___x_4468_; uint8_t v___x_4469_; 
v_options_4467_ = lean_ctor_get(v___y_4465_, 2);
v___x_4468_ = l_Lean_Elab_pp_macroStack;
v___x_4469_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_options_4467_, v___x_4468_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4470_; 
lean_dec(v_macroStack_4464_);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v_msgData_4463_);
return v___x_4470_;
}
else
{
if (lean_obj_tag(v_macroStack_4464_) == 0)
{
lean_object* v___x_4471_; 
v___x_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4471_, 0, v_msgData_4463_);
return v___x_4471_;
}
else
{
lean_object* v_head_4472_; lean_object* v_after_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4488_; 
v_head_4472_ = lean_ctor_get(v_macroStack_4464_, 0);
lean_inc(v_head_4472_);
v_after_4473_ = lean_ctor_get(v_head_4472_, 1);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_head_4472_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; 
v_unused_4489_ = lean_ctor_get(v_head_4472_, 0);
lean_dec(v_unused_4489_);
v___x_4475_ = v_head_4472_;
v_isShared_4476_ = v_isSharedCheck_4488_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_after_4473_);
lean_dec(v_head_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4488_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4477_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_4476_ == 0)
{
lean_ctor_set_tag(v___x_4475_, 7);
lean_ctor_set(v___x_4475_, 1, v___x_4477_);
lean_ctor_set(v___x_4475_, 0, v_msgData_4463_);
v___x_4479_ = v___x_4475_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_msgData_4463_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v_msgData_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4480_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2);
v___x_4481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4479_);
lean_ctor_set(v___x_4481_, 1, v___x_4480_);
v___x_4482_ = l_Lean_MessageData_ofSyntax(v_after_4473_);
v___x_4483_ = l_Lean_indentD(v___x_4482_);
v_msgData_4484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4484_, 0, v___x_4481_);
lean_ctor_set(v_msgData_4484_, 1, v___x_4483_);
v___x_4485_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(v_msgData_4484_, v_macroStack_4464_);
v___x_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4485_);
return v___x_4486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_4490_, lean_object* v_macroStack_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_4490_, v_macroStack_4491_, v___y_4492_);
lean_dec_ref(v___y_4492_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(lean_object* v_msg_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v_ref_4503_; lean_object* v___x_4504_; lean_object* v_a_4505_; lean_object* v_macroStack_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4517_; 
v_ref_4503_ = lean_ctor_get(v___y_4500_, 5);
v___x_4504_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(v_msg_4495_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref(v___x_4504_);
v_macroStack_4506_ = lean_ctor_get(v___y_4496_, 1);
v___x_4507_ = l_Lean_Elab_getBetterRef(v_ref_4503_, v_macroStack_4506_);
lean_inc(v_macroStack_4506_);
v___x_4508_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_a_4505_, v_macroStack_4506_, v___y_4500_);
v_a_4509_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4511_ = v___x_4508_;
v_isShared_4512_ = v_isSharedCheck_4517_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4508_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4517_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4513_; lean_object* v___x_4515_; 
v___x_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4507_);
lean_ctor_set(v___x_4513_, 1, v_a_4509_);
if (v_isShared_4512_ == 0)
{
lean_ctor_set_tag(v___x_4511_, 1);
lean_ctor_set(v___x_4511_, 0, v___x_4513_);
v___x_4515_ = v___x_4511_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4513_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg___boxed(lean_object* v_msg_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4526_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = lean_box(0);
v___x_4533_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2));
v___x_4534_ = l_Lean_mkConst(v___x_4533_, v___x_4532_);
return v___x_4534_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5(void){
_start:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4));
v___x_4537_ = l_Lean_stringToMessageData(v___x_4536_);
return v___x_4537_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7(void){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4539_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6));
v___x_4540_ = l_Lean_stringToMessageData(v___x_4539_);
return v___x_4540_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9));
v___x_4545_ = l_Lean_MessageData_ofFormat(v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v___y_4546_, lean_object* v_monadInfo_4547_, uint8_t v_returnsEarly_4548_, lean_object* v___x_4549_, lean_object* v_a_4550_, uint8_t v___x_4551_, lean_object* v_e_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_defs_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___x_4584_; lean_object* v_returnVar_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4619_; lean_object* v___y_4620_; 
v___x_4584_ = lean_mk_empty_array_with_capacity(v___x_4549_);
if (lean_obj_tag(v_e_4552_) == 0)
{
if (v___x_4551_ == 0)
{
goto v___jp_4633_;
}
else
{
goto v___jp_4594_;
}
}
else
{
goto v___jp_4633_;
}
v___jp_4560_:
{
size_t v_sz_4568_; size_t v___x_4569_; lean_object* v___x_4570_; 
v_sz_4568_ = lean_array_size(v___y_4546_);
v___x_4569_ = ((size_t)0ULL);
v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v_monadInfo_4547_, v___y_4546_, v_sz_4568_, v___x_4569_, v_defs_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
if (lean_obj_tag(v___x_4570_) == 0)
{
if (v_returnsEarly_4548_ == 0)
{
return v___x_4570_;
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4572_; uint8_t v___x_4573_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
v___x_4572_ = lean_array_get_size(v___y_4546_);
v___x_4573_ = lean_nat_dec_eq(v___x_4572_, v___x_4549_);
if (v___x_4573_ == 0)
{
lean_dec(v_a_4571_);
return v___x_4570_;
}
else
{
lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4582_; 
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4582_ == 0)
{
lean_object* v_unused_4583_; 
v_unused_4583_ = lean_ctor_get(v___x_4570_, 0);
lean_dec(v_unused_4583_);
v___x_4575_ = v___x_4570_;
v_isShared_4576_ = v_isSharedCheck_4582_;
goto v_resetjp_4574_;
}
else
{
lean_dec(v___x_4570_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4582_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4577_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3);
v___x_4578_ = lean_array_push(v_a_4571_, v___x_4577_);
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 0, v___x_4578_);
v___x_4580_ = v___x_4575_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4578_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
else
{
return v___x_4570_;
}
}
v___jp_4585_:
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_array_push(v___x_4584_, v_returnVar_4586_);
v_defs_4561_ = v___x_4593_;
v___y_4562_ = v___y_4587_;
v___y_4563_ = v___y_4588_;
v___y_4564_ = v___y_4589_;
v___y_4565_ = v___y_4590_;
v___y_4566_ = v___y_4591_;
v___y_4567_ = v___y_4592_;
goto v___jp_4560_;
}
v___jp_4594_:
{
if (v_returnsEarly_4548_ == 0)
{
lean_dec(v_e_4552_);
lean_dec_ref(v_a_4550_);
v_defs_4561_ = v___x_4584_;
v___y_4562_ = v___y_4553_;
v___y_4563_ = v___y_4554_;
v___y_4564_ = v___y_4555_;
v___y_4565_ = v___y_4556_;
v___y_4566_ = v___y_4557_;
v___y_4567_ = v___y_4558_;
goto v___jp_4560_;
}
else
{
if (lean_obj_tag(v_e_4552_) == 0)
{
lean_object* v_resultType_4595_; lean_object* v___x_4596_; 
v_resultType_4595_ = lean_ctor_get(v_a_4550_, 0);
lean_inc_ref(v_resultType_4595_);
lean_dec_ref(v_a_4550_);
v___x_4596_ = l_Lean_Meta_mkNone(v_resultType_4595_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref_known(v___x_4596_, 1);
v_returnVar_4586_ = v_a_4597_;
v___y_4587_ = v___y_4553_;
v___y_4588_ = v___y_4554_;
v___y_4589_ = v___y_4555_;
v___y_4590_ = v___y_4556_;
v___y_4591_ = v___y_4557_;
v___y_4592_ = v___y_4558_;
goto v___jp_4585_;
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4605_; 
lean_dec_ref(v___x_4584_);
lean_dec_ref(v_monadInfo_4547_);
v_a_4598_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4600_ = v___x_4596_;
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4596_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4605_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4603_; 
if (v_isShared_4601_ == 0)
{
v___x_4603_ = v___x_4600_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4604_; 
v_reuseFailAlloc_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
v___x_4603_ = v_reuseFailAlloc_4604_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
return v___x_4603_;
}
}
}
}
else
{
lean_object* v_val_4606_; lean_object* v_resultType_4607_; lean_object* v___x_4608_; 
v_val_4606_ = lean_ctor_get(v_e_4552_, 0);
lean_inc(v_val_4606_);
lean_dec_ref_known(v_e_4552_, 1);
v_resultType_4607_ = lean_ctor_get(v_a_4550_, 0);
lean_inc_ref(v_resultType_4607_);
lean_dec_ref(v_a_4550_);
v___x_4608_ = l_Lean_Meta_mkSome(v_resultType_4607_, v_val_4606_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref_known(v___x_4608_, 1);
v_returnVar_4586_ = v_a_4609_;
v___y_4587_ = v___y_4553_;
v___y_4588_ = v___y_4554_;
v___y_4589_ = v___y_4555_;
v___y_4590_ = v___y_4556_;
v___y_4591_ = v___y_4557_;
v___y_4592_ = v___y_4558_;
goto v___jp_4585_;
}
else
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
lean_dec_ref(v___x_4584_);
lean_dec_ref(v_monadInfo_4547_);
v_a_4610_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4608_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4608_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
}
}
v___jp_4618_:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_inc_ref(v___y_4619_);
v___x_4621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4621_, 0, v___y_4619_);
lean_ctor_set(v___x_4621_, 1, v___y_4620_);
v___x_4622_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5);
v___x_4623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4621_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
v___x_4624_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v___x_4623_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
v_a_4625_ = lean_ctor_get(v___x_4624_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4624_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4624_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4624_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
v___jp_4633_:
{
if (v_returnsEarly_4548_ == 0)
{
lean_object* v___x_4634_; 
lean_dec_ref(v___x_4584_);
lean_dec_ref(v_a_4550_);
lean_dec_ref(v_monadInfo_4547_);
v___x_4634_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7);
if (lean_obj_tag(v_e_4552_) == 0)
{
lean_object* v___x_4635_; 
v___x_4635_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10);
v___y_4619_ = v___x_4634_;
v___y_4620_ = v___x_4635_;
goto v___jp_4618_;
}
else
{
lean_object* v_val_4636_; lean_object* v___x_4637_; 
v_val_4636_ = lean_ctor_get(v_e_4552_, 0);
lean_inc(v_val_4636_);
lean_dec_ref_known(v_e_4552_, 1);
v___x_4637_ = l_Lean_MessageData_ofExpr(v_val_4636_);
v___y_4619_ = v___x_4634_;
v___y_4620_ = v___x_4637_;
goto v___jp_4618_;
}
}
else
{
goto v___jp_4594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v___y_4638_, lean_object* v_monadInfo_4639_, lean_object* v_returnsEarly_4640_, lean_object* v___x_4641_, lean_object* v_a_4642_, lean_object* v___x_4643_, lean_object* v_e_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
uint8_t v_returnsEarly_boxed_4652_; uint8_t v___x_82772__boxed_4653_; lean_object* v_res_4654_; 
v_returnsEarly_boxed_4652_ = lean_unbox(v_returnsEarly_4640_);
v___x_82772__boxed_4653_ = lean_unbox(v___x_4643_);
v_res_4654_ = l_Lean_Elab_Do_elabDoFor___lam__3(v___y_4638_, v_monadInfo_4639_, v_returnsEarly_boxed_4652_, v___x_4641_, v_a_4642_, v___x_82772__boxed_4653_, v_e_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec(v___x_4641_);
lean_dec_ref(v___y_4638_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_name_4655_, lean_object* v_type_4656_, lean_object* v_k_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
uint8_t v___x_4666_; uint8_t v___x_4667_; lean_object* v___x_4668_; 
v___x_4666_ = 0;
v___x_4667_ = 0;
v___x_4668_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_4655_, v___x_4666_, v_type_4656_, v_k_4657_, v___x_4667_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_name_4669_, lean_object* v_type_4670_, lean_object* v_k_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_4669_, v_type_4670_, v_k_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec_ref(v___y_4675_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec_ref(v___y_4672_);
return v_res_4680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(uint8_t v_returnsEarly_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_doBlockResultType_4701_, lean_object* v_a_4702_, lean_object* v_v_4703_, lean_object* v_u_4704_, lean_object* v___f_4705_, lean_object* v___y_4706_, lean_object* v___x_4707_, lean_object* v___x_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v_ret_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; 
if (v_returnsEarly_4698_ == 0)
{
lean_object* v___x_4772_; 
lean_dec_ref(v___f_4705_);
lean_dec(v_u_4704_);
lean_dec(v_v_4703_);
lean_dec_ref(v_a_4702_);
lean_dec_ref(v_doBlockResultType_4701_);
lean_dec(v_a_4700_);
v___x_4772_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_4699_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
return v___x_4772_;
}
else
{
lean_object* v___x_4773_; 
v___x_4773_ = l_Lean_Meta_getFVarFromUserName(v_a_4700_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4775_; uint8_t v___x_4776_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref_known(v___x_4773_, 1);
v___x_4775_ = lean_array_get_size(v___y_4706_);
v___x_4776_ = lean_nat_dec_eq(v___x_4775_, v___x_4707_);
if (v___x_4776_ == 0)
{
v_ret_4718_ = v_a_4774_;
v___y_4719_ = v___y_4709_;
v___y_4720_ = v___y_4710_;
v___y_4721_ = v___y_4711_;
v___y_4722_ = v___y_4712_;
v___y_4723_ = v___y_4713_;
v___y_4724_ = v___y_4714_;
v___y_4725_ = v___y_4715_;
goto v___jp_4717_;
}
else
{
lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4777_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__9));
v___x_4778_ = lean_mk_empty_array_with_capacity(v___x_4708_);
v___x_4779_ = lean_array_push(v___x_4778_, v_a_4774_);
v___x_4780_ = l_Lean_Meta_mkAppM(v___x_4777_, v___x_4779_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref_known(v___x_4780_, 1);
v_ret_4718_ = v_a_4781_;
v___y_4719_ = v___y_4709_;
v___y_4720_ = v___y_4710_;
v___y_4721_ = v___y_4711_;
v___y_4722_ = v___y_4712_;
v___y_4723_ = v___y_4713_;
v___y_4724_ = v___y_4714_;
v___y_4725_ = v___y_4715_;
goto v___jp_4717_;
}
else
{
lean_dec_ref(v___f_4705_);
lean_dec(v_u_4704_);
lean_dec(v_v_4703_);
lean_dec_ref(v_a_4702_);
lean_dec_ref(v_doBlockResultType_4701_);
lean_dec_ref(v_a_4699_);
return v___x_4780_;
}
}
}
else
{
lean_dec_ref(v___f_4705_);
lean_dec(v_u_4704_);
lean_dec(v_v_4703_);
lean_dec_ref(v_a_4702_);
lean_dec_ref(v_doBlockResultType_4701_);
lean_dec_ref(v_a_4699_);
return v___x_4773_;
}
}
v___jp_4717_:
{
lean_object* v___x_4726_; 
lean_inc(v___y_4725_);
lean_inc_ref(v___y_4724_);
lean_inc(v___y_4723_);
lean_inc_ref(v___y_4722_);
lean_inc_ref(v_ret_4718_);
v___x_4726_ = lean_infer_type(v_ret_4718_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v___x_4728_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
lean_inc(v_a_4727_);
lean_dec_ref_known(v___x_4726_, 1);
v___x_4728_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4701_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4730_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v___x_4728_, 1);
v___x_4730_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_4699_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
v___x_4732_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__1));
v___x_4733_ = l_Lean_Core_mkFreshUserName(v___x_4732_, v___y_4724_, v___y_4725_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v_resultType_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4762_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
v_resultType_4735_ = lean_ctor_get(v_a_4702_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_a_4702_);
if (v_isSharedCheck_4762_ == 0)
{
lean_object* v_unused_4763_; 
v_unused_4763_ = lean_ctor_get(v_a_4702_, 1);
lean_dec(v_unused_4763_);
v___x_4737_ = v_a_4702_;
v_isShared_4738_ = v_isSharedCheck_4762_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_resultType_4735_);
lean_dec(v_a_4702_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4762_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4739_; uint8_t v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4746_; 
v___x_4739_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__2));
v___x_4740_ = 0;
v___x_4741_ = l_Lean_mkLambda(v___x_4739_, v___x_4740_, v_a_4727_, v_a_4729_);
v___x_4742_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__6));
v___x_4743_ = l_Lean_Level_succ___override(v_v_4703_);
v___x_4744_ = lean_box(0);
if (v_isShared_4738_ == 0)
{
lean_ctor_set_tag(v___x_4737_, 1);
lean_ctor_set(v___x_4737_, 1, v___x_4744_);
lean_ctor_set(v___x_4737_, 0, v___x_4743_);
v___x_4746_ = v___x_4737_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___x_4743_);
lean_ctor_set(v_reuseFailAlloc_4761_, 1, v___x_4744_);
v___x_4746_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4747_, 0, v_u_4704_);
lean_ctor_set(v___x_4747_, 1, v___x_4746_);
v___x_4748_ = l_Lean_mkConst(v___x_4742_, v___x_4747_);
lean_inc_ref(v_resultType_4735_);
v___x_4749_ = l_Lean_mkApp3(v___x_4748_, v_resultType_4735_, v___x_4741_, v_ret_4718_);
v___x_4750_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_a_4734_, v_resultType_4735_, v___f_4705_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v_a_4751_; lean_object* v___x_4753_; uint8_t v_isShared_4754_; uint8_t v_isSharedCheck_4760_; 
v_a_4751_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4753_ = v___x_4750_;
v_isShared_4754_ = v_isSharedCheck_4760_;
goto v_resetjp_4752_;
}
else
{
lean_inc(v_a_4751_);
lean_dec(v___x_4750_);
v___x_4753_ = lean_box(0);
v_isShared_4754_ = v_isSharedCheck_4760_;
goto v_resetjp_4752_;
}
v_resetjp_4752_:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4758_; 
v___x_4755_ = l_Lean_mkSimpleThunk(v_a_4731_);
v___x_4756_ = l_Lean_mkAppB(v___x_4749_, v_a_4751_, v___x_4755_);
if (v_isShared_4754_ == 0)
{
lean_ctor_set(v___x_4753_, 0, v___x_4756_);
v___x_4758_ = v___x_4753_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4756_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
else
{
lean_dec_ref(v___x_4749_);
lean_dec(v_a_4731_);
return v___x_4750_;
}
}
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_dec(v_a_4731_);
lean_dec(v_a_4729_);
lean_dec(v_a_4727_);
lean_dec_ref(v_ret_4718_);
lean_dec_ref(v___f_4705_);
lean_dec(v_u_4704_);
lean_dec(v_v_4703_);
lean_dec_ref(v_a_4702_);
v_a_4764_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4733_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4733_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
else
{
lean_dec(v_a_4729_);
lean_dec(v_a_4727_);
lean_dec_ref(v_ret_4718_);
lean_dec_ref(v___f_4705_);
lean_dec(v_u_4704_);
lean_dec(v_v_4703_);
lean_dec_ref(v_a_4702_);
return v___x_4730_;
}
}
else
{
lean_dec(v_a_4727_);
lean_dec_ref(v_ret_4718_);
lean_dec_ref(v___f_4705_);
lean_dec(v_u_4704_);
lean_dec(v_v_4703_);
lean_dec_ref(v_a_4702_);
lean_dec_ref(v_a_4699_);
return v___x_4728_;
}
}
else
{
lean_dec_ref(v_ret_4718_);
lean_dec_ref(v___f_4705_);
lean_dec(v_u_4704_);
lean_dec(v_v_4703_);
lean_dec_ref(v_a_4702_);
lean_dec_ref(v_doBlockResultType_4701_);
lean_dec_ref(v_a_4699_);
return v___x_4726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object** _args){
lean_object* v_returnsEarly_4782_ = _args[0];
lean_object* v_a_4783_ = _args[1];
lean_object* v_a_4784_ = _args[2];
lean_object* v_doBlockResultType_4785_ = _args[3];
lean_object* v_a_4786_ = _args[4];
lean_object* v_v_4787_ = _args[5];
lean_object* v_u_4788_ = _args[6];
lean_object* v___f_4789_ = _args[7];
lean_object* v___y_4790_ = _args[8];
lean_object* v___x_4791_ = _args[9];
lean_object* v___x_4792_ = _args[10];
lean_object* v___y_4793_ = _args[11];
lean_object* v___y_4794_ = _args[12];
lean_object* v___y_4795_ = _args[13];
lean_object* v___y_4796_ = _args[14];
lean_object* v___y_4797_ = _args[15];
lean_object* v___y_4798_ = _args[16];
lean_object* v___y_4799_ = _args[17];
lean_object* v___y_4800_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_4801_; lean_object* v_res_4802_; 
v_returnsEarly_boxed_4801_ = lean_unbox(v_returnsEarly_4782_);
v_res_4802_ = l_Lean_Elab_Do_elabDoFor___lam__4(v_returnsEarly_boxed_4801_, v_a_4783_, v_a_4784_, v_doBlockResultType_4785_, v_a_4786_, v_v_4787_, v_u_4788_, v___f_4789_, v___y_4790_, v___x_4791_, v___x_4792_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec_ref(v___y_4793_);
lean_dec(v___x_4792_);
lean_dec(v___x_4791_);
lean_dec_ref(v___y_4790_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___x_4805_, uint8_t v___x_4806_, lean_object* v_postS_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_){
_start:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4816_ = l_Lean_Expr_fvarId_x21(v_postS_4807_);
v___x_4817_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_4803_, v___x_4816_, v___y_4804_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; uint8_t v___x_4822_; lean_object* v___x_4823_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc(v_a_4818_);
lean_dec_ref_known(v___x_4817_, 1);
v___x_4819_ = lean_mk_empty_array_with_capacity(v___x_4805_);
v___x_4820_ = lean_array_push(v___x_4819_, v_postS_4807_);
v___x_4821_ = 0;
v___x_4822_ = 1;
v___x_4823_ = l_Lean_Meta_mkLambdaFVars(v___x_4820_, v_a_4818_, v___x_4821_, v___x_4806_, v___x_4821_, v___x_4806_, v___x_4822_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
lean_dec_ref(v___x_4820_);
return v___x_4823_;
}
else
{
lean_dec_ref(v_postS_4807_);
return v___x_4817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___x_4826_, lean_object* v___x_4827_, lean_object* v_postS_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
uint8_t v___x_83232__boxed_4837_; lean_object* v_res_4838_; 
v___x_83232__boxed_4837_ = lean_unbox(v___x_4827_);
v_res_4838_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___y_4824_, v___y_4825_, v___x_4826_, v___x_83232__boxed_4837_, v_postS_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec_ref(v___y_4829_);
lean_dec(v___x_4826_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_4840_, lean_object* v_u_4841_, lean_object* v___x_4842_, lean_object* v___x_4843_, lean_object* v_snd_4844_, lean_object* v___x_4845_, lean_object* v_e_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4855_, 0, v_e_4846_);
lean_inc(v___y_4853_);
lean_inc_ref(v___y_4852_);
lean_inc(v___y_4851_);
lean_inc_ref(v___y_4850_);
lean_inc(v___y_4849_);
lean_inc_ref(v___y_4848_);
v___x_4856_ = lean_apply_8(v___f_4840_, v___x_4855_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_, lean_box(0));
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v_a_4857_; lean_object* v___x_4858_; 
v_a_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc(v_a_4857_);
lean_dec_ref_known(v___x_4856_, 1);
v___x_4858_ = l_Lean_Meta_mkProdMkN(v_a_4857_, v_u_4841_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v_fst_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v___x_4858_, 1);
v_fst_4860_ = lean_ctor_get(v_a_4859_, 0);
lean_inc(v_fst_4860_);
lean_dec(v_a_4859_);
v___x_4861_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_4862_ = l_Lean_Name_mkStr2(v___x_4842_, v___x_4861_);
v___x_4863_ = l_Lean_mkConst(v___x_4862_, v___x_4843_);
v___x_4864_ = l_Lean_mkAppB(v___x_4863_, v_snd_4844_, v_fst_4860_);
v___x_4865_ = l_Lean_Elab_Do_mkPureApp(v___x_4845_, v___x_4864_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
return v___x_4865_;
}
else
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4873_; 
lean_dec_ref(v___x_4845_);
lean_dec_ref(v_snd_4844_);
lean_dec(v___x_4843_);
lean_dec_ref(v___x_4842_);
v_a_4866_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4868_ = v___x_4858_;
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4858_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4871_; 
if (v_isShared_4869_ == 0)
{
v___x_4871_ = v___x_4868_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_dec_ref(v___x_4845_);
lean_dec_ref(v_snd_4844_);
lean_dec(v___x_4843_);
lean_dec_ref(v___x_4842_);
lean_dec(v_u_4841_);
v_a_4874_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4856_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4856_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_4882_, lean_object* v_u_4883_, lean_object* v___x_4884_, lean_object* v___x_4885_, lean_object* v_snd_4886_, lean_object* v___x_4887_, lean_object* v_e_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_4882_, v_u_4883_, v___x_4884_, v___x_4885_, v_snd_4886_, v___x_4887_, v_e_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
lean_dec_ref(v___y_4889_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___f_4899_, lean_object* v___x_4900_, lean_object* v_u_4901_, lean_object* v___x_4902_, lean_object* v___x_4903_, lean_object* v_snd_4904_, lean_object* v___x_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4914_; 
lean_inc(v___y_4912_);
lean_inc_ref(v___y_4911_);
lean_inc(v___y_4910_);
lean_inc_ref(v___y_4909_);
lean_inc(v___y_4908_);
lean_inc_ref(v___y_4907_);
v___x_4914_ = lean_apply_8(v___f_4899_, v___x_4900_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, lean_box(0));
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4916_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = l_Lean_Meta_mkProdMkN(v_a_4915_, v_u_4901_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; lean_object* v_fst_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
lean_inc(v_a_4917_);
lean_dec_ref_known(v___x_4916_, 1);
v_fst_4918_ = lean_ctor_get(v_a_4917_, 0);
lean_inc(v_fst_4918_);
lean_dec(v_a_4917_);
v___x_4919_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__7___closed__0));
v___x_4920_ = l_Lean_Name_mkStr2(v___x_4902_, v___x_4919_);
v___x_4921_ = l_Lean_mkConst(v___x_4920_, v___x_4903_);
v___x_4922_ = l_Lean_mkAppB(v___x_4921_, v_snd_4904_, v_fst_4918_);
v___x_4923_ = l_Lean_Elab_Do_mkPureApp(v___x_4905_, v___x_4922_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
return v___x_4923_;
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
lean_dec_ref(v___x_4905_);
lean_dec_ref(v_snd_4904_);
lean_dec(v___x_4903_);
lean_dec_ref(v___x_4902_);
v_a_4924_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4916_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4916_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
else
{
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
lean_dec_ref(v___x_4905_);
lean_dec_ref(v_snd_4904_);
lean_dec(v___x_4903_);
lean_dec_ref(v___x_4902_);
lean_dec(v_u_4901_);
v_a_4932_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4914_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4914_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4937_; 
if (v_isShared_4935_ == 0)
{
v___x_4937_ = v___x_4934_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___f_4940_, lean_object* v___x_4941_, lean_object* v_u_4942_, lean_object* v___x_4943_, lean_object* v___x_4944_, lean_object* v_snd_4945_, lean_object* v___x_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___f_4940_, v___x_4941_, v_u_4942_, v___x_4943_, v___x_4944_, v_snd_4945_, v___x_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
lean_dec(v___y_4953_);
lean_dec_ref(v___y_4952_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec_ref(v___y_4947_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v___f_4956_, lean_object* v___x_4957_, lean_object* v_u_4958_, lean_object* v___x_4959_, lean_object* v___x_4960_, lean_object* v_snd_4961_, lean_object* v___x_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v___x_4971_; 
lean_inc(v___y_4969_);
lean_inc_ref(v___y_4968_);
lean_inc(v___y_4967_);
lean_inc_ref(v___y_4966_);
lean_inc(v___y_4965_);
lean_inc_ref(v___y_4964_);
v___x_4971_ = lean_apply_8(v___f_4956_, v___x_4957_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, lean_box(0));
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v___x_4973_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_a_4972_);
lean_dec_ref_known(v___x_4971_, 1);
v___x_4973_ = l_Lean_Meta_mkProdMkN(v_a_4972_, v_u_4958_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v_fst_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
lean_inc(v_a_4974_);
lean_dec_ref_known(v___x_4973_, 1);
v_fst_4975_ = lean_ctor_get(v_a_4974_, 0);
lean_inc(v_fst_4975_);
lean_dec(v_a_4974_);
v___x_4976_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_4977_ = l_Lean_Name_mkStr2(v___x_4959_, v___x_4976_);
v___x_4978_ = l_Lean_mkConst(v___x_4977_, v___x_4960_);
v___x_4979_ = l_Lean_mkAppB(v___x_4978_, v_snd_4961_, v_fst_4975_);
v___x_4980_ = l_Lean_Elab_Do_mkPureApp(v___x_4962_, v___x_4979_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
return v___x_4980_;
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec_ref(v___x_4962_);
lean_dec_ref(v_snd_4961_);
lean_dec(v___x_4960_);
lean_dec_ref(v___x_4959_);
v_a_4981_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4973_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4973_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_dec_ref(v___x_4962_);
lean_dec_ref(v_snd_4961_);
lean_dec(v___x_4960_);
lean_dec_ref(v___x_4959_);
lean_dec(v_u_4958_);
v_a_4989_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4971_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4971_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object* v___f_4997_, lean_object* v___x_4998_, lean_object* v_u_4999_, lean_object* v___x_5000_, lean_object* v___x_5001_, lean_object* v_snd_5002_, lean_object* v___x_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
lean_object* v_res_5012_; 
v_res_5012_ = l_Lean_Elab_Do_elabDoFor___lam__8(v___f_4997_, v___x_4998_, v_u_4999_, v___x_5000_, v___x_5001_, v_snd_5002_, v___x_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
lean_dec(v___y_5010_);
lean_dec_ref(v___y_5009_);
lean_dec(v___y_5008_);
lean_dec_ref(v___y_5007_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec_ref(v___y_5004_);
return v_res_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v___x_5013_, lean_object* v___f_5014_, lean_object* v___f_5015_, lean_object* v___x_5016_, lean_object* v___x_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_monadInfo_5026_; lean_object* v_mutVars_5027_; lean_object* v_mutVarDefs_5028_; lean_object* v_contInfo_5029_; uint8_t v_deadCode_5030_; lean_object* v_ops_5031_; lean_object* v___x_5033_; uint8_t v_isShared_5034_; uint8_t v_isSharedCheck_5039_; 
v_monadInfo_5026_ = lean_ctor_get(v___y_5018_, 0);
v_mutVars_5027_ = lean_ctor_get(v___y_5018_, 1);
v_mutVarDefs_5028_ = lean_ctor_get(v___y_5018_, 2);
v_contInfo_5029_ = lean_ctor_get(v___y_5018_, 4);
v_deadCode_5030_ = lean_ctor_get_uint8(v___y_5018_, sizeof(void*)*6);
v_ops_5031_ = lean_ctor_get(v___y_5018_, 5);
v_isSharedCheck_5039_ = !lean_is_exclusive(v___y_5018_);
if (v_isSharedCheck_5039_ == 0)
{
lean_object* v_unused_5040_; 
v_unused_5040_ = lean_ctor_get(v___y_5018_, 3);
lean_dec(v_unused_5040_);
v___x_5033_ = v___y_5018_;
v_isShared_5034_ = v_isSharedCheck_5039_;
goto v_resetjp_5032_;
}
else
{
lean_inc(v_ops_5031_);
lean_inc(v_contInfo_5029_);
lean_inc(v_mutVarDefs_5028_);
lean_inc(v_mutVars_5027_);
lean_inc(v_monadInfo_5026_);
lean_dec(v___y_5018_);
v___x_5033_ = lean_box(0);
v_isShared_5034_ = v_isSharedCheck_5039_;
goto v_resetjp_5032_;
}
v_resetjp_5032_:
{
lean_object* v___x_5036_; 
if (v_isShared_5034_ == 0)
{
lean_ctor_set(v___x_5033_, 3, v___x_5013_);
v___x_5036_ = v___x_5033_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5038_; 
v_reuseFailAlloc_5038_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5038_, 0, v_monadInfo_5026_);
lean_ctor_set(v_reuseFailAlloc_5038_, 1, v_mutVars_5027_);
lean_ctor_set(v_reuseFailAlloc_5038_, 2, v_mutVarDefs_5028_);
lean_ctor_set(v_reuseFailAlloc_5038_, 3, v___x_5013_);
lean_ctor_set(v_reuseFailAlloc_5038_, 4, v_contInfo_5029_);
lean_ctor_set(v_reuseFailAlloc_5038_, 5, v_ops_5031_);
lean_ctor_set_uint8(v_reuseFailAlloc_5038_, sizeof(void*)*6, v_deadCode_5030_);
v___x_5036_ = v_reuseFailAlloc_5038_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5037_; 
v___x_5037_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_5014_, v___f_5015_, v___x_5016_, v___x_5017_, v___x_5036_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec_ref(v___x_5036_);
return v___x_5037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object* v___x_5041_, lean_object* v___f_5042_, lean_object* v___f_5043_, lean_object* v___x_5044_, lean_object* v___x_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_Elab_Do_elabDoFor___lam__9(v___x_5041_, v___f_5042_, v___f_5043_, v___x_5044_, v___x_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
lean_dec(v___y_5048_);
lean_dec_ref(v___y_5047_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_u_5060_, lean_object* v_snd_5061_, lean_object* v___f_5062_, lean_object* v___x_5063_, lean_object* v_body_5064_, uint8_t v___x_5065_, lean_object* v___y_5066_, lean_object* v_xh_5067_, lean_object* v_loopS_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v_resultType_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5114_; 
v_resultType_5077_ = lean_ctor_get(v_a_5058_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v_a_5058_);
if (v_isSharedCheck_5114_ == 0)
{
lean_object* v_unused_5115_; 
v_unused_5115_ = lean_ctor_get(v_a_5058_, 1);
lean_dec(v_unused_5115_);
v___x_5079_ = v_a_5058_;
v_isShared_5080_ = v_isSharedCheck_5114_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_resultType_5077_);
lean_dec(v_a_5058_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5114_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v_resultName_5081_; lean_object* v_resultType_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5112_; 
v_resultName_5081_ = lean_ctor_get(v_a_5059_, 0);
v_resultType_5082_ = lean_ctor_get(v_a_5059_, 1);
v_isSharedCheck_5112_ = !lean_is_exclusive(v_a_5059_);
if (v_isSharedCheck_5112_ == 0)
{
lean_object* v_unused_5113_; 
v_unused_5113_ = lean_ctor_get(v_a_5059_, 2);
lean_dec(v_unused_5113_);
v___x_5084_ = v_a_5059_;
v_isShared_5085_ = v_isSharedCheck_5112_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_resultType_5082_);
lean_inc(v_resultName_5081_);
lean_dec(v_a_5059_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5112_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___f_5093_; lean_object* v___f_5094_; lean_object* v___f_5095_; lean_object* v___x_5097_; 
v___x_5086_ = l_Lean_Expr_fvarId_x21(v_loopS_5068_);
v___x_5087_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0));
v___x_5088_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_5089_ = lean_box(0);
lean_inc_n(v_u_5060_, 3);
v___x_5090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5090_, 0, v_u_5060_);
lean_ctor_set(v___x_5090_, 1, v___x_5089_);
lean_inc_ref_n(v___x_5090_, 3);
v___x_5091_ = l_Lean_mkConst(v___x_5088_, v___x_5090_);
lean_inc_ref_n(v_snd_5061_, 3);
v___x_5092_ = l_Lean_Expr_app___override(v___x_5091_, v_snd_5061_);
lean_inc_ref_n(v___x_5092_, 3);
lean_inc_ref_n(v___f_5062_, 2);
v___f_5093_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 6);
lean_closure_set(v___f_5093_, 0, v___f_5062_);
lean_closure_set(v___f_5093_, 1, v_u_5060_);
lean_closure_set(v___f_5093_, 2, v___x_5087_);
lean_closure_set(v___f_5093_, 3, v___x_5090_);
lean_closure_set(v___f_5093_, 4, v_snd_5061_);
lean_closure_set(v___f_5093_, 5, v___x_5092_);
lean_inc(v___x_5063_);
v___f_5094_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 15, 7);
lean_closure_set(v___f_5094_, 0, v___f_5062_);
lean_closure_set(v___f_5094_, 1, v___x_5063_);
lean_closure_set(v___f_5094_, 2, v_u_5060_);
lean_closure_set(v___f_5094_, 3, v___x_5087_);
lean_closure_set(v___f_5094_, 4, v___x_5090_);
lean_closure_set(v___f_5094_, 5, v_snd_5061_);
lean_closure_set(v___f_5094_, 6, v___x_5092_);
v___f_5095_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 15, 7);
lean_closure_set(v___f_5095_, 0, v___f_5062_);
lean_closure_set(v___f_5095_, 1, v___x_5063_);
lean_closure_set(v___f_5095_, 2, v_u_5060_);
lean_closure_set(v___f_5095_, 3, v___x_5087_);
lean_closure_set(v___f_5095_, 4, v___x_5090_);
lean_closure_set(v___f_5095_, 5, v_snd_5061_);
lean_closure_set(v___f_5095_, 6, v___x_5092_);
if (v_isShared_5080_ == 0)
{
lean_ctor_set(v___x_5079_, 1, v___f_5093_);
v___x_5097_ = v___x_5079_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v_resultType_5077_);
lean_ctor_set(v_reuseFailAlloc_5111_, 1, v___f_5093_);
v___x_5097_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
uint8_t v___x_5098_; lean_object* v___x_5100_; 
v___x_5098_ = 1;
lean_inc_ref(v___f_5094_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 2, v___f_5094_);
v___x_5100_ = v___x_5084_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_resultName_5081_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v_resultType_5082_);
lean_ctor_set(v_reuseFailAlloc_5110_, 2, v___f_5094_);
v___x_5100_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___f_5103_; lean_object* v___x_5104_; 
lean_ctor_set_uint8(v___x_5100_, sizeof(void*)*3, v___x_5098_);
v___x_5101_ = lean_box(v___x_5065_);
v___x_5102_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_5102_, 0, v_body_5064_);
lean_closure_set(v___x_5102_, 1, v___x_5100_);
lean_closure_set(v___x_5102_, 2, v___x_5101_);
v___f_5103_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 13, 5);
lean_closure_set(v___f_5103_, 0, v___x_5092_);
lean_closure_set(v___f_5103_, 1, v___f_5095_);
lean_closure_set(v___f_5103_, 2, v___f_5094_);
lean_closure_set(v___f_5103_, 3, v___x_5097_);
lean_closure_set(v___f_5103_, 4, v___x_5102_);
v___x_5104_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_5066_, v___x_5086_, v___f_5103_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v___x_5106_; uint8_t v___x_5107_; uint8_t v___x_5108_; lean_object* v___x_5109_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_a_5105_);
lean_dec_ref_known(v___x_5104_, 1);
v___x_5106_ = lean_array_push(v_xh_5067_, v_loopS_5068_);
v___x_5107_ = 0;
v___x_5108_ = 1;
v___x_5109_ = l_Lean_Meta_mkLambdaFVars(v___x_5106_, v_a_5105_, v___x_5107_, v___x_5065_, v___x_5107_, v___x_5065_, v___x_5108_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
lean_dec_ref(v___x_5106_);
return v___x_5109_;
}
else
{
lean_dec_ref(v_loopS_5068_);
lean_dec_ref(v_xh_5067_);
return v___x_5104_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_a_5116_ = _args[0];
lean_object* v_a_5117_ = _args[1];
lean_object* v_u_5118_ = _args[2];
lean_object* v_snd_5119_ = _args[3];
lean_object* v___f_5120_ = _args[4];
lean_object* v___x_5121_ = _args[5];
lean_object* v_body_5122_ = _args[6];
lean_object* v___x_5123_ = _args[7];
lean_object* v___y_5124_ = _args[8];
lean_object* v_xh_5125_ = _args[9];
lean_object* v_loopS_5126_ = _args[10];
lean_object* v___y_5127_ = _args[11];
lean_object* v___y_5128_ = _args[12];
lean_object* v___y_5129_ = _args[13];
lean_object* v___y_5130_ = _args[14];
lean_object* v___y_5131_ = _args[15];
lean_object* v___y_5132_ = _args[16];
lean_object* v___y_5133_ = _args[17];
lean_object* v___y_5134_ = _args[18];
_start:
{
uint8_t v___x_83641__boxed_5135_; lean_object* v_res_5136_; 
v___x_83641__boxed_5135_ = lean_unbox(v___x_5123_);
v_res_5136_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_a_5116_, v_a_5117_, v_u_5118_, v_snd_5119_, v___f_5120_, v___x_5121_, v_body_5122_, v___x_83641__boxed_5135_, v___y_5124_, v_xh_5125_, v_loopS_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
lean_dec(v___y_5133_);
lean_dec_ref(v___y_5132_);
lean_dec(v___y_5131_);
lean_dec_ref(v___y_5130_);
lean_dec(v___y_5129_);
lean_dec_ref(v___y_5128_);
lean_dec_ref(v___y_5127_);
return v_res_5136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___x_5137_, lean_object* v___x_5138_, lean_object* v_x_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_u_5142_, lean_object* v_snd_5143_, lean_object* v___f_5144_, lean_object* v___x_5145_, lean_object* v_body_5146_, uint8_t v___x_5147_, lean_object* v___y_5148_, lean_object* v_a_5149_, lean_object* v_h_x3f_5150_, lean_object* v___x_5151_, lean_object* v_xh_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_){
_start:
{
lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5161_ = lean_array_get_borrowed(v___x_5137_, v_xh_5152_, v___x_5138_);
lean_inc(v___x_5161_);
v___x_5162_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_5139_, v___x_5161_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v___x_5163_; lean_object* v___f_5164_; lean_object* v___y_5166_; lean_object* v___y_5167_; lean_object* v___y_5168_; lean_object* v___y_5169_; lean_object* v___y_5170_; lean_object* v___y_5171_; lean_object* v___y_5172_; 
lean_dec_ref_known(v___x_5162_, 1);
v___x_5163_ = lean_box(v___x_5147_);
lean_inc_ref(v_xh_5152_);
lean_inc_ref(v_snd_5143_);
v___f_5164_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 10);
lean_closure_set(v___f_5164_, 0, v_a_5140_);
lean_closure_set(v___f_5164_, 1, v_a_5141_);
lean_closure_set(v___f_5164_, 2, v_u_5142_);
lean_closure_set(v___f_5164_, 3, v_snd_5143_);
lean_closure_set(v___f_5164_, 4, v___f_5144_);
lean_closure_set(v___f_5164_, 5, v___x_5145_);
lean_closure_set(v___f_5164_, 6, v_body_5146_);
lean_closure_set(v___f_5164_, 7, v___x_5163_);
lean_closure_set(v___f_5164_, 8, v___y_5148_);
lean_closure_set(v___f_5164_, 9, v_xh_5152_);
if (lean_obj_tag(v_h_x3f_5150_) == 1)
{
lean_object* v_val_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; 
v_val_5176_ = lean_ctor_get(v_h_x3f_5150_, 0);
lean_inc(v_val_5176_);
lean_dec_ref_known(v_h_x3f_5150_, 1);
v___x_5177_ = lean_array_get(v___x_5137_, v_xh_5152_, v___x_5151_);
lean_dec_ref(v_xh_5152_);
v___x_5178_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_5176_, v___x_5177_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_dec_ref_known(v___x_5178_, 1);
v___y_5166_ = v___y_5153_;
v___y_5167_ = v___y_5154_;
v___y_5168_ = v___y_5155_;
v___y_5169_ = v___y_5156_;
v___y_5170_ = v___y_5157_;
v___y_5171_ = v___y_5158_;
v___y_5172_ = v___y_5159_;
goto v___jp_5165_;
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
lean_dec_ref(v___f_5164_);
lean_dec(v_a_5149_);
lean_dec_ref(v_snd_5143_);
v_a_5179_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5178_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5178_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
else
{
lean_dec_ref(v_xh_5152_);
lean_dec(v_h_x3f_5150_);
v___y_5166_ = v___y_5153_;
v___y_5167_ = v___y_5154_;
v___y_5168_ = v___y_5155_;
v___y_5169_ = v___y_5156_;
v___y_5170_ = v___y_5157_;
v___y_5171_ = v___y_5158_;
v___y_5172_ = v___y_5159_;
goto v___jp_5165_;
}
v___jp_5165_:
{
uint8_t v___x_5173_; uint8_t v___x_5174_; lean_object* v___x_5175_; 
v___x_5173_ = 0;
v___x_5174_ = 1;
v___x_5175_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_5149_, v___x_5173_, v_snd_5143_, v___f_5164_, v___x_5174_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_);
return v___x_5175_;
}
}
else
{
lean_object* v_a_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5194_; 
lean_dec_ref(v_xh_5152_);
lean_dec(v_h_x3f_5150_);
lean_dec(v_a_5149_);
lean_dec(v___y_5148_);
lean_dec(v_body_5146_);
lean_dec(v___x_5145_);
lean_dec_ref(v___f_5144_);
lean_dec_ref(v_snd_5143_);
lean_dec(v_u_5142_);
lean_dec_ref(v_a_5141_);
lean_dec_ref(v_a_5140_);
v_a_5187_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5189_ = v___x_5162_;
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_a_5187_);
lean_dec(v___x_5162_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5192_; 
if (v_isShared_5190_ == 0)
{
v___x_5192_ = v___x_5189_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object** _args){
lean_object* v___x_5195_ = _args[0];
lean_object* v___x_5196_ = _args[1];
lean_object* v_x_5197_ = _args[2];
lean_object* v_a_5198_ = _args[3];
lean_object* v_a_5199_ = _args[4];
lean_object* v_u_5200_ = _args[5];
lean_object* v_snd_5201_ = _args[6];
lean_object* v___f_5202_ = _args[7];
lean_object* v___x_5203_ = _args[8];
lean_object* v_body_5204_ = _args[9];
lean_object* v___x_5205_ = _args[10];
lean_object* v___y_5206_ = _args[11];
lean_object* v_a_5207_ = _args[12];
lean_object* v_h_x3f_5208_ = _args[13];
lean_object* v___x_5209_ = _args[14];
lean_object* v_xh_5210_ = _args[15];
lean_object* v___y_5211_ = _args[16];
lean_object* v___y_5212_ = _args[17];
lean_object* v___y_5213_ = _args[18];
lean_object* v___y_5214_ = _args[19];
lean_object* v___y_5215_ = _args[20];
lean_object* v___y_5216_ = _args[21];
lean_object* v___y_5217_ = _args[22];
lean_object* v___y_5218_ = _args[23];
_start:
{
uint8_t v___x_83764__boxed_5219_; lean_object* v_res_5220_; 
v___x_83764__boxed_5219_ = lean_unbox(v___x_5205_);
v_res_5220_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___x_5195_, v___x_5196_, v_x_5197_, v_a_5198_, v_a_5199_, v_u_5200_, v_snd_5201_, v___f_5202_, v___x_5203_, v_body_5204_, v___x_83764__boxed_5219_, v___y_5206_, v_a_5207_, v_h_x3f_5208_, v___x_5209_, v_xh_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___x_5209_);
lean_dec(v___x_5196_);
lean_dec_ref(v___x_5195_);
return v_res_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v___x_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_val_5231_, lean_object* v_a_5232_, lean_object* v_x_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_){
_start:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; 
v___x_5242_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_5243_ = lean_box(0);
v___x_5244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5244_, 0, v_a_5226_);
lean_ctor_set(v___x_5244_, 1, v___x_5243_);
v___x_5245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5245_, 0, v_a_5227_);
lean_ctor_set(v___x_5245_, 1, v___x_5244_);
v___x_5246_ = l_Lean_mkConst(v___x_5242_, v___x_5245_);
v___x_5247_ = l_Lean_instInhabitedExpr;
v___x_5248_ = lean_array_get_borrowed(v___x_5247_, v_x_5233_, v___x_5228_);
lean_inc(v___x_5248_);
v___x_5249_ = l_Lean_mkApp5(v___x_5246_, v_a_5229_, v_a_5230_, v_val_5231_, v_a_5232_, v___x_5248_);
v___x_5250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5249_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v___x_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_, lean_object* v_val_5256_, lean_object* v_a_5257_, lean_object* v_x_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v_res_5267_; 
v_res_5267_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_5251_, v_a_5252_, v___x_5253_, v_a_5254_, v_a_5255_, v_val_5256_, v_a_5257_, v_x_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec_ref(v___y_5259_);
lean_dec_ref(v_x_5258_);
lean_dec(v___x_5253_);
return v_res_5267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(size_t v_sz_5268_, size_t v_i_5269_, lean_object* v_bs_5270_){
_start:
{
uint8_t v___x_5271_; 
v___x_5271_ = lean_usize_dec_lt(v_i_5269_, v_sz_5268_);
if (v___x_5271_ == 0)
{
return v_bs_5270_;
}
else
{
lean_object* v_v_5272_; lean_object* v___x_5273_; lean_object* v_bs_x27_5274_; lean_object* v___x_5275_; size_t v___x_5276_; size_t v___x_5277_; lean_object* v___x_5278_; 
v_v_5272_ = lean_array_uget(v_bs_5270_, v_i_5269_);
v___x_5273_ = lean_unsigned_to_nat(0u);
v_bs_x27_5274_ = lean_array_uset(v_bs_5270_, v_i_5269_, v___x_5273_);
v___x_5275_ = l_Lean_Elab_Do_MutVar_getId(v_v_5272_);
lean_dec(v_v_5272_);
v___x_5276_ = ((size_t)1ULL);
v___x_5277_ = lean_usize_add(v_i_5269_, v___x_5276_);
v___x_5278_ = lean_array_uset(v_bs_x27_5274_, v_i_5269_, v___x_5275_);
v_i_5269_ = v___x_5277_;
v_bs_5270_ = v___x_5278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_sz_5280_, lean_object* v_i_5281_, lean_object* v_bs_5282_){
_start:
{
size_t v_sz_boxed_5283_; size_t v_i_boxed_5284_; lean_object* v_res_5285_; 
v_sz_boxed_5283_ = lean_unbox_usize(v_sz_5280_);
lean_dec(v_sz_5280_);
v_i_boxed_5284_ = lean_unbox_usize(v_i_5281_);
lean_dec(v_i_5281_);
v_res_5285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_boxed_5283_, v_i_boxed_5284_, v_bs_5282_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_a_5286_, lean_object* v_as_5287_, size_t v_i_5288_, size_t v_stop_5289_, lean_object* v_b_5290_){
_start:
{
lean_object* v___y_5292_; uint8_t v___x_5296_; 
v___x_5296_ = lean_usize_dec_eq(v_i_5288_, v_stop_5289_);
if (v___x_5296_ == 0)
{
lean_object* v_reassigns_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; uint8_t v___x_5300_; 
v_reassigns_5297_ = lean_ctor_get(v_a_5286_, 1);
v___x_5298_ = lean_array_uget_borrowed(v_as_5287_, v_i_5288_);
v___x_5299_ = l_Lean_Elab_Do_MutVar_getId(v___x_5298_);
v___x_5300_ = l_Lean_NameSet_contains(v_reassigns_5297_, v___x_5299_);
lean_dec(v___x_5299_);
if (v___x_5300_ == 0)
{
v___y_5292_ = v_b_5290_;
goto v___jp_5291_;
}
else
{
lean_object* v___x_5301_; 
lean_inc(v___x_5298_);
v___x_5301_ = lean_array_push(v_b_5290_, v___x_5298_);
v___y_5292_ = v___x_5301_;
goto v___jp_5291_;
}
}
else
{
return v_b_5290_;
}
v___jp_5291_:
{
size_t v___x_5293_; size_t v___x_5294_; 
v___x_5293_ = ((size_t)1ULL);
v___x_5294_ = lean_usize_add(v_i_5288_, v___x_5293_);
v_i_5288_ = v___x_5294_;
v_b_5290_ = v___y_5292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_a_5302_, lean_object* v_as_5303_, lean_object* v_i_5304_, lean_object* v_stop_5305_, lean_object* v_b_5306_){
_start:
{
size_t v_i_boxed_5307_; size_t v_stop_boxed_5308_; lean_object* v_res_5309_; 
v_i_boxed_5307_ = lean_unbox_usize(v_i_5304_);
lean_dec(v_i_5304_);
v_stop_boxed_5308_ = lean_unbox_usize(v_stop_5305_);
lean_dec(v_stop_5305_);
v_res_5309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_5302_, v_as_5303_, v_i_boxed_5307_, v_stop_boxed_5308_, v_b_5306_);
lean_dec_ref(v_as_5303_);
lean_dec_ref(v_a_5302_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(lean_object* v___x_5310_, lean_object* v_a_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
lean_object* v___x_5320_; lean_object* v___x_82204__overap_5321_; lean_object* v___x_5322_; 
v___x_5320_ = l_Lean_instInhabitedExpr;
v___x_82204__overap_5321_ = l_instInhabitedOfMonad___redArg(v___x_5310_, v___x_5320_);
lean_inc(v___y_5318_);
lean_inc_ref(v___y_5317_);
lean_inc(v___y_5316_);
lean_inc_ref(v___y_5315_);
lean_inc(v___y_5314_);
lean_inc_ref(v___y_5313_);
lean_inc_ref(v___y_5312_);
v___x_5322_ = lean_apply_8(v___x_82204__overap_5321_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_, lean_box(0));
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed(lean_object* v___x_5323_, lean_object* v_a_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v_res_5333_; 
v_res_5333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(v___x_5323_, v_a_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
lean_dec_ref(v___y_5325_);
lean_dec_ref(v_a_5324_);
return v_res_5333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = l_instMonadEIO(lean_box(0));
return v___x_5334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1(void){
_start:
{
lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5335_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0);
v___x_5336_ = l_StateRefT_x27_instMonad___redArg(v___x_5335_);
return v___x_5336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed(lean_object* v_acc_5343_, lean_object* v_declInfos_5344_, lean_object* v_k_5345_, lean_object* v_kind_5346_, lean_object* v_x_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
uint8_t v_kind_boxed_5356_; lean_object* v_res_5357_; 
v_kind_boxed_5356_ = lean_unbox(v_kind_5346_);
v_res_5357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(v_acc_5343_, v_declInfos_5344_, v_k_5345_, v_kind_boxed_5356_, v_x_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec_ref(v___y_5348_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(lean_object* v_declInfos_5358_, lean_object* v_k_5359_, uint8_t v_kind_5360_, lean_object* v_acc_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_){
_start:
{
lean_object* v___x_5370_; lean_object* v_toApplicative_5371_; lean_object* v_toFunctor_5372_; lean_object* v_toSeq_5373_; lean_object* v_toSeqLeft_5374_; lean_object* v_toSeqRight_5375_; lean_object* v___f_5376_; lean_object* v___f_5377_; lean_object* v___f_5378_; lean_object* v___f_5379_; lean_object* v___x_5380_; lean_object* v___f_5381_; lean_object* v___f_5382_; lean_object* v___f_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v_toApplicative_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5467_; 
v___x_5370_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1);
v_toApplicative_5371_ = lean_ctor_get(v___x_5370_, 0);
v_toFunctor_5372_ = lean_ctor_get(v_toApplicative_5371_, 0);
v_toSeq_5373_ = lean_ctor_get(v_toApplicative_5371_, 2);
v_toSeqLeft_5374_ = lean_ctor_get(v_toApplicative_5371_, 3);
v_toSeqRight_5375_ = lean_ctor_get(v_toApplicative_5371_, 4);
v___f_5376_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2));
v___f_5377_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_5372_, 2);
v___f_5378_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5378_, 0, v_toFunctor_5372_);
v___f_5379_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5379_, 0, v_toFunctor_5372_);
v___x_5380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5380_, 0, v___f_5378_);
lean_ctor_set(v___x_5380_, 1, v___f_5379_);
lean_inc(v_toSeqRight_5375_);
v___f_5381_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5381_, 0, v_toSeqRight_5375_);
lean_inc(v_toSeqLeft_5374_);
v___f_5382_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5382_, 0, v_toSeqLeft_5374_);
lean_inc(v_toSeq_5373_);
v___f_5383_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5383_, 0, v_toSeq_5373_);
v___x_5384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5384_, 0, v___x_5380_);
lean_ctor_set(v___x_5384_, 1, v___f_5376_);
lean_ctor_set(v___x_5384_, 2, v___f_5383_);
lean_ctor_set(v___x_5384_, 3, v___f_5382_);
lean_ctor_set(v___x_5384_, 4, v___f_5381_);
v___x_5385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5385_, 0, v___x_5384_);
lean_ctor_set(v___x_5385_, 1, v___f_5377_);
v___x_5386_ = l_StateRefT_x27_instMonad___redArg(v___x_5385_);
v_toApplicative_5387_ = lean_ctor_get(v___x_5386_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5467_ == 0)
{
lean_object* v_unused_5468_; 
v_unused_5468_ = lean_ctor_get(v___x_5386_, 1);
lean_dec(v_unused_5468_);
v___x_5389_ = v___x_5386_;
v_isShared_5390_ = v_isSharedCheck_5467_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_toApplicative_5387_);
lean_dec(v___x_5386_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5467_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v_toFunctor_5391_; lean_object* v_toSeq_5392_; lean_object* v_toSeqLeft_5393_; lean_object* v_toSeqRight_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5465_; 
v_toFunctor_5391_ = lean_ctor_get(v_toApplicative_5387_, 0);
v_toSeq_5392_ = lean_ctor_get(v_toApplicative_5387_, 2);
v_toSeqLeft_5393_ = lean_ctor_get(v_toApplicative_5387_, 3);
v_toSeqRight_5394_ = lean_ctor_get(v_toApplicative_5387_, 4);
v_isSharedCheck_5465_ = !lean_is_exclusive(v_toApplicative_5387_);
if (v_isSharedCheck_5465_ == 0)
{
lean_object* v_unused_5466_; 
v_unused_5466_ = lean_ctor_get(v_toApplicative_5387_, 1);
lean_dec(v_unused_5466_);
v___x_5396_ = v_toApplicative_5387_;
v_isShared_5397_ = v_isSharedCheck_5465_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_toSeqRight_5394_);
lean_inc(v_toSeqLeft_5393_);
lean_inc(v_toSeq_5392_);
lean_inc(v_toFunctor_5391_);
lean_dec(v_toApplicative_5387_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5465_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___f_5398_; lean_object* v___f_5399_; lean_object* v___f_5400_; lean_object* v___f_5401_; lean_object* v___x_5402_; lean_object* v___f_5403_; lean_object* v___f_5404_; lean_object* v___f_5405_; lean_object* v___x_5407_; 
v___f_5398_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4));
v___f_5399_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5));
lean_inc_ref(v_toFunctor_5391_);
v___f_5400_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5400_, 0, v_toFunctor_5391_);
v___f_5401_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5401_, 0, v_toFunctor_5391_);
v___x_5402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5402_, 0, v___f_5400_);
lean_ctor_set(v___x_5402_, 1, v___f_5401_);
v___f_5403_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5403_, 0, v_toSeqRight_5394_);
v___f_5404_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5404_, 0, v_toSeqLeft_5393_);
v___f_5405_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5405_, 0, v_toSeq_5392_);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 4, v___f_5403_);
lean_ctor_set(v___x_5396_, 3, v___f_5404_);
lean_ctor_set(v___x_5396_, 2, v___f_5405_);
lean_ctor_set(v___x_5396_, 1, v___f_5398_);
lean_ctor_set(v___x_5396_, 0, v___x_5402_);
v___x_5407_ = v___x_5396_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___x_5402_);
lean_ctor_set(v_reuseFailAlloc_5464_, 1, v___f_5398_);
lean_ctor_set(v_reuseFailAlloc_5464_, 2, v___f_5405_);
lean_ctor_set(v_reuseFailAlloc_5464_, 3, v___f_5404_);
lean_ctor_set(v_reuseFailAlloc_5464_, 4, v___f_5403_);
v___x_5407_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
lean_object* v___x_5409_; 
if (v_isShared_5390_ == 0)
{
lean_ctor_set(v___x_5389_, 1, v___f_5399_);
lean_ctor_set(v___x_5389_, 0, v___x_5407_);
v___x_5409_ = v___x_5389_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5463_, 1, v___f_5399_);
v___x_5409_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
lean_object* v___x_5410_; lean_object* v_toApplicative_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5461_; 
v___x_5410_ = l_StateRefT_x27_instMonad___redArg(v___x_5409_);
v_toApplicative_5411_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5461_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5461_ == 0)
{
lean_object* v_unused_5462_; 
v_unused_5462_ = lean_ctor_get(v___x_5410_, 1);
lean_dec(v_unused_5462_);
v___x_5413_ = v___x_5410_;
v_isShared_5414_ = v_isSharedCheck_5461_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_toApplicative_5411_);
lean_dec(v___x_5410_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5461_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v_toFunctor_5415_; lean_object* v_toSeq_5416_; lean_object* v_toSeqLeft_5417_; lean_object* v_toSeqRight_5418_; lean_object* v___x_5420_; uint8_t v_isShared_5421_; uint8_t v_isSharedCheck_5459_; 
v_toFunctor_5415_ = lean_ctor_get(v_toApplicative_5411_, 0);
v_toSeq_5416_ = lean_ctor_get(v_toApplicative_5411_, 2);
v_toSeqLeft_5417_ = lean_ctor_get(v_toApplicative_5411_, 3);
v_toSeqRight_5418_ = lean_ctor_get(v_toApplicative_5411_, 4);
v_isSharedCheck_5459_ = !lean_is_exclusive(v_toApplicative_5411_);
if (v_isSharedCheck_5459_ == 0)
{
lean_object* v_unused_5460_; 
v_unused_5460_ = lean_ctor_get(v_toApplicative_5411_, 1);
lean_dec(v_unused_5460_);
v___x_5420_ = v_toApplicative_5411_;
v_isShared_5421_ = v_isSharedCheck_5459_;
goto v_resetjp_5419_;
}
else
{
lean_inc(v_toSeqRight_5418_);
lean_inc(v_toSeqLeft_5417_);
lean_inc(v_toSeq_5416_);
lean_inc(v_toFunctor_5415_);
lean_dec(v_toApplicative_5411_);
v___x_5420_ = lean_box(0);
v_isShared_5421_ = v_isSharedCheck_5459_;
goto v_resetjp_5419_;
}
v_resetjp_5419_:
{
lean_object* v___f_5422_; lean_object* v___f_5423_; lean_object* v___f_5424_; lean_object* v___f_5425_; lean_object* v___x_5426_; lean_object* v___f_5427_; lean_object* v___f_5428_; lean_object* v___f_5429_; lean_object* v___x_5431_; 
v___f_5422_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6));
v___f_5423_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7));
lean_inc_ref(v_toFunctor_5415_);
v___f_5424_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5424_, 0, v_toFunctor_5415_);
v___f_5425_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5425_, 0, v_toFunctor_5415_);
v___x_5426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5426_, 0, v___f_5424_);
lean_ctor_set(v___x_5426_, 1, v___f_5425_);
v___f_5427_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5427_, 0, v_toSeqRight_5418_);
v___f_5428_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5428_, 0, v_toSeqLeft_5417_);
v___f_5429_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5429_, 0, v_toSeq_5416_);
if (v_isShared_5421_ == 0)
{
lean_ctor_set(v___x_5420_, 4, v___f_5427_);
lean_ctor_set(v___x_5420_, 3, v___f_5428_);
lean_ctor_set(v___x_5420_, 2, v___f_5429_);
lean_ctor_set(v___x_5420_, 1, v___f_5422_);
lean_ctor_set(v___x_5420_, 0, v___x_5426_);
v___x_5431_ = v___x_5420_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5426_);
lean_ctor_set(v_reuseFailAlloc_5458_, 1, v___f_5422_);
lean_ctor_set(v_reuseFailAlloc_5458_, 2, v___f_5429_);
lean_ctor_set(v_reuseFailAlloc_5458_, 3, v___f_5428_);
lean_ctor_set(v_reuseFailAlloc_5458_, 4, v___f_5427_);
v___x_5431_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
lean_object* v___x_5433_; 
if (v_isShared_5414_ == 0)
{
lean_ctor_set(v___x_5413_, 1, v___f_5423_);
lean_ctor_set(v___x_5413_, 0, v___x_5431_);
v___x_5433_ = v___x_5413_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v___x_5431_);
lean_ctor_set(v_reuseFailAlloc_5457_, 1, v___f_5423_);
v___x_5433_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; uint8_t v___x_5437_; 
v___x_5434_ = l_ReaderT_instMonad___redArg(v___x_5433_);
v___x_5435_ = lean_array_get_size(v_acc_5361_);
v___x_5436_ = lean_array_get_size(v_declInfos_5358_);
v___x_5437_ = lean_nat_dec_lt(v___x_5435_, v___x_5436_);
if (v___x_5437_ == 0)
{
lean_object* v___x_5438_; 
lean_dec_ref(v___x_5434_);
lean_dec_ref(v_declInfos_5358_);
lean_inc(v___y_5368_);
lean_inc_ref(v___y_5367_);
lean_inc(v___y_5366_);
lean_inc_ref(v___y_5365_);
lean_inc(v___y_5364_);
lean_inc_ref(v___y_5363_);
lean_inc_ref(v___y_5362_);
v___x_5438_ = lean_apply_9(v_k_5359_, v_acc_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, lean_box(0));
return v___x_5438_;
}
else
{
lean_object* v___f_5439_; lean_object* v___x_5440_; uint8_t v___x_5441_; lean_object* v___f_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v_snd_5447_; lean_object* v_fst_5448_; lean_object* v_fst_5449_; lean_object* v_snd_5450_; lean_object* v___x_5451_; 
v___f_5439_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed), 10, 1);
lean_closure_set(v___f_5439_, 0, v___x_5434_);
v___x_5440_ = lean_box(0);
v___x_5441_ = 0;
v___f_5442_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5442_, 0, v___f_5439_);
v___x_5443_ = lean_box(v___x_5441_);
v___x_5444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5443_);
lean_ctor_set(v___x_5444_, 1, v___f_5442_);
v___x_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5445_, 0, v___x_5440_);
lean_ctor_set(v___x_5445_, 1, v___x_5444_);
v___x_5446_ = lean_array_get(v___x_5445_, v_declInfos_5358_, v___x_5435_);
lean_dec_ref_known(v___x_5445_, 2);
v_snd_5447_ = lean_ctor_get(v___x_5446_, 1);
lean_inc(v_snd_5447_);
v_fst_5448_ = lean_ctor_get(v___x_5446_, 0);
lean_inc(v_fst_5448_);
lean_dec(v___x_5446_);
v_fst_5449_ = lean_ctor_get(v_snd_5447_, 0);
lean_inc(v_fst_5449_);
v_snd_5450_ = lean_ctor_get(v_snd_5447_, 1);
lean_inc(v_snd_5450_);
lean_dec(v_snd_5447_);
lean_inc(v___y_5368_);
lean_inc_ref(v___y_5367_);
lean_inc(v___y_5366_);
lean_inc_ref(v___y_5365_);
lean_inc(v___y_5364_);
lean_inc_ref(v___y_5363_);
lean_inc_ref(v___y_5362_);
lean_inc_ref(v_acc_5361_);
v___x_5451_ = lean_apply_9(v_snd_5450_, v_acc_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, lean_box(0));
if (lean_obj_tag(v___x_5451_) == 0)
{
lean_object* v_a_5452_; lean_object* v___x_5453_; lean_object* v___f_5454_; uint8_t v___x_5455_; lean_object* v___x_5456_; 
v_a_5452_ = lean_ctor_get(v___x_5451_, 0);
lean_inc(v_a_5452_);
lean_dec_ref_known(v___x_5451_, 1);
v___x_5453_ = lean_box(v_kind_5360_);
v___f_5454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed), 13, 4);
lean_closure_set(v___f_5454_, 0, v_acc_5361_);
lean_closure_set(v___f_5454_, 1, v_declInfos_5358_);
lean_closure_set(v___f_5454_, 2, v_k_5359_);
lean_closure_set(v___f_5454_, 3, v___x_5453_);
v___x_5455_ = lean_unbox(v_fst_5449_);
lean_dec(v_fst_5449_);
v___x_5456_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_5448_, v___x_5455_, v_a_5452_, v___f_5454_, v_kind_5360_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_);
return v___x_5456_;
}
else
{
lean_dec(v_fst_5449_);
lean_dec(v_fst_5448_);
lean_dec_ref(v_acc_5361_);
lean_dec_ref(v_k_5359_);
lean_dec_ref(v_declInfos_5358_);
return v___x_5451_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(lean_object* v_acc_5469_, lean_object* v_declInfos_5470_, lean_object* v_k_5471_, uint8_t v_kind_5472_, lean_object* v_x_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_){
_start:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5482_ = lean_array_push(v_acc_5469_, v_x_5473_);
v___x_5483_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_5470_, v_k_5471_, v_kind_5472_, v___x_5482_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
return v___x_5483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___boxed(lean_object* v_declInfos_5484_, lean_object* v_k_5485_, lean_object* v_kind_5486_, lean_object* v_acc_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_){
_start:
{
uint8_t v_kind_boxed_5496_; lean_object* v_res_5497_; 
v_kind_boxed_5496_ = lean_unbox(v_kind_5486_);
v_res_5497_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_5484_, v_k_5485_, v_kind_boxed_5496_, v_acc_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_);
lean_dec(v___y_5494_);
lean_dec_ref(v___y_5493_);
lean_dec(v___y_5492_);
lean_dec_ref(v___y_5491_);
lean_dec(v___y_5490_);
lean_dec_ref(v___y_5489_);
lean_dec_ref(v___y_5488_);
return v_res_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(lean_object* v_declInfos_5500_, lean_object* v_k_5501_, uint8_t v_kind_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_){
_start:
{
lean_object* v___x_5511_; lean_object* v___x_5512_; 
v___x_5511_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0));
v___x_5512_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_5500_, v_k_5501_, v_kind_5502_, v___x_5511_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_);
return v___x_5512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_declInfos_5513_, lean_object* v_k_5514_, lean_object* v_kind_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_){
_start:
{
uint8_t v_kind_boxed_5524_; lean_object* v_res_5525_; 
v_kind_boxed_5524_ = lean_unbox(v_kind_5515_);
v_res_5525_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_declInfos_5513_, v_k_5514_, v_kind_boxed_5524_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
lean_dec(v___y_5522_);
lean_dec_ref(v___y_5521_);
lean_dec(v___y_5520_);
lean_dec_ref(v___y_5519_);
lean_dec(v___y_5518_);
lean_dec_ref(v___y_5517_);
lean_dec_ref(v___y_5516_);
return v_res_5525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(size_t v_sz_5526_, size_t v_i_5527_, lean_object* v_bs_5528_){
_start:
{
uint8_t v___x_5529_; 
v___x_5529_ = lean_usize_dec_lt(v_i_5527_, v_sz_5526_);
if (v___x_5529_ == 0)
{
return v_bs_5528_;
}
else
{
lean_object* v_v_5530_; lean_object* v_fst_5531_; lean_object* v_snd_5532_; lean_object* v___x_5534_; uint8_t v_isShared_5535_; uint8_t v_isSharedCheck_5548_; 
v_v_5530_ = lean_array_uget(v_bs_5528_, v_i_5527_);
v_fst_5531_ = lean_ctor_get(v_v_5530_, 0);
v_snd_5532_ = lean_ctor_get(v_v_5530_, 1);
v_isSharedCheck_5548_ = !lean_is_exclusive(v_v_5530_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5534_ = v_v_5530_;
v_isShared_5535_ = v_isSharedCheck_5548_;
goto v_resetjp_5533_;
}
else
{
lean_inc(v_snd_5532_);
lean_inc(v_fst_5531_);
lean_dec(v_v_5530_);
v___x_5534_ = lean_box(0);
v_isShared_5535_ = v_isSharedCheck_5548_;
goto v_resetjp_5533_;
}
v_resetjp_5533_:
{
lean_object* v___x_5536_; lean_object* v_bs_x27_5537_; uint8_t v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5541_; 
v___x_5536_ = lean_unsigned_to_nat(0u);
v_bs_x27_5537_ = lean_array_uset(v_bs_5528_, v_i_5527_, v___x_5536_);
v___x_5538_ = 0;
v___x_5539_ = lean_box(v___x_5538_);
if (v_isShared_5535_ == 0)
{
lean_ctor_set(v___x_5534_, 0, v___x_5539_);
v___x_5541_ = v___x_5534_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_snd_5532_);
v___x_5541_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5542_; size_t v___x_5543_; size_t v___x_5544_; lean_object* v___x_5545_; 
v___x_5542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5542_, 0, v_fst_5531_);
lean_ctor_set(v___x_5542_, 1, v___x_5541_);
v___x_5543_ = ((size_t)1ULL);
v___x_5544_ = lean_usize_add(v_i_5527_, v___x_5543_);
v___x_5545_ = lean_array_uset(v_bs_x27_5537_, v_i_5527_, v___x_5542_);
v_i_5527_ = v___x_5544_;
v_bs_5528_ = v___x_5545_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5___boxed(lean_object* v_sz_5549_, lean_object* v_i_5550_, lean_object* v_bs_5551_){
_start:
{
size_t v_sz_boxed_5552_; size_t v_i_boxed_5553_; lean_object* v_res_5554_; 
v_sz_boxed_5552_ = lean_unbox_usize(v_sz_5549_);
lean_dec(v_sz_5549_);
v_i_boxed_5553_ = lean_unbox_usize(v_i_5550_);
lean_dec(v_i_5550_);
v_res_5554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_boxed_5552_, v_i_boxed_5553_, v_bs_5551_);
return v_res_5554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_5555_, lean_object* v_k_5556_, uint8_t v_kind_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_){
_start:
{
size_t v_sz_5566_; size_t v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; 
v_sz_5566_ = lean_array_size(v_declInfos_5555_);
v___x_5567_ = ((size_t)0ULL);
v___x_5568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_5566_, v___x_5567_, v_declInfos_5555_);
v___x_5569_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v___x_5568_, v_k_5556_, v_kind_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_5570_, lean_object* v_k_5571_, lean_object* v_kind_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_){
_start:
{
uint8_t v_kind_boxed_5581_; lean_object* v_res_5582_; 
v_kind_boxed_5581_ = lean_unbox(v_kind_5572_);
v_res_5582_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_5570_, v_k_5571_, v_kind_boxed_5581_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
lean_dec_ref(v___y_5573_);
return v_res_5582_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__3(void){
_start:
{
lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5588_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__2));
v___x_5589_ = l_Lean_stringToMessageData(v___x_5588_);
return v___x_5589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_5620_, lean_object* v_dec_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_){
_start:
{
lean_object* v___x_5630_; uint8_t v___x_5631_; 
v___x_5630_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_5620_);
v___x_5631_ = l_Lean_Syntax_isOfKind(v_stx_5620_, v___x_5630_);
if (v___x_5631_ == 0)
{
lean_object* v___x_5632_; 
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_5632_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_5632_;
}
else
{
lean_object* v___x_5633_; lean_object* v___x_5634_; uint8_t v___x_5635_; 
v___x_5633_ = lean_unsigned_to_nat(1u);
v___x_5634_ = l_Lean_Syntax_getArg(v_stx_5620_, v___x_5633_);
lean_inc(v___x_5634_);
v___x_5635_ = l_Lean_Syntax_matchesNull(v___x_5634_, v___x_5633_);
if (v___x_5635_ == 0)
{
lean_object* v___x_5636_; 
lean_dec(v___x_5634_);
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_5636_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_5636_;
}
else
{
lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; uint8_t v___x_5640_; lean_object* v___y_5642_; lean_object* v___y_5643_; uint8_t v___y_5644_; lean_object* v___y_5645_; lean_object* v___y_5646_; lean_object* v___y_5647_; lean_object* v___y_5648_; lean_object* v___y_5649_; lean_object* v___y_5650_; lean_object* v___y_5651_; lean_object* v___y_5652_; lean_object* v_forIn_5653_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5657_; lean_object* v___y_5658_; lean_object* v___y_5659_; lean_object* v___y_5660_; lean_object* v___y_5670_; lean_object* v___y_5671_; uint8_t v___y_5672_; lean_object* v___y_5673_; lean_object* v___y_5674_; lean_object* v___y_5675_; lean_object* v___y_5676_; lean_object* v___y_5677_; lean_object* v___y_5678_; lean_object* v___y_5679_; lean_object* v___y_5680_; lean_object* v___y_5681_; uint8_t v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; lean_object* v___y_5685_; lean_object* v___y_5686_; lean_object* v___y_5687_; lean_object* v___y_5688_; lean_object* v___y_5689_; lean_object* v___y_5690_; lean_object* v___y_5691_; lean_object* v___y_5692_; lean_object* v___y_5693_; lean_object* v___y_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5697_; lean_object* v___y_5698_; lean_object* v___y_5740_; uint8_t v___y_5741_; lean_object* v___y_5742_; lean_object* v___y_5743_; lean_object* v___y_5744_; lean_object* v___y_5745_; lean_object* v___y_5746_; lean_object* v___y_5747_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v___y_5750_; lean_object* v___y_5751_; lean_object* v___y_5752_; lean_object* v___y_5753_; lean_object* v___y_5754_; lean_object* v___y_5755_; lean_object* v___y_5756_; lean_object* v___y_5757_; uint8_t v___y_5758_; lean_object* v___y_5759_; lean_object* v___y_5760_; lean_object* v___y_5761_; lean_object* v___y_5762_; uint8_t v___y_5763_; lean_object* v___y_5764_; lean_object* v___y_5765_; lean_object* v___y_5766_; lean_object* v___y_5767_; lean_object* v___y_5768_; lean_object* v___y_5769_; lean_object* v___y_5770_; lean_object* v___y_5771_; lean_object* v___y_5772_; lean_object* v___y_5773_; lean_object* v___y_5774_; lean_object* v___y_5775_; lean_object* v___y_5784_; uint8_t v___y_5785_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v___y_5790_; lean_object* v___y_5791_; lean_object* v___y_5792_; lean_object* v___y_5793_; lean_object* v___y_5794_; lean_object* v___y_5795_; lean_object* v___y_5796_; lean_object* v___y_5797_; lean_object* v___y_5798_; lean_object* v___y_5799_; lean_object* v___y_5800_; lean_object* v___y_5801_; lean_object* v___y_5802_; lean_object* v___y_5803_; lean_object* v___y_5804_; lean_object* v___y_5805_; uint8_t v___y_5806_; lean_object* v___y_5807_; lean_object* v___y_5808_; lean_object* v___y_5809_; lean_object* v___y_5810_; lean_object* v___y_5811_; lean_object* v___y_5812_; lean_object* v___y_5813_; uint8_t v___y_5814_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v_fst_5818_; lean_object* v_snd_5819_; lean_object* v___y_5820_; lean_object* v___y_5821_; lean_object* v___y_5822_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5853_; uint8_t v___y_5854_; lean_object* v___y_5855_; lean_object* v___y_5856_; lean_object* v___y_5857_; lean_object* v___y_5858_; lean_object* v___y_5859_; lean_object* v___y_5860_; lean_object* v___y_5861_; lean_object* v___y_5862_; lean_object* v___y_5863_; lean_object* v___y_5864_; lean_object* v___y_5865_; lean_object* v___y_5866_; lean_object* v___y_5867_; lean_object* v___y_5868_; uint8_t v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; lean_object* v___y_5872_; lean_object* v___y_5873_; lean_object* v___y_5874_; lean_object* v___y_5875_; lean_object* v___y_5876_; lean_object* v___y_5877_; lean_object* v___y_5878_; lean_object* v___y_5879_; lean_object* v___y_5880_; lean_object* v___y_5881_; lean_object* v___y_5882_; lean_object* v___y_5883_; lean_object* v___y_5884_; lean_object* v___y_5885_; uint8_t v___y_5886_; lean_object* v___y_5887_; lean_object* v___y_5888_; lean_object* v___y_5889_; lean_object* v___y_5890_; lean_object* v___y_5891_; lean_object* v___y_5975_; lean_object* v___y_5976_; lean_object* v___y_5977_; lean_object* v___y_5978_; lean_object* v___y_5979_; lean_object* v___y_5980_; lean_object* v___y_5981_; lean_object* v___y_5982_; lean_object* v___y_5983_; lean_object* v___y_5984_; uint8_t v___y_5985_; lean_object* v___y_5986_; lean_object* v___y_5987_; lean_object* v___y_5988_; lean_object* v___y_5989_; lean_object* v___y_5990_; lean_object* v___y_5991_; uint8_t v___y_5992_; lean_object* v___y_5993_; lean_object* v___y_5994_; lean_object* v___y_5995_; lean_object* v___y_5996_; lean_object* v___y_5997_; lean_object* v___y_5998_; lean_object* v___y_5999_; lean_object* v___y_6000_; lean_object* v___y_6001_; lean_object* v___y_6002_; lean_object* v___y_6003_; lean_object* v___y_6004_; lean_object* v___y_6005_; uint8_t v___y_6006_; lean_object* v___y_6007_; lean_object* v___y_6008_; lean_object* v___y_6009_; lean_object* v___y_6010_; lean_object* v___y_6011_; lean_object* v___y_6012_; 
v___x_5637_ = lean_unsigned_to_nat(0u);
v___x_5638_ = l_Lean_Syntax_getArg(v___x_5634_, v___x_5637_);
lean_dec(v___x_5634_);
v___x_5639_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_5638_);
v___x_5640_ = l_Lean_Syntax_isOfKind(v___x_5638_, v___x_5639_);
if (v___x_5640_ == 0)
{
lean_object* v___x_6026_; 
lean_dec(v___x_5638_);
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_6026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6026_;
}
else
{
lean_object* v_tk_6027_; lean_object* v___y_6029_; uint8_t v___y_6030_; lean_object* v___y_6031_; lean_object* v___y_6032_; lean_object* v___y_6033_; lean_object* v___y_6034_; uint8_t v___y_6035_; lean_object* v___y_6036_; lean_object* v___y_6037_; lean_object* v_dec_x3f_6038_; lean_object* v___y_6039_; lean_object* v___y_6040_; lean_object* v___y_6041_; lean_object* v___y_6042_; lean_object* v___y_6043_; lean_object* v___y_6044_; lean_object* v___y_6045_; lean_object* v___y_6166_; uint8_t v___y_6167_; lean_object* v___y_6168_; lean_object* v___y_6169_; lean_object* v___y_6170_; lean_object* v___y_6171_; uint8_t v___y_6172_; lean_object* v___y_6173_; lean_object* v___y_6174_; lean_object* v_inv_x3f_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; lean_object* v___y_6180_; lean_object* v___y_6181_; lean_object* v___y_6182_; lean_object* v_h_x3f_6194_; lean_object* v___y_6195_; lean_object* v___y_6196_; lean_object* v___y_6197_; lean_object* v___y_6198_; lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; lean_object* v___x_6219_; uint8_t v___x_6220_; 
v_tk_6027_ = l_Lean_Syntax_getArg(v_stx_5620_, v___x_5637_);
v___x_6219_ = l_Lean_Syntax_getArg(v___x_5638_, v___x_5637_);
v___x_6220_ = l_Lean_Syntax_isNone(v___x_6219_);
if (v___x_6220_ == 0)
{
lean_object* v___x_6221_; uint8_t v___x_6222_; 
v___x_6221_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_6219_);
v___x_6222_ = l_Lean_Syntax_matchesNull(v___x_6219_, v___x_6221_);
if (v___x_6222_ == 0)
{
lean_object* v___x_6223_; 
lean_dec(v___x_6219_);
lean_dec(v_tk_6027_);
lean_dec(v___x_5638_);
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_6223_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6223_;
}
else
{
lean_object* v_h_x3f_6224_; lean_object* v___x_6225_; 
v_h_x3f_6224_ = l_Lean_Syntax_getArg(v___x_6219_, v___x_5637_);
lean_dec(v___x_6219_);
v___x_6225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6225_, 0, v_h_x3f_6224_);
v_h_x3f_6194_ = v___x_6225_;
v___y_6195_ = v_a_5622_;
v___y_6196_ = v_a_5623_;
v___y_6197_ = v_a_5624_;
v___y_6198_ = v_a_5625_;
v___y_6199_ = v_a_5626_;
v___y_6200_ = v_a_5627_;
v___y_6201_ = v_a_5628_;
goto v___jp_6193_;
}
}
else
{
lean_object* v___x_6226_; 
lean_dec(v___x_6219_);
v___x_6226_ = lean_box(0);
v_h_x3f_6194_ = v___x_6226_;
v___y_6195_ = v_a_5622_;
v___y_6196_ = v_a_5623_;
v___y_6197_ = v_a_5624_;
v___y_6198_ = v_a_5625_;
v___y_6199_ = v_a_5626_;
v___y_6200_ = v_a_5627_;
v___y_6201_ = v_a_5628_;
goto v___jp_6193_;
}
v___jp_6028_:
{
lean_object* v___x_6046_; 
v___x_6046_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_5621_, v_tk_6027_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
lean_dec(v_tk_6027_);
if (lean_obj_tag(v___x_6046_) == 0)
{
lean_object* v_a_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; 
v_a_6047_ = lean_ctor_get(v___x_6046_, 0);
lean_inc(v_a_6047_);
lean_dec_ref_known(v___x_6046_, 1);
v___x_6048_ = lean_mk_empty_array_with_capacity(v___x_5633_);
lean_inc(v___y_6036_);
v___x_6049_ = lean_array_push(v___x_6048_, v___y_6036_);
v___x_6050_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_6049_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
lean_dec_ref(v___x_6049_);
if (lean_obj_tag(v___x_6050_) == 0)
{
lean_object* v___x_6051_; 
lean_dec_ref_known(v___x_6050_, 1);
v___x_6051_ = l_Lean_Meta_mkFreshLevelMVar(v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
if (lean_obj_tag(v___x_6051_) == 0)
{
lean_object* v_a_6052_; lean_object* v___x_6053_; 
v_a_6052_ = lean_ctor_get(v___x_6051_, 0);
lean_inc(v_a_6052_);
lean_dec_ref_known(v___x_6051_, 1);
v___x_6053_ = l_Lean_Meta_mkFreshLevelMVar(v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
if (lean_obj_tag(v___x_6053_) == 0)
{
lean_object* v_a_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; uint8_t v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; 
v_a_6054_ = lean_ctor_get(v___x_6053_, 0);
lean_inc(v_a_6054_);
lean_dec_ref_known(v___x_6053_, 1);
lean_inc(v_a_6052_);
v___x_6055_ = l_Lean_Level_succ___override(v_a_6052_);
v___x_6056_ = l_Lean_mkSort(v___x_6055_);
v___x_6057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6056_);
v___x_6058_ = 0;
v___x_6059_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__16));
v___x_6060_ = l_Lean_Meta_mkFreshExprMVar(v___x_6057_, v___x_6058_, v___x_6059_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
if (lean_obj_tag(v___x_6060_) == 0)
{
lean_object* v_a_6061_; lean_object* v___x_6063_; uint8_t v_isShared_6064_; uint8_t v_isSharedCheck_6132_; 
v_a_6061_ = lean_ctor_get(v___x_6060_, 0);
v_isSharedCheck_6132_ = !lean_is_exclusive(v___x_6060_);
if (v_isSharedCheck_6132_ == 0)
{
v___x_6063_ = v___x_6060_;
v_isShared_6064_ = v_isSharedCheck_6132_;
goto v_resetjp_6062_;
}
else
{
lean_inc(v_a_6061_);
lean_dec(v___x_6060_);
v___x_6063_ = lean_box(0);
v_isShared_6064_ = v_isSharedCheck_6132_;
goto v_resetjp_6062_;
}
v_resetjp_6062_:
{
lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6068_; 
lean_inc(v_a_6054_);
v___x_6065_ = l_Lean_Level_succ___override(v_a_6054_);
v___x_6066_ = l_Lean_mkSort(v___x_6065_);
if (v_isShared_6064_ == 0)
{
lean_ctor_set_tag(v___x_6063_, 1);
lean_ctor_set(v___x_6063_, 0, v___x_6066_);
v___x_6068_ = v___x_6063_;
goto v_reusejp_6067_;
}
else
{
lean_object* v_reuseFailAlloc_6131_; 
v_reuseFailAlloc_6131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6131_, 0, v___x_6066_);
v___x_6068_ = v_reuseFailAlloc_6131_;
goto v_reusejp_6067_;
}
v_reusejp_6067_:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; 
v___x_6069_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__18));
v___x_6070_ = l_Lean_Meta_mkFreshExprMVar(v___x_6068_, v___x_6058_, v___x_6069_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
if (lean_obj_tag(v___x_6070_) == 0)
{
lean_object* v_a_6071_; lean_object* v___x_6073_; uint8_t v_isShared_6074_; uint8_t v_isSharedCheck_6130_; 
v_a_6071_ = lean_ctor_get(v___x_6070_, 0);
v_isSharedCheck_6130_ = !lean_is_exclusive(v___x_6070_);
if (v_isSharedCheck_6130_ == 0)
{
v___x_6073_ = v___x_6070_;
v_isShared_6074_ = v_isSharedCheck_6130_;
goto v_resetjp_6072_;
}
else
{
lean_inc(v_a_6071_);
lean_dec(v___x_6070_);
v___x_6073_ = lean_box(0);
v_isShared_6074_ = v_isSharedCheck_6130_;
goto v_resetjp_6072_;
}
v_resetjp_6072_:
{
lean_object* v___x_6076_; 
lean_inc(v_a_6071_);
if (v_isShared_6074_ == 0)
{
lean_ctor_set_tag(v___x_6073_, 1);
v___x_6076_ = v___x_6073_;
goto v_reusejp_6075_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v_a_6071_);
v___x_6076_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6075_;
}
v_reusejp_6075_:
{
lean_object* v___x_6077_; lean_object* v___x_6078_; 
v___x_6077_ = lean_box(0);
v___x_6078_ = l_Lean_Elab_Term_elabTermEnsuringType(v___y_6037_, v___x_6076_, v___x_5640_, v___x_5640_, v___x_6077_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
if (lean_obj_tag(v___x_6078_) == 0)
{
lean_object* v_a_6079_; lean_object* v___x_6080_; lean_object* v_body_6081_; lean_object* v___x_6082_; 
v_a_6079_ = lean_ctor_get(v___x_6078_, 0);
lean_inc(v_a_6079_);
lean_dec_ref_known(v___x_6078_, 1);
v___x_6080_ = lean_unsigned_to_nat(5u);
v_body_6081_ = l_Lean_Syntax_getArg(v_stx_5620_, v___x_6080_);
lean_dec(v_stx_5620_);
lean_inc(v_body_6081_);
v___x_6082_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_6081_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_);
if (lean_obj_tag(v___x_6082_) == 0)
{
lean_object* v_a_6083_; lean_object* v___x_6084_; 
v_a_6083_ = lean_ctor_get(v___x_6082_, 0);
lean_inc(v_a_6083_);
lean_dec_ref_known(v___x_6082_, 1);
v___x_6084_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_6039_);
if (lean_obj_tag(v___x_6084_) == 0)
{
lean_object* v_a_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; 
v_a_6085_ = lean_ctor_get(v___x_6084_, 0);
lean_inc(v_a_6085_);
lean_dec_ref_known(v___x_6084_, 1);
v___x_6086_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__20));
v___x_6087_ = l_Lean_Core_mkFreshUserName(v___x_6086_, v___y_6044_, v___y_6045_);
if (lean_obj_tag(v___x_6087_) == 0)
{
lean_object* v_a_6088_; lean_object* v_monadInfo_6089_; lean_object* v_mutVars_6090_; lean_object* v___f_6091_; lean_object* v___f_6092_; lean_object* v___x_6093_; lean_object* v___f_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; uint8_t v___x_6097_; 
v_a_6088_ = lean_ctor_get(v___x_6087_, 0);
lean_inc(v_a_6088_);
lean_dec_ref_known(v___x_6087_, 1);
v_monadInfo_6089_ = lean_ctor_get(v___y_6039_, 0);
v_mutVars_6090_ = lean_ctor_get(v___y_6039_, 1);
lean_inc(v_a_6061_);
v___f_6091_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_6091_, 0, v_a_6061_);
lean_inc_ref(v___f_6091_);
lean_inc(v___y_6031_);
v___f_6092_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 5, 3);
lean_closure_set(v___f_6092_, 0, v___y_6031_);
lean_closure_set(v___f_6092_, 1, v___f_6091_);
lean_closure_set(v___f_6092_, 2, v___x_5633_);
v___x_6093_ = lean_box(v___x_5640_);
lean_inc(v_a_6085_);
v___f_6094_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 12, 3);
lean_closure_set(v___f_6094_, 0, v_a_6085_);
lean_closure_set(v___f_6094_, 1, v___x_5633_);
lean_closure_set(v___f_6094_, 2, v___x_6093_);
v___x_6095_ = lean_array_get_size(v_mutVars_6090_);
v___x_6096_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__21));
v___x_6097_ = lean_nat_dec_lt(v___x_5637_, v___x_6095_);
if (v___x_6097_ == 0)
{
lean_inc(v_a_6061_);
lean_inc(v_a_6088_);
lean_inc(v_a_6071_);
lean_inc(v_a_6054_);
lean_inc(v_a_6052_);
lean_inc(v_a_6079_);
v___y_5975_ = v_a_6079_;
v___y_5976_ = v_a_6052_;
v___y_5977_ = v___y_6031_;
v___y_5978_ = v_a_6085_;
v___y_5979_ = v_a_6047_;
v___y_5980_ = v___f_6091_;
v___y_5981_ = v_body_6081_;
v___y_5982_ = v_monadInfo_6089_;
v___y_5983_ = v___y_6029_;
v___y_5984_ = v___f_6092_;
v___y_5985_ = v___y_6030_;
v___y_5986_ = v_a_6054_;
v___y_5987_ = v___f_6094_;
v___y_5988_ = v_a_6071_;
v___y_5989_ = v_a_6088_;
v___y_5990_ = v_a_6061_;
v___y_5991_ = v___y_6039_;
v___y_5992_ = v___x_6058_;
v___y_5993_ = v___y_6044_;
v___y_5994_ = v___y_6043_;
v___y_5995_ = v___y_6041_;
v___y_5996_ = v___y_6042_;
v___y_5997_ = v_a_6054_;
v___y_5998_ = v_a_6083_;
v___y_5999_ = v_a_6079_;
v___y_6000_ = v_a_6052_;
v___y_6001_ = v___y_6036_;
v___y_6002_ = v___y_6032_;
v___y_6003_ = v___y_6033_;
v___y_6004_ = v___y_6045_;
v___y_6005_ = v___y_6034_;
v___y_6006_ = v___y_6035_;
v___y_6007_ = v_dec_x3f_6038_;
v___y_6008_ = v___y_6040_;
v___y_6009_ = v_a_6071_;
v___y_6010_ = v_a_6061_;
v___y_6011_ = v_a_6088_;
v___y_6012_ = v___x_6096_;
goto v___jp_5974_;
}
else
{
uint8_t v___x_6098_; 
v___x_6098_ = lean_nat_dec_le(v___x_6095_, v___x_6095_);
if (v___x_6098_ == 0)
{
if (v___x_6097_ == 0)
{
lean_inc(v_a_6061_);
lean_inc(v_a_6088_);
lean_inc(v_a_6071_);
lean_inc(v_a_6054_);
lean_inc(v_a_6052_);
lean_inc(v_a_6079_);
v___y_5975_ = v_a_6079_;
v___y_5976_ = v_a_6052_;
v___y_5977_ = v___y_6031_;
v___y_5978_ = v_a_6085_;
v___y_5979_ = v_a_6047_;
v___y_5980_ = v___f_6091_;
v___y_5981_ = v_body_6081_;
v___y_5982_ = v_monadInfo_6089_;
v___y_5983_ = v___y_6029_;
v___y_5984_ = v___f_6092_;
v___y_5985_ = v___y_6030_;
v___y_5986_ = v_a_6054_;
v___y_5987_ = v___f_6094_;
v___y_5988_ = v_a_6071_;
v___y_5989_ = v_a_6088_;
v___y_5990_ = v_a_6061_;
v___y_5991_ = v___y_6039_;
v___y_5992_ = v___x_6058_;
v___y_5993_ = v___y_6044_;
v___y_5994_ = v___y_6043_;
v___y_5995_ = v___y_6041_;
v___y_5996_ = v___y_6042_;
v___y_5997_ = v_a_6054_;
v___y_5998_ = v_a_6083_;
v___y_5999_ = v_a_6079_;
v___y_6000_ = v_a_6052_;
v___y_6001_ = v___y_6036_;
v___y_6002_ = v___y_6032_;
v___y_6003_ = v___y_6033_;
v___y_6004_ = v___y_6045_;
v___y_6005_ = v___y_6034_;
v___y_6006_ = v___y_6035_;
v___y_6007_ = v_dec_x3f_6038_;
v___y_6008_ = v___y_6040_;
v___y_6009_ = v_a_6071_;
v___y_6010_ = v_a_6061_;
v___y_6011_ = v_a_6088_;
v___y_6012_ = v___x_6096_;
goto v___jp_5974_;
}
else
{
size_t v___x_6099_; size_t v___x_6100_; lean_object* v___x_6101_; 
v___x_6099_ = ((size_t)0ULL);
v___x_6100_ = lean_usize_of_nat(v___x_6095_);
v___x_6101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_6083_, v_mutVars_6090_, v___x_6099_, v___x_6100_, v___x_6096_);
lean_inc(v_a_6061_);
lean_inc(v_a_6088_);
lean_inc(v_a_6071_);
lean_inc(v_a_6054_);
lean_inc(v_a_6052_);
lean_inc(v_a_6079_);
v___y_5975_ = v_a_6079_;
v___y_5976_ = v_a_6052_;
v___y_5977_ = v___y_6031_;
v___y_5978_ = v_a_6085_;
v___y_5979_ = v_a_6047_;
v___y_5980_ = v___f_6091_;
v___y_5981_ = v_body_6081_;
v___y_5982_ = v_monadInfo_6089_;
v___y_5983_ = v___y_6029_;
v___y_5984_ = v___f_6092_;
v___y_5985_ = v___y_6030_;
v___y_5986_ = v_a_6054_;
v___y_5987_ = v___f_6094_;
v___y_5988_ = v_a_6071_;
v___y_5989_ = v_a_6088_;
v___y_5990_ = v_a_6061_;
v___y_5991_ = v___y_6039_;
v___y_5992_ = v___x_6058_;
v___y_5993_ = v___y_6044_;
v___y_5994_ = v___y_6043_;
v___y_5995_ = v___y_6041_;
v___y_5996_ = v___y_6042_;
v___y_5997_ = v_a_6054_;
v___y_5998_ = v_a_6083_;
v___y_5999_ = v_a_6079_;
v___y_6000_ = v_a_6052_;
v___y_6001_ = v___y_6036_;
v___y_6002_ = v___y_6032_;
v___y_6003_ = v___y_6033_;
v___y_6004_ = v___y_6045_;
v___y_6005_ = v___y_6034_;
v___y_6006_ = v___y_6035_;
v___y_6007_ = v_dec_x3f_6038_;
v___y_6008_ = v___y_6040_;
v___y_6009_ = v_a_6071_;
v___y_6010_ = v_a_6061_;
v___y_6011_ = v_a_6088_;
v___y_6012_ = v___x_6101_;
goto v___jp_5974_;
}
}
else
{
size_t v___x_6102_; size_t v___x_6103_; lean_object* v___x_6104_; 
v___x_6102_ = ((size_t)0ULL);
v___x_6103_ = lean_usize_of_nat(v___x_6095_);
v___x_6104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_6083_, v_mutVars_6090_, v___x_6102_, v___x_6103_, v___x_6096_);
lean_inc(v_a_6061_);
lean_inc(v_a_6088_);
lean_inc(v_a_6071_);
lean_inc(v_a_6054_);
lean_inc(v_a_6052_);
lean_inc(v_a_6079_);
v___y_5975_ = v_a_6079_;
v___y_5976_ = v_a_6052_;
v___y_5977_ = v___y_6031_;
v___y_5978_ = v_a_6085_;
v___y_5979_ = v_a_6047_;
v___y_5980_ = v___f_6091_;
v___y_5981_ = v_body_6081_;
v___y_5982_ = v_monadInfo_6089_;
v___y_5983_ = v___y_6029_;
v___y_5984_ = v___f_6092_;
v___y_5985_ = v___y_6030_;
v___y_5986_ = v_a_6054_;
v___y_5987_ = v___f_6094_;
v___y_5988_ = v_a_6071_;
v___y_5989_ = v_a_6088_;
v___y_5990_ = v_a_6061_;
v___y_5991_ = v___y_6039_;
v___y_5992_ = v___x_6058_;
v___y_5993_ = v___y_6044_;
v___y_5994_ = v___y_6043_;
v___y_5995_ = v___y_6041_;
v___y_5996_ = v___y_6042_;
v___y_5997_ = v_a_6054_;
v___y_5998_ = v_a_6083_;
v___y_5999_ = v_a_6079_;
v___y_6000_ = v_a_6052_;
v___y_6001_ = v___y_6036_;
v___y_6002_ = v___y_6032_;
v___y_6003_ = v___y_6033_;
v___y_6004_ = v___y_6045_;
v___y_6005_ = v___y_6034_;
v___y_6006_ = v___y_6035_;
v___y_6007_ = v_dec_x3f_6038_;
v___y_6008_ = v___y_6040_;
v___y_6009_ = v_a_6071_;
v___y_6010_ = v_a_6061_;
v___y_6011_ = v_a_6088_;
v___y_6012_ = v___x_6104_;
goto v___jp_5974_;
}
}
}
else
{
lean_object* v_a_6105_; lean_object* v___x_6107_; uint8_t v_isShared_6108_; uint8_t v_isSharedCheck_6112_; 
lean_dec(v_a_6085_);
lean_dec(v_a_6083_);
lean_dec(v_body_6081_);
lean_dec(v_a_6079_);
lean_dec(v_a_6071_);
lean_dec(v_a_6061_);
lean_dec(v_a_6054_);
lean_dec(v_a_6052_);
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
v_a_6105_ = lean_ctor_get(v___x_6087_, 0);
v_isSharedCheck_6112_ = !lean_is_exclusive(v___x_6087_);
if (v_isSharedCheck_6112_ == 0)
{
v___x_6107_ = v___x_6087_;
v_isShared_6108_ = v_isSharedCheck_6112_;
goto v_resetjp_6106_;
}
else
{
lean_inc(v_a_6105_);
lean_dec(v___x_6087_);
v___x_6107_ = lean_box(0);
v_isShared_6108_ = v_isSharedCheck_6112_;
goto v_resetjp_6106_;
}
v_resetjp_6106_:
{
lean_object* v___x_6110_; 
if (v_isShared_6108_ == 0)
{
v___x_6110_ = v___x_6107_;
goto v_reusejp_6109_;
}
else
{
lean_object* v_reuseFailAlloc_6111_; 
v_reuseFailAlloc_6111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6111_, 0, v_a_6105_);
v___x_6110_ = v_reuseFailAlloc_6111_;
goto v_reusejp_6109_;
}
v_reusejp_6109_:
{
return v___x_6110_;
}
}
}
}
else
{
lean_object* v_a_6113_; lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6120_; 
lean_dec(v_a_6083_);
lean_dec(v_body_6081_);
lean_dec(v_a_6079_);
lean_dec(v_a_6071_);
lean_dec(v_a_6061_);
lean_dec(v_a_6054_);
lean_dec(v_a_6052_);
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
v_a_6113_ = lean_ctor_get(v___x_6084_, 0);
v_isSharedCheck_6120_ = !lean_is_exclusive(v___x_6084_);
if (v_isSharedCheck_6120_ == 0)
{
v___x_6115_ = v___x_6084_;
v_isShared_6116_ = v_isSharedCheck_6120_;
goto v_resetjp_6114_;
}
else
{
lean_inc(v_a_6113_);
lean_dec(v___x_6084_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6120_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
lean_object* v___x_6118_; 
if (v_isShared_6116_ == 0)
{
v___x_6118_ = v___x_6115_;
goto v_reusejp_6117_;
}
else
{
lean_object* v_reuseFailAlloc_6119_; 
v_reuseFailAlloc_6119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_a_6113_);
v___x_6118_ = v_reuseFailAlloc_6119_;
goto v_reusejp_6117_;
}
v_reusejp_6117_:
{
return v___x_6118_;
}
}
}
}
else
{
lean_object* v_a_6121_; lean_object* v___x_6123_; uint8_t v_isShared_6124_; uint8_t v_isSharedCheck_6128_; 
lean_dec(v_body_6081_);
lean_dec(v_a_6079_);
lean_dec(v_a_6071_);
lean_dec(v_a_6061_);
lean_dec(v_a_6054_);
lean_dec(v_a_6052_);
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
v_a_6121_ = lean_ctor_get(v___x_6082_, 0);
v_isSharedCheck_6128_ = !lean_is_exclusive(v___x_6082_);
if (v_isSharedCheck_6128_ == 0)
{
v___x_6123_ = v___x_6082_;
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
else
{
lean_inc(v_a_6121_);
lean_dec(v___x_6082_);
v___x_6123_ = lean_box(0);
v_isShared_6124_ = v_isSharedCheck_6128_;
goto v_resetjp_6122_;
}
v_resetjp_6122_:
{
lean_object* v___x_6126_; 
if (v_isShared_6124_ == 0)
{
v___x_6126_ = v___x_6123_;
goto v_reusejp_6125_;
}
else
{
lean_object* v_reuseFailAlloc_6127_; 
v_reuseFailAlloc_6127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6121_);
v___x_6126_ = v_reuseFailAlloc_6127_;
goto v_reusejp_6125_;
}
v_reusejp_6125_:
{
return v___x_6126_;
}
}
}
}
else
{
lean_dec(v_a_6071_);
lean_dec(v_a_6061_);
lean_dec(v_a_6054_);
lean_dec(v_a_6052_);
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
lean_dec(v_stx_5620_);
return v___x_6078_;
}
}
}
}
else
{
lean_dec(v_a_6061_);
lean_dec(v_a_6054_);
lean_dec(v_a_6052_);
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6037_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
lean_dec(v_stx_5620_);
return v___x_6070_;
}
}
}
}
else
{
lean_dec(v_a_6054_);
lean_dec(v_a_6052_);
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6037_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
lean_dec(v_stx_5620_);
return v___x_6060_;
}
}
else
{
lean_object* v_a_6133_; lean_object* v___x_6135_; uint8_t v_isShared_6136_; uint8_t v_isSharedCheck_6140_; 
lean_dec(v_a_6052_);
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6037_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
lean_dec(v_stx_5620_);
v_a_6133_ = lean_ctor_get(v___x_6053_, 0);
v_isSharedCheck_6140_ = !lean_is_exclusive(v___x_6053_);
if (v_isSharedCheck_6140_ == 0)
{
v___x_6135_ = v___x_6053_;
v_isShared_6136_ = v_isSharedCheck_6140_;
goto v_resetjp_6134_;
}
else
{
lean_inc(v_a_6133_);
lean_dec(v___x_6053_);
v___x_6135_ = lean_box(0);
v_isShared_6136_ = v_isSharedCheck_6140_;
goto v_resetjp_6134_;
}
v_resetjp_6134_:
{
lean_object* v___x_6138_; 
if (v_isShared_6136_ == 0)
{
v___x_6138_ = v___x_6135_;
goto v_reusejp_6137_;
}
else
{
lean_object* v_reuseFailAlloc_6139_; 
v_reuseFailAlloc_6139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6139_, 0, v_a_6133_);
v___x_6138_ = v_reuseFailAlloc_6139_;
goto v_reusejp_6137_;
}
v_reusejp_6137_:
{
return v___x_6138_;
}
}
}
}
else
{
lean_object* v_a_6141_; lean_object* v___x_6143_; uint8_t v_isShared_6144_; uint8_t v_isSharedCheck_6148_; 
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6037_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
lean_dec(v_stx_5620_);
v_a_6141_ = lean_ctor_get(v___x_6051_, 0);
v_isSharedCheck_6148_ = !lean_is_exclusive(v___x_6051_);
if (v_isSharedCheck_6148_ == 0)
{
v___x_6143_ = v___x_6051_;
v_isShared_6144_ = v_isSharedCheck_6148_;
goto v_resetjp_6142_;
}
else
{
lean_inc(v_a_6141_);
lean_dec(v___x_6051_);
v___x_6143_ = lean_box(0);
v_isShared_6144_ = v_isSharedCheck_6148_;
goto v_resetjp_6142_;
}
v_resetjp_6142_:
{
lean_object* v___x_6146_; 
if (v_isShared_6144_ == 0)
{
v___x_6146_ = v___x_6143_;
goto v_reusejp_6145_;
}
else
{
lean_object* v_reuseFailAlloc_6147_; 
v_reuseFailAlloc_6147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6147_, 0, v_a_6141_);
v___x_6146_ = v_reuseFailAlloc_6147_;
goto v_reusejp_6145_;
}
v_reusejp_6145_:
{
return v___x_6146_;
}
}
}
}
else
{
lean_object* v_a_6149_; lean_object* v___x_6151_; uint8_t v_isShared_6152_; uint8_t v_isSharedCheck_6156_; 
lean_dec(v_a_6047_);
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6037_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
lean_dec(v_stx_5620_);
v_a_6149_ = lean_ctor_get(v___x_6050_, 0);
v_isSharedCheck_6156_ = !lean_is_exclusive(v___x_6050_);
if (v_isSharedCheck_6156_ == 0)
{
v___x_6151_ = v___x_6050_;
v_isShared_6152_ = v_isSharedCheck_6156_;
goto v_resetjp_6150_;
}
else
{
lean_inc(v_a_6149_);
lean_dec(v___x_6050_);
v___x_6151_ = lean_box(0);
v_isShared_6152_ = v_isSharedCheck_6156_;
goto v_resetjp_6150_;
}
v_resetjp_6150_:
{
lean_object* v___x_6154_; 
if (v_isShared_6152_ == 0)
{
v___x_6154_ = v___x_6151_;
goto v_reusejp_6153_;
}
else
{
lean_object* v_reuseFailAlloc_6155_; 
v_reuseFailAlloc_6155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6155_, 0, v_a_6149_);
v___x_6154_ = v_reuseFailAlloc_6155_;
goto v_reusejp_6153_;
}
v_reusejp_6153_:
{
return v___x_6154_;
}
}
}
}
else
{
lean_object* v_a_6157_; lean_object* v___x_6159_; uint8_t v_isShared_6160_; uint8_t v_isSharedCheck_6164_; 
lean_dec(v_dec_x3f_6038_);
lean_dec(v___y_6037_);
lean_dec(v___y_6036_);
lean_dec(v___y_6033_);
lean_dec(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec(v___y_6029_);
lean_dec(v_stx_5620_);
v_a_6157_ = lean_ctor_get(v___x_6046_, 0);
v_isSharedCheck_6164_ = !lean_is_exclusive(v___x_6046_);
if (v_isSharedCheck_6164_ == 0)
{
v___x_6159_ = v___x_6046_;
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
else
{
lean_inc(v_a_6157_);
lean_dec(v___x_6046_);
v___x_6159_ = lean_box(0);
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
v_resetjp_6158_:
{
lean_object* v___x_6162_; 
if (v_isShared_6160_ == 0)
{
v___x_6162_ = v___x_6159_;
goto v_reusejp_6161_;
}
else
{
lean_object* v_reuseFailAlloc_6163_; 
v_reuseFailAlloc_6163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_a_6157_);
v___x_6162_ = v_reuseFailAlloc_6163_;
goto v_reusejp_6161_;
}
v_reusejp_6161_:
{
return v___x_6162_;
}
}
}
}
v___jp_6165_:
{
lean_object* v___x_6183_; uint8_t v___x_6184_; 
v___x_6183_ = l_Lean_Syntax_getArg(v_stx_5620_, v___y_6171_);
v___x_6184_ = l_Lean_Syntax_isNone(v___x_6183_);
if (v___x_6184_ == 0)
{
uint8_t v___x_6185_; 
lean_inc(v___x_6183_);
v___x_6185_ = l_Lean_Syntax_matchesNull(v___x_6183_, v___x_5633_);
if (v___x_6185_ == 0)
{
lean_object* v___x_6186_; 
lean_dec(v___x_6183_);
lean_dec(v_inv_x3f_6175_);
lean_dec(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec(v___y_6169_);
lean_dec(v___y_6168_);
lean_dec(v___y_6166_);
lean_dec(v_tk_6027_);
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_6186_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6186_;
}
else
{
lean_object* v_dec_x3f_6187_; lean_object* v___x_6188_; uint8_t v___x_6189_; 
v_dec_x3f_6187_ = l_Lean_Syntax_getArg(v___x_6183_, v___x_5637_);
lean_dec(v___x_6183_);
v___x_6188_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_x3f_6187_);
v___x_6189_ = l_Lean_Syntax_isOfKind(v_dec_x3f_6187_, v___x_6188_);
if (v___x_6189_ == 0)
{
lean_object* v___x_6190_; 
lean_dec(v_dec_x3f_6187_);
lean_dec(v_inv_x3f_6175_);
lean_dec(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec(v___y_6169_);
lean_dec(v___y_6168_);
lean_dec(v___y_6166_);
lean_dec(v_tk_6027_);
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_6190_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6190_;
}
else
{
lean_object* v___x_6191_; 
v___x_6191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6191_, 0, v_dec_x3f_6187_);
v___y_6029_ = v___y_6166_;
v___y_6030_ = v___y_6167_;
v___y_6031_ = v___y_6168_;
v___y_6032_ = v_inv_x3f_6175_;
v___y_6033_ = v___y_6169_;
v___y_6034_ = v___y_6170_;
v___y_6035_ = v___y_6172_;
v___y_6036_ = v___y_6173_;
v___y_6037_ = v___y_6174_;
v_dec_x3f_6038_ = v___x_6191_;
v___y_6039_ = v___y_6176_;
v___y_6040_ = v___y_6177_;
v___y_6041_ = v___y_6178_;
v___y_6042_ = v___y_6179_;
v___y_6043_ = v___y_6180_;
v___y_6044_ = v___y_6181_;
v___y_6045_ = v___y_6182_;
goto v___jp_6028_;
}
}
}
else
{
lean_object* v___x_6192_; 
lean_dec(v___x_6183_);
v___x_6192_ = lean_box(0);
v___y_6029_ = v___y_6166_;
v___y_6030_ = v___y_6167_;
v___y_6031_ = v___y_6168_;
v___y_6032_ = v_inv_x3f_6175_;
v___y_6033_ = v___y_6169_;
v___y_6034_ = v___y_6170_;
v___y_6035_ = v___y_6172_;
v___y_6036_ = v___y_6173_;
v___y_6037_ = v___y_6174_;
v_dec_x3f_6038_ = v___x_6192_;
v___y_6039_ = v___y_6176_;
v___y_6040_ = v___y_6177_;
v___y_6041_ = v___y_6178_;
v___y_6042_ = v___y_6179_;
v___y_6043_ = v___y_6180_;
v___y_6044_ = v___y_6181_;
v___y_6045_ = v___y_6182_;
goto v___jp_6028_;
}
}
v___jp_6193_:
{
lean_object* v_x_6202_; lean_object* v___x_6203_; uint8_t v___x_6204_; 
v_x_6202_ = l_Lean_Syntax_getArg(v___x_5638_, v___x_5633_);
v___x_6203_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__21));
lean_inc(v_x_6202_);
v___x_6204_ = l_Lean_Syntax_isOfKind(v_x_6202_, v___x_6203_);
if (v___x_6204_ == 0)
{
lean_object* v___x_6205_; 
lean_dec(v_x_6202_);
lean_dec(v_h_x3f_6194_);
lean_dec(v_tk_6027_);
lean_dec(v___x_5638_);
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_6205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6205_;
}
else
{
lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; uint8_t v___x_6210_; 
v___x_6206_ = lean_unsigned_to_nat(2u);
v___x_6207_ = lean_unsigned_to_nat(3u);
v___x_6208_ = l_Lean_Syntax_getArg(v___x_5638_, v___x_6207_);
lean_dec(v___x_5638_);
v___x_6209_ = l_Lean_Syntax_getArg(v_stx_5620_, v___x_6206_);
v___x_6210_ = l_Lean_Syntax_isNone(v___x_6209_);
if (v___x_6210_ == 0)
{
uint8_t v___x_6211_; 
lean_inc(v___x_6209_);
v___x_6211_ = l_Lean_Syntax_matchesNull(v___x_6209_, v___x_5633_);
if (v___x_6211_ == 0)
{
lean_object* v___x_6212_; 
lean_dec(v___x_6209_);
lean_dec(v___x_6208_);
lean_dec(v_x_6202_);
lean_dec(v_h_x3f_6194_);
lean_dec(v_tk_6027_);
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_6212_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6212_;
}
else
{
lean_object* v_inv_x3f_6213_; lean_object* v___x_6214_; uint8_t v___x_6215_; 
v_inv_x3f_6213_ = l_Lean_Syntax_getArg(v___x_6209_, v___x_5637_);
lean_dec(v___x_6209_);
v___x_6214_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_x3f_6213_);
v___x_6215_ = l_Lean_Syntax_isOfKind(v_inv_x3f_6213_, v___x_6214_);
if (v___x_6215_ == 0)
{
lean_object* v___x_6216_; 
lean_dec(v_inv_x3f_6213_);
lean_dec(v___x_6208_);
lean_dec(v_x_6202_);
lean_dec(v_h_x3f_6194_);
lean_dec(v_tk_6027_);
lean_dec_ref(v_dec_5621_);
lean_dec(v_stx_5620_);
v___x_6216_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6216_;
}
else
{
lean_object* v___x_6217_; 
v___x_6217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6217_, 0, v_inv_x3f_6213_);
lean_inc(v_x_6202_);
lean_inc(v_h_x3f_6194_);
v___y_6166_ = v_h_x3f_6194_;
v___y_6167_ = v___x_6204_;
v___y_6168_ = v_x_6202_;
v___y_6169_ = v_h_x3f_6194_;
v___y_6170_ = v___x_6206_;
v___y_6171_ = v___x_6207_;
v___y_6172_ = v___x_6204_;
v___y_6173_ = v_x_6202_;
v___y_6174_ = v___x_6208_;
v_inv_x3f_6175_ = v___x_6217_;
v___y_6176_ = v___y_6195_;
v___y_6177_ = v___y_6196_;
v___y_6178_ = v___y_6197_;
v___y_6179_ = v___y_6198_;
v___y_6180_ = v___y_6199_;
v___y_6181_ = v___y_6200_;
v___y_6182_ = v___y_6201_;
goto v___jp_6165_;
}
}
}
else
{
lean_object* v___x_6218_; 
lean_dec(v___x_6209_);
v___x_6218_ = lean_box(0);
lean_inc(v_x_6202_);
lean_inc(v_h_x3f_6194_);
v___y_6166_ = v_h_x3f_6194_;
v___y_6167_ = v___x_6204_;
v___y_6168_ = v_x_6202_;
v___y_6169_ = v_h_x3f_6194_;
v___y_6170_ = v___x_6206_;
v___y_6171_ = v___x_6207_;
v___y_6172_ = v___x_6204_;
v___y_6173_ = v_x_6202_;
v___y_6174_ = v___x_6208_;
v_inv_x3f_6175_ = v___x_6218_;
v___y_6176_ = v___y_6195_;
v___y_6177_ = v___y_6196_;
v___y_6178_ = v___y_6197_;
v___y_6179_ = v___y_6198_;
v___y_6180_ = v___y_6199_;
v___y_6181_ = v___y_6200_;
v___y_6182_ = v___y_6201_;
goto v___jp_6165_;
}
}
}
}
v___jp_5641_:
{
lean_object* v_doBlockResultType_5661_; lean_object* v___x_5662_; lean_object* v___y_5663_; lean_object* v___x_5664_; lean_object* v___f_5665_; lean_object* v___x_5666_; 
v_doBlockResultType_5661_ = lean_ctor_get(v___y_5654_, 3);
v___x_5662_ = lean_box(v___y_5644_);
lean_inc(v___y_5645_);
lean_inc_ref(v_doBlockResultType_5661_);
v___y_5663_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 19, 11);
lean_closure_set(v___y_5663_, 0, v___x_5662_);
lean_closure_set(v___y_5663_, 1, v___y_5649_);
lean_closure_set(v___y_5663_, 2, v___y_5650_);
lean_closure_set(v___y_5663_, 3, v_doBlockResultType_5661_);
lean_closure_set(v___y_5663_, 4, v___y_5648_);
lean_closure_set(v___y_5663_, 5, v___y_5645_);
lean_closure_set(v___y_5663_, 6, v___y_5643_);
lean_closure_set(v___y_5663_, 7, v___y_5646_);
lean_closure_set(v___y_5663_, 8, v___y_5642_);
lean_closure_set(v___y_5663_, 9, v___x_5637_);
lean_closure_set(v___y_5663_, 10, v___x_5633_);
v___x_5664_ = lean_box(v___x_5640_);
v___f_5665_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 13, 4);
lean_closure_set(v___f_5665_, 0, v___y_5647_);
lean_closure_set(v___f_5665_, 1, v___y_5663_);
lean_closure_set(v___f_5665_, 2, v___x_5633_);
lean_closure_set(v___f_5665_, 3, v___x_5664_);
lean_inc_ref(v___y_5652_);
v___x_5666_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___y_5651_, v___y_5652_, v___f_5665_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_);
if (lean_obj_tag(v___x_5666_) == 0)
{
lean_object* v_a_5667_; lean_object* v___x_5668_; 
v_a_5667_ = lean_ctor_get(v___x_5666_, 0);
lean_inc(v_a_5667_);
lean_dec_ref_known(v___x_5666_, 1);
lean_inc_ref(v_doBlockResultType_5661_);
v___x_5668_ = l_Lean_Elab_Do_mkBindApp(v___y_5652_, v_doBlockResultType_5661_, v_forIn_5653_, v_a_5667_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_);
return v___x_5668_;
}
else
{
lean_dec_ref(v_forIn_5653_);
lean_dec_ref(v___y_5652_);
return v___x_5666_;
}
}
v___jp_5669_:
{
lean_object* v___x_5699_; 
v___x_5699_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat(v___y_5679_, v___y_5682_, v___y_5697_, v___y_5693_, v___y_5695_, v___y_5681_, v___y_5692_, v___y_5691_, v___y_5698_);
lean_dec_ref(v___y_5679_);
if (lean_obj_tag(v___x_5699_) == 0)
{
lean_object* v_a_5700_; lean_object* v___x_5701_; lean_object* v_a_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; uint8_t v___x_5705_; 
v_a_5700_ = lean_ctor_get(v___x_5699_, 0);
lean_inc(v_a_5700_);
lean_dec_ref_known(v___x_5699_, 1);
v___x_5701_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(v___y_5694_, v___y_5692_);
v_a_5702_ = lean_ctor_get(v___x_5701_, 0);
lean_inc(v_a_5702_);
lean_dec_ref(v___x_5701_);
lean_inc_ref(v___y_5689_);
v___x_5703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5703_, 0, v___y_5683_);
lean_ctor_set(v___x_5703_, 1, v___y_5688_);
lean_ctor_set(v___x_5703_, 2, v___y_5684_);
lean_ctor_set(v___x_5703_, 3, v___y_5689_);
lean_ctor_set(v___x_5703_, 4, v_a_5700_);
v___x_5704_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__1));
v___x_5705_ = l_Lean_Expr_isConstOf(v_a_5702_, v___x_5704_);
lean_dec(v_a_5702_);
if (v___x_5705_ == 0)
{
if (lean_obj_tag(v___y_5690_) == 1)
{
lean_object* v_val_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v_a_5709_; lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5716_; 
lean_dec_ref_known(v___x_5703_, 5);
lean_dec_ref(v___y_5696_);
lean_dec_ref(v___y_5689_);
lean_dec(v___y_5687_);
lean_dec(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
v_val_5706_ = lean_ctor_get(v___y_5690_, 0);
lean_inc(v_val_5706_);
lean_dec_ref_known(v___y_5690_, 1);
v___x_5707_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__3, &l_Lean_Elab_Do_elabDoFor___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___closed__3);
v___x_5708_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_val_5706_, v___x_5707_, v___y_5697_, v___y_5693_, v___y_5695_, v___y_5681_, v___y_5692_, v___y_5691_, v___y_5698_);
lean_dec(v_val_5706_);
v_a_5709_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5716_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5716_ == 0)
{
v___x_5711_ = v___x_5708_;
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
else
{
lean_inc(v_a_5709_);
lean_dec(v___x_5708_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v___x_5714_; 
if (v_isShared_5712_ == 0)
{
v___x_5714_ = v___x_5711_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
return v___x_5714_;
}
}
}
else
{
lean_dec(v___y_5690_);
if (lean_obj_tag(v___y_5685_) == 1)
{
lean_object* v_val_5717_; lean_object* v___x_5718_; 
lean_dec_ref(v___y_5680_);
v_val_5717_ = lean_ctor_get(v___y_5685_, 0);
lean_inc(v_val_5717_);
lean_dec_ref_known(v___y_5685_, 1);
v___x_5718_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant(v___x_5703_, v_val_5717_, v___y_5686_, v___y_5696_, v___y_5697_, v___y_5693_, v___y_5695_, v___y_5681_, v___y_5692_, v___y_5691_, v___y_5698_);
lean_dec(v___y_5686_);
if (lean_obj_tag(v___x_5718_) == 0)
{
lean_object* v_a_5719_; 
v_a_5719_ = lean_ctor_get(v___x_5718_, 0);
lean_inc(v_a_5719_);
lean_dec_ref_known(v___x_5718_, 1);
v___y_5642_ = v___y_5670_;
v___y_5643_ = v___y_5671_;
v___y_5644_ = v___y_5672_;
v___y_5645_ = v___y_5673_;
v___y_5646_ = v___y_5674_;
v___y_5647_ = v___y_5675_;
v___y_5648_ = v___y_5677_;
v___y_5649_ = v___y_5676_;
v___y_5650_ = v___y_5678_;
v___y_5651_ = v___y_5687_;
v___y_5652_ = v___y_5689_;
v_forIn_5653_ = v_a_5719_;
v___y_5654_ = v___y_5697_;
v___y_5655_ = v___y_5693_;
v___y_5656_ = v___y_5695_;
v___y_5657_ = v___y_5681_;
v___y_5658_ = v___y_5692_;
v___y_5659_ = v___y_5691_;
v___y_5660_ = v___y_5698_;
goto v___jp_5641_;
}
else
{
lean_dec_ref(v___y_5689_);
lean_dec(v___y_5687_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
return v___x_5718_;
}
}
else
{
lean_dec_ref_known(v___x_5703_, 5);
lean_dec_ref(v___y_5696_);
lean_dec(v___y_5686_);
lean_dec(v___y_5685_);
v___y_5642_ = v___y_5670_;
v___y_5643_ = v___y_5671_;
v___y_5644_ = v___y_5672_;
v___y_5645_ = v___y_5673_;
v___y_5646_ = v___y_5674_;
v___y_5647_ = v___y_5675_;
v___y_5648_ = v___y_5677_;
v___y_5649_ = v___y_5676_;
v___y_5650_ = v___y_5678_;
v___y_5651_ = v___y_5687_;
v___y_5652_ = v___y_5689_;
v_forIn_5653_ = v___y_5680_;
v___y_5654_ = v___y_5697_;
v___y_5655_ = v___y_5693_;
v___y_5656_ = v___y_5695_;
v___y_5657_ = v___y_5681_;
v___y_5658_ = v___y_5692_;
v___y_5659_ = v___y_5691_;
v___y_5660_ = v___y_5698_;
goto v___jp_5641_;
}
}
}
else
{
lean_object* v___x_5720_; 
lean_dec_ref(v___y_5696_);
lean_dec(v___y_5686_);
v___x_5720_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget(v___x_5703_, v___y_5685_, v___y_5690_, v___y_5697_, v___y_5693_, v___y_5695_, v___y_5681_, v___y_5692_, v___y_5691_, v___y_5698_);
if (lean_obj_tag(v___x_5720_) == 0)
{
lean_object* v_a_5721_; 
v_a_5721_ = lean_ctor_get(v___x_5720_, 0);
lean_inc(v_a_5721_);
lean_dec_ref_known(v___x_5720_, 1);
if (lean_obj_tag(v_a_5721_) == 1)
{
lean_object* v_val_5722_; 
lean_dec_ref(v___y_5680_);
v_val_5722_ = lean_ctor_get(v_a_5721_, 0);
lean_inc(v_val_5722_);
lean_dec_ref_known(v_a_5721_, 1);
v___y_5642_ = v___y_5670_;
v___y_5643_ = v___y_5671_;
v___y_5644_ = v___y_5672_;
v___y_5645_ = v___y_5673_;
v___y_5646_ = v___y_5674_;
v___y_5647_ = v___y_5675_;
v___y_5648_ = v___y_5677_;
v___y_5649_ = v___y_5676_;
v___y_5650_ = v___y_5678_;
v___y_5651_ = v___y_5687_;
v___y_5652_ = v___y_5689_;
v_forIn_5653_ = v_val_5722_;
v___y_5654_ = v___y_5697_;
v___y_5655_ = v___y_5693_;
v___y_5656_ = v___y_5695_;
v___y_5657_ = v___y_5681_;
v___y_5658_ = v___y_5692_;
v___y_5659_ = v___y_5691_;
v___y_5660_ = v___y_5698_;
goto v___jp_5641_;
}
else
{
lean_dec(v_a_5721_);
v___y_5642_ = v___y_5670_;
v___y_5643_ = v___y_5671_;
v___y_5644_ = v___y_5672_;
v___y_5645_ = v___y_5673_;
v___y_5646_ = v___y_5674_;
v___y_5647_ = v___y_5675_;
v___y_5648_ = v___y_5677_;
v___y_5649_ = v___y_5676_;
v___y_5650_ = v___y_5678_;
v___y_5651_ = v___y_5687_;
v___y_5652_ = v___y_5689_;
v_forIn_5653_ = v___y_5680_;
v___y_5654_ = v___y_5697_;
v___y_5655_ = v___y_5693_;
v___y_5656_ = v___y_5695_;
v___y_5657_ = v___y_5681_;
v___y_5658_ = v___y_5692_;
v___y_5659_ = v___y_5691_;
v___y_5660_ = v___y_5698_;
goto v___jp_5641_;
}
}
else
{
lean_object* v_a_5723_; lean_object* v___x_5725_; uint8_t v_isShared_5726_; uint8_t v_isSharedCheck_5730_; 
lean_dec_ref(v___y_5689_);
lean_dec(v___y_5687_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
v_a_5723_ = lean_ctor_get(v___x_5720_, 0);
v_isSharedCheck_5730_ = !lean_is_exclusive(v___x_5720_);
if (v_isSharedCheck_5730_ == 0)
{
v___x_5725_ = v___x_5720_;
v_isShared_5726_ = v_isSharedCheck_5730_;
goto v_resetjp_5724_;
}
else
{
lean_inc(v_a_5723_);
lean_dec(v___x_5720_);
v___x_5725_ = lean_box(0);
v_isShared_5726_ = v_isSharedCheck_5730_;
goto v_resetjp_5724_;
}
v_resetjp_5724_:
{
lean_object* v___x_5728_; 
if (v_isShared_5726_ == 0)
{
v___x_5728_ = v___x_5725_;
goto v_reusejp_5727_;
}
else
{
lean_object* v_reuseFailAlloc_5729_; 
v_reuseFailAlloc_5729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_a_5723_);
v___x_5728_ = v_reuseFailAlloc_5729_;
goto v_reusejp_5727_;
}
v_reusejp_5727_:
{
return v___x_5728_;
}
}
}
}
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5738_; 
lean_dec_ref(v___y_5696_);
lean_dec_ref(v___y_5694_);
lean_dec(v___y_5690_);
lean_dec_ref(v___y_5689_);
lean_dec_ref(v___y_5688_);
lean_dec(v___y_5687_);
lean_dec(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec_ref(v___y_5683_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
v_a_5731_ = lean_ctor_get(v___x_5699_, 0);
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5699_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5733_ = v___x_5699_;
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_a_5731_);
lean_dec(v___x_5699_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5736_; 
if (v_isShared_5734_ == 0)
{
v___x_5736_ = v___x_5733_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_a_5731_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
return v___x_5736_;
}
}
}
}
v___jp_5739_:
{
lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___f_5778_; uint8_t v___x_5779_; lean_object* v___x_5780_; 
v___x_5776_ = l_Lean_instInhabitedExpr;
v___x_5777_ = lean_box(v___x_5640_);
lean_inc(v___y_5750_);
lean_inc(v___y_5744_);
lean_inc(v___y_5749_);
lean_inc_ref(v___y_5746_);
lean_inc_ref(v___y_5745_);
v___f_5778_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 24, 15);
lean_closure_set(v___f_5778_, 0, v___x_5776_);
lean_closure_set(v___f_5778_, 1, v___x_5637_);
lean_closure_set(v___f_5778_, 2, v___y_5743_);
lean_closure_set(v___f_5778_, 3, v___y_5745_);
lean_closure_set(v___f_5778_, 4, v___y_5746_);
lean_closure_set(v___f_5778_, 5, v___y_5749_);
lean_closure_set(v___f_5778_, 6, v___y_5751_);
lean_closure_set(v___f_5778_, 7, v___y_5754_);
lean_closure_set(v___f_5778_, 8, v___y_5752_);
lean_closure_set(v___f_5778_, 9, v___y_5747_);
lean_closure_set(v___f_5778_, 10, v___x_5777_);
lean_closure_set(v___f_5778_, 11, v___y_5744_);
lean_closure_set(v___f_5778_, 12, v___y_5750_);
lean_closure_set(v___f_5778_, 13, v___y_5748_);
lean_closure_set(v___f_5778_, 14, v___x_5633_);
v___x_5779_ = 0;
v___x_5780_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_5775_, v___f_5778_, v___x_5779_, v___y_5773_, v___y_5768_, v___y_5771_, v___y_5757_, v___y_5767_, v___y_5766_, v___y_5774_);
if (lean_obj_tag(v___x_5780_) == 0)
{
lean_object* v_a_5781_; lean_object* v___x_5782_; 
v_a_5781_ = lean_ctor_get(v___x_5780_, 0);
lean_inc_n(v_a_5781_, 2);
lean_dec_ref_known(v___x_5780_, 1);
v___x_5782_ = l_Lean_Expr_app___override(v___y_5770_, v_a_5781_);
if (lean_obj_tag(v___y_5760_) == 0)
{
if (v___y_5763_ == 0)
{
v___y_5670_ = v___y_5740_;
v___y_5671_ = v___y_5749_;
v___y_5672_ = v___y_5741_;
v___y_5673_ = v___y_5742_;
v___y_5674_ = v___y_5753_;
v___y_5675_ = v___y_5744_;
v___y_5676_ = v___y_5746_;
v___y_5677_ = v___y_5745_;
v___y_5678_ = v___y_5755_;
v___y_5679_ = v___y_5756_;
v___y_5680_ = v___x_5782_;
v___y_5681_ = v___y_5757_;
v___y_5682_ = v___y_5758_;
v___y_5683_ = v___y_5759_;
v___y_5684_ = v_a_5781_;
v___y_5685_ = v___y_5760_;
v___y_5686_ = v___y_5761_;
v___y_5687_ = v___y_5750_;
v___y_5688_ = v___y_5762_;
v___y_5689_ = v___y_5764_;
v___y_5690_ = v___y_5765_;
v___y_5691_ = v___y_5766_;
v___y_5692_ = v___y_5767_;
v___y_5693_ = v___y_5768_;
v___y_5694_ = v___y_5769_;
v___y_5695_ = v___y_5771_;
v___y_5696_ = v___y_5772_;
v___y_5697_ = v___y_5773_;
v___y_5698_ = v___y_5774_;
goto v___jp_5669_;
}
else
{
if (lean_obj_tag(v___y_5765_) == 0)
{
lean_dec(v_a_5781_);
lean_dec_ref(v___y_5772_);
lean_dec_ref(v___y_5769_);
lean_dec_ref(v___y_5762_);
lean_dec(v___y_5761_);
lean_dec_ref(v___y_5759_);
lean_dec_ref(v___y_5756_);
v___y_5642_ = v___y_5740_;
v___y_5643_ = v___y_5749_;
v___y_5644_ = v___y_5741_;
v___y_5645_ = v___y_5742_;
v___y_5646_ = v___y_5753_;
v___y_5647_ = v___y_5744_;
v___y_5648_ = v___y_5745_;
v___y_5649_ = v___y_5746_;
v___y_5650_ = v___y_5755_;
v___y_5651_ = v___y_5750_;
v___y_5652_ = v___y_5764_;
v_forIn_5653_ = v___x_5782_;
v___y_5654_ = v___y_5773_;
v___y_5655_ = v___y_5768_;
v___y_5656_ = v___y_5771_;
v___y_5657_ = v___y_5757_;
v___y_5658_ = v___y_5767_;
v___y_5659_ = v___y_5766_;
v___y_5660_ = v___y_5774_;
goto v___jp_5641_;
}
else
{
v___y_5670_ = v___y_5740_;
v___y_5671_ = v___y_5749_;
v___y_5672_ = v___y_5741_;
v___y_5673_ = v___y_5742_;
v___y_5674_ = v___y_5753_;
v___y_5675_ = v___y_5744_;
v___y_5676_ = v___y_5746_;
v___y_5677_ = v___y_5745_;
v___y_5678_ = v___y_5755_;
v___y_5679_ = v___y_5756_;
v___y_5680_ = v___x_5782_;
v___y_5681_ = v___y_5757_;
v___y_5682_ = v___y_5758_;
v___y_5683_ = v___y_5759_;
v___y_5684_ = v_a_5781_;
v___y_5685_ = v___y_5760_;
v___y_5686_ = v___y_5761_;
v___y_5687_ = v___y_5750_;
v___y_5688_ = v___y_5762_;
v___y_5689_ = v___y_5764_;
v___y_5690_ = v___y_5765_;
v___y_5691_ = v___y_5766_;
v___y_5692_ = v___y_5767_;
v___y_5693_ = v___y_5768_;
v___y_5694_ = v___y_5769_;
v___y_5695_ = v___y_5771_;
v___y_5696_ = v___y_5772_;
v___y_5697_ = v___y_5773_;
v___y_5698_ = v___y_5774_;
goto v___jp_5669_;
}
}
}
else
{
v___y_5670_ = v___y_5740_;
v___y_5671_ = v___y_5749_;
v___y_5672_ = v___y_5741_;
v___y_5673_ = v___y_5742_;
v___y_5674_ = v___y_5753_;
v___y_5675_ = v___y_5744_;
v___y_5676_ = v___y_5746_;
v___y_5677_ = v___y_5745_;
v___y_5678_ = v___y_5755_;
v___y_5679_ = v___y_5756_;
v___y_5680_ = v___x_5782_;
v___y_5681_ = v___y_5757_;
v___y_5682_ = v___y_5758_;
v___y_5683_ = v___y_5759_;
v___y_5684_ = v_a_5781_;
v___y_5685_ = v___y_5760_;
v___y_5686_ = v___y_5761_;
v___y_5687_ = v___y_5750_;
v___y_5688_ = v___y_5762_;
v___y_5689_ = v___y_5764_;
v___y_5690_ = v___y_5765_;
v___y_5691_ = v___y_5766_;
v___y_5692_ = v___y_5767_;
v___y_5693_ = v___y_5768_;
v___y_5694_ = v___y_5769_;
v___y_5695_ = v___y_5771_;
v___y_5696_ = v___y_5772_;
v___y_5697_ = v___y_5773_;
v___y_5698_ = v___y_5774_;
goto v___jp_5669_;
}
}
else
{
lean_dec_ref(v___y_5772_);
lean_dec_ref(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5765_);
lean_dec_ref(v___y_5764_);
lean_dec_ref(v___y_5762_);
lean_dec(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec_ref(v___y_5756_);
lean_dec(v___y_5755_);
lean_dec_ref(v___y_5753_);
lean_dec(v___y_5750_);
lean_dec(v___y_5749_);
lean_dec_ref(v___y_5746_);
lean_dec_ref(v___y_5745_);
lean_dec(v___y_5744_);
lean_dec_ref(v___y_5740_);
return v___x_5780_;
}
}
v___jp_5783_:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; 
v___x_5827_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_5828_ = l_Lean_Core_mkFreshUserName(v___x_5827_, v___y_5825_, v___y_5826_);
if (lean_obj_tag(v___x_5828_) == 0)
{
if (lean_obj_tag(v___y_5811_) == 1)
{
if (lean_obj_tag(v_snd_5819_) == 1)
{
lean_object* v_a_5829_; lean_object* v_val_5830_; lean_object* v_val_5831_; lean_object* v___f_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
lean_dec_ref(v___y_5812_);
v_a_5829_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_a_5829_);
lean_dec_ref_known(v___x_5828_, 1);
v_val_5830_ = lean_ctor_get(v___y_5811_, 0);
v_val_5831_ = lean_ctor_get(v_snd_5819_, 0);
lean_inc(v_val_5831_);
lean_dec_ref_known(v_snd_5819_, 1);
v___f_5832_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_5832_, 0, v___y_5799_);
lean_closure_set(v___f_5832_, 1, v___y_5788_);
lean_closure_set(v___f_5832_, 2, v___x_5637_);
lean_closure_set(v___f_5832_, 3, v___y_5803_);
lean_closure_set(v___f_5832_, 4, v___y_5802_);
lean_closure_set(v___f_5832_, 5, v_val_5831_);
lean_closure_set(v___f_5832_, 6, v___y_5786_);
v___x_5833_ = l_Lean_TSyntax_getId(v___y_5808_);
lean_dec(v___y_5808_);
v___x_5834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5833_);
lean_ctor_set(v___x_5834_, 1, v___y_5809_);
v___x_5835_ = l_Lean_TSyntax_getId(v_val_5830_);
v___x_5836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5836_, 0, v___x_5835_);
lean_ctor_set(v___x_5836_, 1, v___f_5832_);
v___x_5837_ = lean_mk_empty_array_with_capacity(v___y_5813_);
v___x_5838_ = lean_array_push(v___x_5837_, v___x_5834_);
v___x_5839_ = lean_array_push(v___x_5838_, v___x_5836_);
lean_inc_ref(v___y_5797_);
v___y_5740_ = v___y_5784_;
v___y_5741_ = v___y_5785_;
v___y_5742_ = v___y_5787_;
v___y_5743_ = v___y_5789_;
v___y_5744_ = v___y_5790_;
v___y_5745_ = v___y_5791_;
v___y_5746_ = v___y_5792_;
v___y_5747_ = v___y_5793_;
v___y_5748_ = v___y_5794_;
v___y_5749_ = v___y_5795_;
v___y_5750_ = v_a_5829_;
v___y_5751_ = v___y_5797_;
v___y_5752_ = v___y_5798_;
v___y_5753_ = v___y_5800_;
v___y_5754_ = v___y_5801_;
v___y_5755_ = v___y_5804_;
v___y_5756_ = v___y_5805_;
v___y_5757_ = v___y_5823_;
v___y_5758_ = v___y_5806_;
v___y_5759_ = v___y_5807_;
v___y_5760_ = v___y_5810_;
v___y_5761_ = v___y_5811_;
v___y_5762_ = v___y_5796_;
v___y_5763_ = v___y_5814_;
v___y_5764_ = v___y_5797_;
v___y_5765_ = v___y_5815_;
v___y_5766_ = v___y_5825_;
v___y_5767_ = v___y_5824_;
v___y_5768_ = v___y_5821_;
v___y_5769_ = v___y_5816_;
v___y_5770_ = v_fst_5818_;
v___y_5771_ = v___y_5822_;
v___y_5772_ = v___y_5817_;
v___y_5773_ = v___y_5820_;
v___y_5774_ = v___y_5826_;
v___y_5775_ = v___x_5839_;
goto v___jp_5739_;
}
else
{
lean_object* v_a_5840_; lean_object* v___x_5841_; 
lean_dec_ref(v___y_5809_);
lean_dec(v___y_5808_);
lean_dec_ref(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___y_5799_);
lean_dec(v___y_5788_);
lean_dec_ref(v___y_5786_);
v_a_5840_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_a_5840_);
lean_dec_ref_known(v___x_5828_, 1);
lean_inc_ref(v___y_5811_);
v___x_5841_ = lean_apply_2(v___y_5812_, v___y_5811_, v_snd_5819_);
lean_inc_ref(v___y_5797_);
v___y_5740_ = v___y_5784_;
v___y_5741_ = v___y_5785_;
v___y_5742_ = v___y_5787_;
v___y_5743_ = v___y_5789_;
v___y_5744_ = v___y_5790_;
v___y_5745_ = v___y_5791_;
v___y_5746_ = v___y_5792_;
v___y_5747_ = v___y_5793_;
v___y_5748_ = v___y_5794_;
v___y_5749_ = v___y_5795_;
v___y_5750_ = v_a_5840_;
v___y_5751_ = v___y_5797_;
v___y_5752_ = v___y_5798_;
v___y_5753_ = v___y_5800_;
v___y_5754_ = v___y_5801_;
v___y_5755_ = v___y_5804_;
v___y_5756_ = v___y_5805_;
v___y_5757_ = v___y_5823_;
v___y_5758_ = v___y_5806_;
v___y_5759_ = v___y_5807_;
v___y_5760_ = v___y_5810_;
v___y_5761_ = v___y_5811_;
v___y_5762_ = v___y_5796_;
v___y_5763_ = v___y_5814_;
v___y_5764_ = v___y_5797_;
v___y_5765_ = v___y_5815_;
v___y_5766_ = v___y_5825_;
v___y_5767_ = v___y_5824_;
v___y_5768_ = v___y_5821_;
v___y_5769_ = v___y_5816_;
v___y_5770_ = v_fst_5818_;
v___y_5771_ = v___y_5822_;
v___y_5772_ = v___y_5817_;
v___y_5773_ = v___y_5820_;
v___y_5774_ = v___y_5826_;
v___y_5775_ = v___x_5841_;
goto v___jp_5739_;
}
}
else
{
lean_object* v_a_5842_; lean_object* v___x_5843_; 
lean_dec_ref(v___y_5809_);
lean_dec(v___y_5808_);
lean_dec_ref(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___y_5799_);
lean_dec(v___y_5788_);
lean_dec_ref(v___y_5786_);
v_a_5842_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_a_5842_);
lean_dec_ref_known(v___x_5828_, 1);
lean_inc(v___y_5811_);
v___x_5843_ = lean_apply_2(v___y_5812_, v___y_5811_, v_snd_5819_);
lean_inc_ref(v___y_5797_);
v___y_5740_ = v___y_5784_;
v___y_5741_ = v___y_5785_;
v___y_5742_ = v___y_5787_;
v___y_5743_ = v___y_5789_;
v___y_5744_ = v___y_5790_;
v___y_5745_ = v___y_5791_;
v___y_5746_ = v___y_5792_;
v___y_5747_ = v___y_5793_;
v___y_5748_ = v___y_5794_;
v___y_5749_ = v___y_5795_;
v___y_5750_ = v_a_5842_;
v___y_5751_ = v___y_5797_;
v___y_5752_ = v___y_5798_;
v___y_5753_ = v___y_5800_;
v___y_5754_ = v___y_5801_;
v___y_5755_ = v___y_5804_;
v___y_5756_ = v___y_5805_;
v___y_5757_ = v___y_5823_;
v___y_5758_ = v___y_5806_;
v___y_5759_ = v___y_5807_;
v___y_5760_ = v___y_5810_;
v___y_5761_ = v___y_5811_;
v___y_5762_ = v___y_5796_;
v___y_5763_ = v___y_5814_;
v___y_5764_ = v___y_5797_;
v___y_5765_ = v___y_5815_;
v___y_5766_ = v___y_5825_;
v___y_5767_ = v___y_5824_;
v___y_5768_ = v___y_5821_;
v___y_5769_ = v___y_5816_;
v___y_5770_ = v_fst_5818_;
v___y_5771_ = v___y_5822_;
v___y_5772_ = v___y_5817_;
v___y_5773_ = v___y_5820_;
v___y_5774_ = v___y_5826_;
v___y_5775_ = v___x_5843_;
goto v___jp_5739_;
}
}
else
{
lean_object* v_a_5844_; lean_object* v___x_5846_; uint8_t v_isShared_5847_; uint8_t v_isSharedCheck_5851_; 
lean_dec(v_snd_5819_);
lean_dec_ref(v_fst_5818_);
lean_dec_ref(v___y_5817_);
lean_dec_ref(v___y_5816_);
lean_dec(v___y_5815_);
lean_dec_ref(v___y_5812_);
lean_dec(v___y_5811_);
lean_dec(v___y_5810_);
lean_dec_ref(v___y_5809_);
lean_dec(v___y_5808_);
lean_dec_ref(v___y_5807_);
lean_dec_ref(v___y_5805_);
lean_dec(v___y_5804_);
lean_dec_ref(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec_ref(v___y_5801_);
lean_dec_ref(v___y_5800_);
lean_dec(v___y_5799_);
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec_ref(v___y_5796_);
lean_dec(v___y_5795_);
lean_dec(v___y_5794_);
lean_dec(v___y_5793_);
lean_dec_ref(v___y_5792_);
lean_dec_ref(v___y_5791_);
lean_dec(v___y_5790_);
lean_dec(v___y_5789_);
lean_dec(v___y_5788_);
lean_dec_ref(v___y_5786_);
lean_dec_ref(v___y_5784_);
v_a_5844_ = lean_ctor_get(v___x_5828_, 0);
v_isSharedCheck_5851_ = !lean_is_exclusive(v___x_5828_);
if (v_isSharedCheck_5851_ == 0)
{
v___x_5846_ = v___x_5828_;
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
else
{
lean_inc(v_a_5844_);
lean_dec(v___x_5828_);
v___x_5846_ = lean_box(0);
v_isShared_5847_ = v_isSharedCheck_5851_;
goto v_resetjp_5845_;
}
v_resetjp_5845_:
{
lean_object* v___x_5849_; 
if (v_isShared_5847_ == 0)
{
v___x_5849_ = v___x_5846_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_a_5844_);
v___x_5849_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
return v___x_5849_;
}
}
}
}
v___jp_5852_:
{
lean_object* v___x_5892_; lean_object* v___x_5893_; 
v___x_5892_ = lean_box(0);
lean_inc_ref(v___y_5864_);
lean_inc(v___y_5883_);
lean_inc_ref(v___y_5871_);
lean_inc(v___y_5872_);
lean_inc_ref(v___y_5875_);
lean_inc(v___y_5874_);
lean_inc_ref(v___y_5888_);
v___x_5893_ = lean_apply_8(v___y_5864_, v___x_5892_, v___y_5888_, v___y_5874_, v___y_5875_, v___y_5872_, v___y_5871_, v___y_5883_, lean_box(0));
if (lean_obj_tag(v___x_5893_) == 0)
{
lean_object* v_a_5894_; lean_object* v_m_5895_; lean_object* v_u_5896_; lean_object* v_v_5897_; lean_object* v___x_5898_; 
v_a_5894_ = lean_ctor_get(v___x_5893_, 0);
lean_inc(v_a_5894_);
lean_dec_ref_known(v___x_5893_, 1);
v_m_5895_ = lean_ctor_get(v___y_5873_, 0);
v_u_5896_ = lean_ctor_get(v___y_5873_, 1);
v_v_5897_ = lean_ctor_get(v___y_5873_, 2);
lean_inc(v_u_5896_);
v___x_5898_ = l_Lean_Meta_mkProdMkN(v_a_5894_, v_u_5896_, v___y_5875_, v___y_5872_, v___y_5871_, v___y_5883_);
if (lean_obj_tag(v___x_5898_) == 0)
{
lean_object* v_a_5899_; 
v_a_5899_ = lean_ctor_get(v___x_5898_, 0);
lean_inc(v_a_5899_);
lean_dec_ref_known(v___x_5898_, 1);
if (lean_obj_tag(v___y_5882_) == 0)
{
lean_object* v_fst_5900_; lean_object* v_snd_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5920_; 
v_fst_5900_ = lean_ctor_get(v_a_5899_, 0);
v_snd_5901_ = lean_ctor_get(v_a_5899_, 1);
v_isSharedCheck_5920_ = !lean_is_exclusive(v_a_5899_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5903_ = v_a_5899_;
v_isShared_5904_ = v_isSharedCheck_5920_;
goto v_resetjp_5902_;
}
else
{
lean_inc(v_snd_5901_);
lean_inc(v_fst_5900_);
lean_dec(v_a_5899_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5920_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5908_; 
v___x_5905_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__5));
v___x_5906_ = lean_box(0);
lean_inc(v_v_5897_);
if (v_isShared_5904_ == 0)
{
lean_ctor_set_tag(v___x_5903_, 1);
lean_ctor_set(v___x_5903_, 1, v___x_5906_);
lean_ctor_set(v___x_5903_, 0, v_v_5897_);
v___x_5908_ = v___x_5903_;
goto v_reusejp_5907_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_v_5897_);
lean_ctor_set(v_reuseFailAlloc_5919_, 1, v___x_5906_);
v___x_5908_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5907_;
}
v_reusejp_5907_:
{
lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
lean_inc(v_u_5896_);
v___x_5909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5909_, 0, v_u_5896_);
lean_ctor_set(v___x_5909_, 1, v___x_5908_);
v___x_5910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___y_5880_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___y_5876_);
lean_ctor_set(v___x_5911_, 1, v___x_5910_);
lean_inc_ref(v___x_5911_);
v___x_5912_ = l_Lean_mkConst(v___x_5905_, v___x_5911_);
lean_inc_ref(v___y_5890_);
lean_inc_ref(v___y_5889_);
lean_inc_ref(v_m_5895_);
v___x_5913_ = l_Lean_mkApp3(v___x_5912_, v_m_5895_, v___y_5889_, v___y_5890_);
v___x_5914_ = l_Lean_Elab_Term_mkInstMVar(v___x_5913_, v___x_5892_, v___y_5888_, v___y_5874_, v___y_5875_, v___y_5872_, v___y_5871_, v___y_5883_);
if (lean_obj_tag(v___x_5914_) == 0)
{
lean_object* v_a_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; 
v_a_5915_ = lean_ctor_get(v___x_5914_, 0);
lean_inc(v_a_5915_);
lean_dec_ref_known(v___x_5914_, 1);
v___x_5916_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__7));
v___x_5917_ = l_Lean_mkConst(v___x_5916_, v___x_5911_);
lean_inc(v_fst_5900_);
lean_inc_ref(v___y_5878_);
lean_inc(v_snd_5901_);
lean_inc_ref(v___y_5890_);
lean_inc_ref(v___y_5889_);
lean_inc_ref(v_m_5895_);
v___x_5918_ = l_Lean_mkApp7(v___x_5917_, v_m_5895_, v___y_5889_, v___y_5890_, v_a_5915_, v_snd_5901_, v___y_5878_, v_fst_5900_);
lean_inc(v_u_5896_);
v___y_5784_ = v___y_5853_;
v___y_5785_ = v___y_5854_;
v___y_5786_ = v___y_5855_;
v___y_5787_ = v_v_5897_;
v___y_5788_ = v___y_5856_;
v___y_5789_ = v___y_5857_;
v___y_5790_ = v___y_5891_;
v___y_5791_ = v___y_5858_;
v___y_5792_ = v___y_5859_;
v___y_5793_ = v___y_5860_;
v___y_5794_ = v___y_5861_;
v___y_5795_ = v_u_5896_;
v___y_5796_ = v_fst_5900_;
v___y_5797_ = v_snd_5901_;
v___y_5798_ = v___x_5892_;
v___y_5799_ = v___y_5862_;
v___y_5800_ = v___y_5863_;
v___y_5801_ = v___y_5864_;
v___y_5802_ = v___y_5865_;
v___y_5803_ = v___y_5866_;
v___y_5804_ = v___y_5867_;
v___y_5805_ = v___y_5877_;
v___y_5806_ = v___y_5854_;
v___y_5807_ = v___y_5878_;
v___y_5808_ = v___y_5879_;
v___y_5809_ = v___y_5870_;
v___y_5810_ = v___y_5881_;
v___y_5811_ = v___y_5882_;
v___y_5812_ = v___y_5884_;
v___y_5813_ = v___y_5885_;
v___y_5814_ = v___y_5886_;
v___y_5815_ = v___y_5887_;
v___y_5816_ = v___y_5889_;
v___y_5817_ = v___y_5890_;
v_fst_5818_ = v___x_5918_;
v_snd_5819_ = v___x_5892_;
v___y_5820_ = v___y_5868_;
v___y_5821_ = v___y_5888_;
v___y_5822_ = v___y_5874_;
v___y_5823_ = v___y_5875_;
v___y_5824_ = v___y_5872_;
v___y_5825_ = v___y_5871_;
v___y_5826_ = v___y_5883_;
goto v___jp_5783_;
}
else
{
lean_dec_ref_known(v___x_5911_, 2);
lean_dec(v_snd_5901_);
lean_dec(v_fst_5900_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec_ref(v___y_5889_);
lean_dec(v___y_5887_);
lean_dec_ref(v___y_5884_);
lean_dec(v___y_5881_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec_ref(v___y_5877_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec_ref(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec(v___y_5861_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec(v___y_5857_);
lean_dec(v___y_5856_);
lean_dec_ref(v___y_5855_);
lean_dec_ref(v___y_5853_);
return v___x_5914_;
}
}
}
}
else
{
lean_object* v_fst_5921_; lean_object* v_snd_5922_; lean_object* v___x_5924_; uint8_t v_isShared_5925_; uint8_t v_isSharedCheck_5957_; 
v_fst_5921_ = lean_ctor_get(v_a_5899_, 0);
v_snd_5922_ = lean_ctor_get(v_a_5899_, 1);
v_isSharedCheck_5957_ = !lean_is_exclusive(v_a_5899_);
if (v_isSharedCheck_5957_ == 0)
{
v___x_5924_ = v_a_5899_;
v_isShared_5925_ = v_isSharedCheck_5957_;
goto v_resetjp_5923_;
}
else
{
lean_inc(v_snd_5922_);
lean_inc(v_fst_5921_);
lean_dec(v_a_5899_);
v___x_5924_ = lean_box(0);
v_isShared_5925_ = v_isSharedCheck_5957_;
goto v_resetjp_5923_;
}
v_resetjp_5923_:
{
lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5929_; 
v___x_5926_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
v___x_5927_ = lean_box(0);
lean_inc(v___y_5876_);
if (v_isShared_5925_ == 0)
{
lean_ctor_set_tag(v___x_5924_, 1);
lean_ctor_set(v___x_5924_, 1, v___x_5927_);
lean_ctor_set(v___x_5924_, 0, v___y_5876_);
v___x_5929_ = v___x_5924_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5956_; 
v_reuseFailAlloc_5956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5956_, 0, v___y_5876_);
lean_ctor_set(v_reuseFailAlloc_5956_, 1, v___x_5927_);
v___x_5929_ = v_reuseFailAlloc_5956_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; 
lean_inc(v___y_5880_);
v___x_5930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___y_5880_);
lean_ctor_set(v___x_5930_, 1, v___x_5929_);
v___x_5931_ = l_Lean_mkConst(v___x_5926_, v___x_5930_);
lean_inc_ref(v___y_5889_);
lean_inc_ref(v___y_5890_);
v___x_5932_ = l_Lean_mkAppB(v___x_5931_, v___y_5890_, v___y_5889_);
v___x_5933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5932_);
v___x_5934_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_5935_ = l_Lean_Meta_mkFreshExprMVar(v___x_5933_, v___y_5869_, v___x_5934_, v___y_5875_, v___y_5872_, v___y_5871_, v___y_5883_);
if (lean_obj_tag(v___x_5935_) == 0)
{
lean_object* v_a_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; 
v_a_5936_ = lean_ctor_get(v___x_5935_, 0);
lean_inc_n(v_a_5936_, 2);
lean_dec_ref_known(v___x_5935_, 1);
v___x_5937_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__12));
lean_inc(v_v_5897_);
v___x_5938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5938_, 0, v_v_5897_);
lean_ctor_set(v___x_5938_, 1, v___x_5927_);
lean_inc(v_u_5896_);
v___x_5939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5939_, 0, v_u_5896_);
lean_ctor_set(v___x_5939_, 1, v___x_5938_);
v___x_5940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___y_5880_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___y_5876_);
lean_ctor_set(v___x_5941_, 1, v___x_5940_);
lean_inc_ref(v___x_5941_);
v___x_5942_ = l_Lean_mkConst(v___x_5937_, v___x_5941_);
lean_inc_ref(v___y_5890_);
lean_inc_ref(v___y_5889_);
lean_inc_ref(v_m_5895_);
v___x_5943_ = l_Lean_mkApp4(v___x_5942_, v_m_5895_, v___y_5889_, v___y_5890_, v_a_5936_);
v___x_5944_ = l_Lean_Elab_Term_mkInstMVar(v___x_5943_, v___x_5892_, v___y_5888_, v___y_5874_, v___y_5875_, v___y_5872_, v___y_5871_, v___y_5883_);
if (lean_obj_tag(v___x_5944_) == 0)
{
lean_object* v_a_5945_; lean_object* v___x_5947_; uint8_t v_isShared_5948_; uint8_t v_isSharedCheck_5955_; 
v_a_5945_ = lean_ctor_get(v___x_5944_, 0);
v_isSharedCheck_5955_ = !lean_is_exclusive(v___x_5944_);
if (v_isSharedCheck_5955_ == 0)
{
v___x_5947_ = v___x_5944_;
v_isShared_5948_ = v_isSharedCheck_5955_;
goto v_resetjp_5946_;
}
else
{
lean_inc(v_a_5945_);
lean_dec(v___x_5944_);
v___x_5947_ = lean_box(0);
v_isShared_5948_ = v_isSharedCheck_5955_;
goto v_resetjp_5946_;
}
v_resetjp_5946_:
{
lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5953_; 
v___x_5949_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__14));
v___x_5950_ = l_Lean_mkConst(v___x_5949_, v___x_5941_);
lean_inc(v_fst_5921_);
lean_inc_ref(v___y_5878_);
lean_inc(v_snd_5922_);
lean_inc(v_a_5936_);
lean_inc_ref(v___y_5890_);
lean_inc_ref(v___y_5889_);
lean_inc_ref(v_m_5895_);
v___x_5951_ = l_Lean_mkApp8(v___x_5950_, v_m_5895_, v___y_5889_, v___y_5890_, v_a_5936_, v_a_5945_, v_snd_5922_, v___y_5878_, v_fst_5921_);
if (v_isShared_5948_ == 0)
{
lean_ctor_set_tag(v___x_5947_, 1);
lean_ctor_set(v___x_5947_, 0, v_a_5936_);
v___x_5953_ = v___x_5947_;
goto v_reusejp_5952_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_a_5936_);
v___x_5953_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5952_;
}
v_reusejp_5952_:
{
lean_inc(v_u_5896_);
v___y_5784_ = v___y_5853_;
v___y_5785_ = v___y_5854_;
v___y_5786_ = v___y_5855_;
v___y_5787_ = v_v_5897_;
v___y_5788_ = v___y_5856_;
v___y_5789_ = v___y_5857_;
v___y_5790_ = v___y_5891_;
v___y_5791_ = v___y_5858_;
v___y_5792_ = v___y_5859_;
v___y_5793_ = v___y_5860_;
v___y_5794_ = v___y_5861_;
v___y_5795_ = v_u_5896_;
v___y_5796_ = v_fst_5921_;
v___y_5797_ = v_snd_5922_;
v___y_5798_ = v___x_5892_;
v___y_5799_ = v___y_5862_;
v___y_5800_ = v___y_5863_;
v___y_5801_ = v___y_5864_;
v___y_5802_ = v___y_5865_;
v___y_5803_ = v___y_5866_;
v___y_5804_ = v___y_5867_;
v___y_5805_ = v___y_5877_;
v___y_5806_ = v___y_5854_;
v___y_5807_ = v___y_5878_;
v___y_5808_ = v___y_5879_;
v___y_5809_ = v___y_5870_;
v___y_5810_ = v___y_5881_;
v___y_5811_ = v___y_5882_;
v___y_5812_ = v___y_5884_;
v___y_5813_ = v___y_5885_;
v___y_5814_ = v___y_5886_;
v___y_5815_ = v___y_5887_;
v___y_5816_ = v___y_5889_;
v___y_5817_ = v___y_5890_;
v_fst_5818_ = v___x_5951_;
v_snd_5819_ = v___x_5953_;
v___y_5820_ = v___y_5868_;
v___y_5821_ = v___y_5888_;
v___y_5822_ = v___y_5874_;
v___y_5823_ = v___y_5875_;
v___y_5824_ = v___y_5872_;
v___y_5825_ = v___y_5871_;
v___y_5826_ = v___y_5883_;
goto v___jp_5783_;
}
}
}
else
{
lean_dec_ref_known(v___x_5941_, 2);
lean_dec(v_a_5936_);
lean_dec(v_snd_5922_);
lean_dec_ref_known(v___y_5882_, 1);
lean_dec(v_fst_5921_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec_ref(v___y_5889_);
lean_dec(v___y_5887_);
lean_dec_ref(v___y_5884_);
lean_dec(v___y_5881_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec_ref(v___y_5877_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec_ref(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec(v___y_5861_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec(v___y_5857_);
lean_dec(v___y_5856_);
lean_dec_ref(v___y_5855_);
lean_dec_ref(v___y_5853_);
return v___x_5944_;
}
}
else
{
lean_dec(v_snd_5922_);
lean_dec_ref_known(v___y_5882_, 1);
lean_dec(v_fst_5921_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec_ref(v___y_5889_);
lean_dec(v___y_5887_);
lean_dec_ref(v___y_5884_);
lean_dec(v___y_5881_);
lean_dec(v___y_5880_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec_ref(v___y_5877_);
lean_dec(v___y_5876_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec_ref(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec(v___y_5861_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec(v___y_5857_);
lean_dec(v___y_5856_);
lean_dec_ref(v___y_5855_);
lean_dec_ref(v___y_5853_);
return v___x_5935_;
}
}
}
}
}
else
{
lean_object* v_a_5958_; lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_5965_; 
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec_ref(v___y_5889_);
lean_dec(v___y_5887_);
lean_dec_ref(v___y_5884_);
lean_dec(v___y_5882_);
lean_dec(v___y_5881_);
lean_dec(v___y_5880_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec_ref(v___y_5877_);
lean_dec(v___y_5876_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec_ref(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec(v___y_5861_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec(v___y_5857_);
lean_dec(v___y_5856_);
lean_dec_ref(v___y_5855_);
lean_dec_ref(v___y_5853_);
v_a_5958_ = lean_ctor_get(v___x_5898_, 0);
v_isSharedCheck_5965_ = !lean_is_exclusive(v___x_5898_);
if (v_isSharedCheck_5965_ == 0)
{
v___x_5960_ = v___x_5898_;
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
else
{
lean_inc(v_a_5958_);
lean_dec(v___x_5898_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v___x_5963_; 
if (v_isShared_5961_ == 0)
{
v___x_5963_ = v___x_5960_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5964_; 
v_reuseFailAlloc_5964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5964_, 0, v_a_5958_);
v___x_5963_ = v_reuseFailAlloc_5964_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
return v___x_5963_;
}
}
}
}
else
{
lean_object* v_a_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5973_; 
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec_ref(v___y_5889_);
lean_dec(v___y_5887_);
lean_dec_ref(v___y_5884_);
lean_dec(v___y_5882_);
lean_dec(v___y_5881_);
lean_dec(v___y_5880_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec_ref(v___y_5877_);
lean_dec(v___y_5876_);
lean_dec_ref(v___y_5870_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec_ref(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec_ref(v___y_5863_);
lean_dec(v___y_5862_);
lean_dec(v___y_5861_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec(v___y_5857_);
lean_dec(v___y_5856_);
lean_dec_ref(v___y_5855_);
lean_dec_ref(v___y_5853_);
v_a_5966_ = lean_ctor_get(v___x_5893_, 0);
v_isSharedCheck_5973_ = !lean_is_exclusive(v___x_5893_);
if (v_isSharedCheck_5973_ == 0)
{
v___x_5968_ = v___x_5893_;
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_a_5966_);
lean_dec(v___x_5893_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5971_; 
if (v_isShared_5969_ == 0)
{
v___x_5971_ = v___x_5968_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_a_5966_);
v___x_5971_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
return v___x_5971_;
}
}
}
}
v___jp_5974_:
{
uint8_t v_returnsEarly_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___f_6016_; 
v_returnsEarly_6013_ = lean_ctor_get_uint8(v___y_5998_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_5998_);
v___x_6014_ = lean_box(v_returnsEarly_6013_);
v___x_6015_ = lean_box(v___y_5985_);
lean_inc_ref(v___y_5978_);
lean_inc_ref(v___y_5982_);
lean_inc_ref(v___y_6012_);
v___f_6016_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 14, 6);
lean_closure_set(v___f_6016_, 0, v___y_6012_);
lean_closure_set(v___f_6016_, 1, v___y_5982_);
lean_closure_set(v___f_6016_, 2, v___x_6014_);
lean_closure_set(v___f_6016_, 3, v___x_5637_);
lean_closure_set(v___f_6016_, 4, v___y_5978_);
lean_closure_set(v___f_6016_, 5, v___x_6015_);
if (v_returnsEarly_6013_ == 0)
{
size_t v_sz_6017_; size_t v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; 
lean_dec(v___y_6011_);
v_sz_6017_ = lean_array_size(v___y_6012_);
v___x_6018_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6012_, 2);
v___x_6019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_6017_, v___x_6018_, v___y_6012_);
v___x_6020_ = lean_array_to_list(v___x_6019_);
v___y_5853_ = v___y_6012_;
v___y_5854_ = v_returnsEarly_6013_;
v___y_5855_ = v___y_5975_;
v___y_5856_ = v___y_5976_;
v___y_5857_ = v___y_5977_;
v___y_5858_ = v___y_5978_;
v___y_5859_ = v___y_5979_;
v___y_5860_ = v___y_5981_;
v___y_5861_ = v___y_5983_;
v___y_5862_ = v___y_5986_;
v___y_5863_ = v___y_5987_;
v___y_5864_ = v___f_6016_;
v___y_5865_ = v___y_5988_;
v___y_5866_ = v___y_5990_;
v___y_5867_ = v___y_5989_;
v___y_5868_ = v___y_5991_;
v___y_5869_ = v___y_5992_;
v___y_5870_ = v___y_5980_;
v___y_5871_ = v___y_5993_;
v___y_5872_ = v___y_5994_;
v___y_5873_ = v___y_5982_;
v___y_5874_ = v___y_5995_;
v___y_5875_ = v___y_5996_;
v___y_5876_ = v___y_5997_;
v___y_5877_ = v___y_6012_;
v___y_5878_ = v___y_5999_;
v___y_5879_ = v___y_6001_;
v___y_5880_ = v___y_6000_;
v___y_5881_ = v___y_6002_;
v___y_5882_ = v___y_6003_;
v___y_5883_ = v___y_6004_;
v___y_5884_ = v___y_5984_;
v___y_5885_ = v___y_6005_;
v___y_5886_ = v___y_6006_;
v___y_5887_ = v___y_6007_;
v___y_5888_ = v___y_6008_;
v___y_5889_ = v___y_6009_;
v___y_5890_ = v___y_6010_;
v___y_5891_ = v___x_6020_;
goto v___jp_5852_;
}
else
{
size_t v_sz_6021_; size_t v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
v_sz_6021_ = lean_array_size(v___y_6012_);
v___x_6022_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6012_, 2);
v___x_6023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_6021_, v___x_6022_, v___y_6012_);
v___x_6024_ = lean_array_to_list(v___x_6023_);
v___x_6025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6025_, 0, v___y_6011_);
lean_ctor_set(v___x_6025_, 1, v___x_6024_);
v___y_5853_ = v___y_6012_;
v___y_5854_ = v_returnsEarly_6013_;
v___y_5855_ = v___y_5975_;
v___y_5856_ = v___y_5976_;
v___y_5857_ = v___y_5977_;
v___y_5858_ = v___y_5978_;
v___y_5859_ = v___y_5979_;
v___y_5860_ = v___y_5981_;
v___y_5861_ = v___y_5983_;
v___y_5862_ = v___y_5986_;
v___y_5863_ = v___y_5987_;
v___y_5864_ = v___f_6016_;
v___y_5865_ = v___y_5988_;
v___y_5866_ = v___y_5990_;
v___y_5867_ = v___y_5989_;
v___y_5868_ = v___y_5991_;
v___y_5869_ = v___y_5992_;
v___y_5870_ = v___y_5980_;
v___y_5871_ = v___y_5993_;
v___y_5872_ = v___y_5994_;
v___y_5873_ = v___y_5982_;
v___y_5874_ = v___y_5995_;
v___y_5875_ = v___y_5996_;
v___y_5876_ = v___y_5997_;
v___y_5877_ = v___y_6012_;
v___y_5878_ = v___y_5999_;
v___y_5879_ = v___y_6001_;
v___y_5880_ = v___y_6000_;
v___y_5881_ = v___y_6002_;
v___y_5882_ = v___y_6003_;
v___y_5883_ = v___y_6004_;
v___y_5884_ = v___y_5984_;
v___y_5885_ = v___y_6005_;
v___y_5886_ = v___y_6006_;
v___y_5887_ = v___y_6007_;
v___y_5888_ = v___y_6008_;
v___y_5889_ = v___y_6009_;
v___y_5890_ = v___y_6010_;
v___y_5891_ = v___x_6025_;
goto v___jp_5852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_6227_, lean_object* v_dec_6228_, lean_object* v_a_6229_, lean_object* v_a_6230_, lean_object* v_a_6231_, lean_object* v_a_6232_, lean_object* v_a_6233_, lean_object* v_a_6234_, lean_object* v_a_6235_, lean_object* v_a_6236_){
_start:
{
lean_object* v_res_6237_; 
v_res_6237_ = l_Lean_Elab_Do_elabDoFor(v_stx_6227_, v_dec_6228_, v_a_6229_, v_a_6230_, v_a_6231_, v_a_6232_, v_a_6233_, v_a_6234_, v_a_6235_);
lean_dec(v_a_6235_);
lean_dec_ref(v_a_6234_);
lean_dec(v_a_6233_);
lean_dec_ref(v_a_6232_);
lean_dec(v_a_6231_);
lean_dec_ref(v_a_6230_);
lean_dec_ref(v_a_6229_);
return v_res_6237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v_00_u03b1_6238_, lean_object* v_msg_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_){
_start:
{
lean_object* v___x_6247_; 
v___x_6247_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_6239_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_);
return v___x_6247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v_00_u03b1_6248_, lean_object* v_msg_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_){
_start:
{
lean_object* v_res_6257_; 
v_res_6257_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(v_00_u03b1_6248_, v_msg_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
return v_res_6257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_6258_, lean_object* v_name_6259_, lean_object* v_type_6260_, lean_object* v_k_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_){
_start:
{
lean_object* v___x_6270_; 
v___x_6270_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_6259_, v_type_6260_, v_k_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
return v___x_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_6271_, lean_object* v_name_6272_, lean_object* v_type_6273_, lean_object* v_k_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_){
_start:
{
lean_object* v_res_6283_; 
v_res_6283_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_6271_, v_name_6272_, v_type_6273_, v_k_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_);
lean_dec(v___y_6281_);
lean_dec_ref(v___y_6280_);
lean_dec(v___y_6279_);
lean_dec_ref(v___y_6278_);
lean_dec(v___y_6277_);
lean_dec_ref(v___y_6276_);
lean_dec_ref(v___y_6275_);
return v_res_6283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(lean_object* v_msgData_6284_, lean_object* v_macroStack_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_){
_start:
{
lean_object* v___x_6293_; 
v___x_6293_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_6284_, v_macroStack_6285_, v___y_6290_);
return v___x_6293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___boxed(lean_object* v_msgData_6294_, lean_object* v_macroStack_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_){
_start:
{
lean_object* v_res_6303_; 
v_res_6303_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(v_msgData_6294_, v_macroStack_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_);
lean_dec(v___y_6301_);
lean_dec_ref(v___y_6300_);
lean_dec(v___y_6299_);
lean_dec_ref(v___y_6298_);
lean_dec(v___y_6297_);
lean_dec_ref(v___y_6296_);
return v_res_6303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; 
v___x_6311_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6312_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_6313_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_6314_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_6315_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6311_, v___x_6312_, v___x_6313_, v___x_6314_);
return v___x_6315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_6316_){
_start:
{
lean_object* v_res_6317_; 
v_res_6317_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_6317_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Sum_Basic(uint8_t builtin);
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
res = runtime_initialize_Init_Data_Sum_Basic(builtin);
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
lean_object* runtime_initialize_Std_WP_Gadget_ForIn(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Gadget_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Std_WP_Gadget_ForIn(uint8_t builtin);
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Init_Data_Sum_Basic(uint8_t builtin);
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
res = initialize_Std_WP_Gadget_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Sum_Basic(builtin);
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
