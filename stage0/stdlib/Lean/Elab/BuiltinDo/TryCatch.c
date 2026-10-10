// Lean compiler output
// Module: Lean.Elab.BuiltinDo.TryCatch
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.Do.Control
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_withDeadCodeFromInfo(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkFreshResultType___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_registerMVarErrorHoleInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkPure___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_enterFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadExcept"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 154, 253, 120, 110, 153, 103, 113)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tryCatch"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 154, 253, 120, 110, 153, 103, 113)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(167, 129, 71, 246, 198, 229, 11, 131)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "MonadExceptOf"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(190, 1, 119, 34, 204, 224, 173, 252)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tryCatchThe"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(34, 194, 87, 82, 168, 232, 231, 97)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doCatch"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 196, 191, 146, 79, 230, 20, 8)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "doCatchMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 106, 10, 98, 177, 11, 181, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "catch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__19_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoTry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoTry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "β"};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__2_value),LEAN_SCALAR_PTR_LITERAL(163, 67, 89, 131, 111, 186, 232, 248)}};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoTry___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "MonadFinally"};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__4_value),LEAN_SCALAR_PTR_LITERAL(83, 34, 97, 149, 212, 54, 5, 166)}};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoTry___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Functor"};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__6_value),LEAN_SCALAR_PTR_LITERAL(39, 234, 35, 88, 204, 30, 230, 30)}};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoTry___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tryFinally"};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__8_value),LEAN_SCALAR_PTR_LITERAL(98, 44, 194, 252, 68, 153, 47, 79)}};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_elabDoTry___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Invalid `try`. There must be a `catch` or `finally`."};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoTry___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoTry___closed__11;
static const lean_string_object l_Lean_Elab_Do_elabDoTry___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoTry___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__12_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_elabDoTry___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoTry___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabDoTry"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 47, 35, 48, 51, 128, 204, 231)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___boxed(lean_object* v_00_u03b1_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0(v_00_u03b1_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec_ref(v___y_22_);
return v_res_30_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(lean_object* v___x_31_, uint8_t v___x_32_, lean_object* v_cont_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Elab_Do_elabDoSeq(v___x_31_, v_cont_33_, v___x_32_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
return v___x_42_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_31_ = stack[0].m_obj;
uint8_t v___x_32_ = stack[1].m_num;
lean_object* v_cont_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v___y_38_ = stack[7].m_obj;
lean_object* v___y_39_ = stack[8].m_obj;
lean_object* v___y_40_ = stack[9].m_obj;
lean_object* v_res_43_;
v_res_43_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(v___x_31_, v___x_32_, v_cont_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0___boxed(lean_object* v___x_44_, lean_object* v___x_45_, lean_object* v_cont_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v___x_3917__boxed_55_; lean_object* v_res_56_; 
v___x_3917__boxed_55_ = lean_unbox(v___x_45_);
v_res_56_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(v___x_44_, v___x_3917__boxed_55_, v_cont_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec_ref(v___y_47_);
return v_res_56_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(lean_object* v_lifter_70_, lean_object* v___f_71_, lean_object* v___x_72_, uint8_t v___x_73_, lean_object* v_monadInfo_74_, lean_object* v_body_75_, lean_object* v___y_76_, lean_object* v_eType_x3f_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_catcher_87_; lean_object* v___y_88_; lean_object* v___x_105_; 
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
lean_inc_ref(v_x_78_);
v___x_105_ = lean_infer_type(v_x_78_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_n(v_a_106_, 2);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = l_Lean_Meta_getDecLevel(v_a_106_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_107_, 1);
if (lean_obj_tag(v_eType_x3f_77_) == 0)
{
goto v___jp_109_;
}
else
{
if (v___x_73_ == 0)
{
goto v___jp_109_;
}
else
{
lean_object* v_m_127_; lean_object* v_u_128_; lean_object* v_v_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_m_127_ = lean_ctor_get(v_monadInfo_74_, 0);
lean_inc_ref_n(v_m_127_, 2);
v_u_128_ = lean_ctor_get(v_monadInfo_74_, 1);
lean_inc(v_u_128_);
v_v_129_ = lean_ctor_get(v_monadInfo_74_, 2);
lean_inc(v_v_129_);
lean_dec_ref(v_monadInfo_74_);
v___x_130_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5));
v___x_131_ = lean_box(0);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v_v_129_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v_u_128_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v_a_108_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
lean_inc_ref(v___x_134_);
v___x_135_ = l_Lean_mkConst(v___x_130_, v___x_134_);
lean_inc(v_a_106_);
v___x_136_ = l_Lean_mkAppB(v___x_135_, v_a_106_, v_m_127_);
v___x_137_ = lean_box(0);
v___x_138_ = l_Lean_Elab_Term_mkInstMVar(v___x_136_, v___x_137_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v_liftedDoBlockResultType_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
v_liftedDoBlockResultType_140_ = lean_ctor_get(v_lifter_70_, 5);
v___x_141_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7));
v___x_142_ = l_Lean_mkConst(v___x_141_, v___x_134_);
lean_inc_ref(v_liftedDoBlockResultType_140_);
v___x_143_ = lean_alloc_closure((void*)(l_Lean_mkApp6), 7, 6);
lean_closure_set(v___x_143_, 0, v___x_142_);
lean_closure_set(v___x_143_, 1, v_a_106_);
lean_closure_set(v___x_143_, 2, v_m_127_);
lean_closure_set(v___x_143_, 3, v_a_139_);
lean_closure_set(v___x_143_, 4, v_liftedDoBlockResultType_140_);
lean_closure_set(v___x_143_, 5, v_body_75_);
v_catcher_87_ = v___x_143_;
v___y_88_ = v___y_76_;
goto v___jp_86_;
}
else
{
lean_dec_ref_known(v___x_134_, 2);
lean_dec_ref(v_m_127_);
lean_dec(v_a_106_);
lean_dec_ref(v_x_78_);
lean_dec_ref(v_body_75_);
lean_dec_ref(v___f_71_);
lean_dec_ref(v_lifter_70_);
return v___x_138_;
}
}
}
v___jp_109_:
{
lean_object* v_m_110_; lean_object* v_u_111_; lean_object* v_v_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_m_110_ = lean_ctor_get(v_monadInfo_74_, 0);
lean_inc_ref_n(v_m_110_, 2);
v_u_111_ = lean_ctor_get(v_monadInfo_74_, 1);
lean_inc(v_u_111_);
v_v_112_ = lean_ctor_get(v_monadInfo_74_, 2);
lean_inc(v_v_112_);
lean_dec_ref(v_monadInfo_74_);
v___x_113_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1));
v___x_114_ = lean_box(0);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v_v_112_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v_u_111_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_117_, 0, v_a_108_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
lean_inc_ref(v___x_117_);
v___x_118_ = l_Lean_mkConst(v___x_113_, v___x_117_);
lean_inc(v_a_106_);
v___x_119_ = l_Lean_mkAppB(v___x_118_, v_a_106_, v_m_110_);
v___x_120_ = lean_box(0);
v___x_121_ = l_Lean_Elab_Term_mkInstMVar(v___x_119_, v___x_120_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v_liftedDoBlockResultType_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v___x_121_, 1);
v_liftedDoBlockResultType_123_ = lean_ctor_get(v_lifter_70_, 5);
v___x_124_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3));
v___x_125_ = l_Lean_mkConst(v___x_124_, v___x_117_);
lean_inc_ref(v_liftedDoBlockResultType_123_);
v___x_126_ = lean_alloc_closure((void*)(l_Lean_mkApp6), 7, 6);
lean_closure_set(v___x_126_, 0, v___x_125_);
lean_closure_set(v___x_126_, 1, v_a_106_);
lean_closure_set(v___x_126_, 2, v_m_110_);
lean_closure_set(v___x_126_, 3, v_a_122_);
lean_closure_set(v___x_126_, 4, v_liftedDoBlockResultType_123_);
lean_closure_set(v___x_126_, 5, v_body_75_);
v_catcher_87_ = v___x_126_;
v___y_88_ = v___y_76_;
goto v___jp_86_;
}
else
{
lean_dec_ref_known(v___x_117_, 2);
lean_dec_ref(v_m_110_);
lean_dec(v_a_106_);
lean_dec_ref(v_x_78_);
lean_dec_ref(v_body_75_);
lean_dec_ref(v___f_71_);
lean_dec_ref(v_lifter_70_);
return v___x_121_;
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_a_106_);
lean_dec_ref(v_x_78_);
lean_dec_ref(v_body_75_);
lean_dec_ref(v_monadInfo_74_);
lean_dec_ref(v___f_71_);
lean_dec_ref(v_lifter_70_);
v_a_144_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_107_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_107_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_dec_ref(v_x_78_);
lean_dec_ref(v_body_75_);
lean_dec_ref(v_monadInfo_74_);
lean_dec_ref(v___f_71_);
lean_dec_ref(v_lifter_70_);
return v___x_105_;
}
v___jp_86_:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Elab_Do_EffectForwarder_lift(v_lifter_70_, v___f_71_, v___y_88_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
lean_dec_ref_known(v___x_89_, 1);
v___x_91_ = lean_mk_empty_array_with_capacity(v___x_72_);
v___x_92_ = lean_array_push(v___x_91_, v_x_78_);
v___x_93_ = 0;
v___x_94_ = 1;
v___x_95_ = l_Lean_Meta_mkLambdaFVars(v___x_92_, v_a_90_, v___x_93_, v___x_73_, v___x_93_, v___x_73_, v___x_94_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec_ref(v___x_92_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_104_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_apply_1(v_catcher_87_, v_a_96_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
else
{
lean_dec_ref(v_catcher_87_);
return v___x_95_;
}
}
else
{
lean_dec_ref(v_catcher_87_);
lean_dec_ref(v_x_78_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lifter_70_ = stack[0].m_obj;
lean_object* v___f_71_ = stack[1].m_obj;
lean_object* v___x_72_ = stack[2].m_obj;
uint8_t v___x_73_ = stack[3].m_num;
lean_object* v_monadInfo_74_ = stack[4].m_obj;
lean_object* v_body_75_ = stack[5].m_obj;
lean_object* v___y_76_ = stack[6].m_obj;
lean_object* v_eType_x3f_77_ = stack[7].m_obj;
lean_object* v_x_78_ = stack[8].m_obj;
lean_object* v___y_79_ = stack[9].m_obj;
lean_object* v___y_80_ = stack[10].m_obj;
lean_object* v___y_81_ = stack[11].m_obj;
lean_object* v___y_82_ = stack[12].m_obj;
lean_object* v___y_83_ = stack[13].m_obj;
lean_object* v___y_84_ = stack[14].m_obj;
lean_object* v_res_152_;
v_res_152_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(v_lifter_70_, v___f_71_, v___x_72_, v___x_73_, v_monadInfo_74_, v_body_75_, v___y_76_, v_eType_x3f_77_, v_x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed(lean_object* v_lifter_153_, lean_object* v___f_154_, lean_object* v___x_155_, lean_object* v___x_156_, lean_object* v_monadInfo_157_, lean_object* v_body_158_, lean_object* v___y_159_, lean_object* v_eType_x3f_160_, lean_object* v_x_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
uint8_t v___x_3997__boxed_169_; lean_object* v_res_170_; 
v___x_3997__boxed_169_ = lean_unbox(v___x_156_);
v_res_170_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(v_lifter_153_, v___f_154_, v___x_155_, v___x_3997__boxed_169_, v_monadInfo_157_, v_body_158_, v___y_159_, v_eType_x3f_160_, v_x_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v_eType_x3f_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___x_155_);
return v_res_170_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(lean_object* v_lifter_180_, lean_object* v_body_181_, lean_object* v_catch___182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
lean_inc(v_catch___182_);
v___x_192_ = l_Lean_Syntax_isOfKind(v_catch___182_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
lean_dec(v_catch___182_);
lean_dec_ref(v_body_181_);
lean_dec_ref(v_lifter_180_);
v___x_193_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_193_;
}
else
{
lean_object* v_monadInfo_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v_eType_x3f_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_monadInfo_194_ = lean_ctor_get(v_a_183_, 0);
v___x_195_ = lean_unsigned_to_nat(1u);
v___x_196_ = l_Lean_Syntax_getArg(v_catch___182_, v___x_195_);
v___x_226_ = lean_unsigned_to_nat(2u);
v___x_227_ = l_Lean_Syntax_getArg(v_catch___182_, v___x_226_);
v___x_228_ = l_Lean_Syntax_isNone(v___x_227_);
if (v___x_228_ == 0)
{
uint8_t v___x_229_; 
lean_inc(v___x_227_);
v___x_229_ = l_Lean_Syntax_matchesNull(v___x_227_, v___x_226_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
lean_dec(v___x_227_);
lean_dec(v___x_196_);
lean_dec(v_catch___182_);
lean_dec_ref(v_body_181_);
lean_dec_ref(v_lifter_180_);
v___x_230_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_230_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = l_Lean_Syntax_getArg(v___x_227_, v___x_195_);
lean_dec(v___x_227_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
v_eType_x3f_209_ = v___x_232_;
v___y_210_ = v_a_183_;
v___y_211_ = v_a_184_;
v___y_212_ = v_a_185_;
v___y_213_ = v_a_186_;
v___y_214_ = v_a_187_;
v___y_215_ = v_a_188_;
v___y_216_ = v_a_189_;
goto v___jp_208_;
}
}
else
{
lean_object* v___x_233_; 
lean_dec(v___x_227_);
v___x_233_ = lean_box(0);
v_eType_x3f_209_ = v___x_233_;
v___y_210_ = v_a_183_;
v___y_211_ = v_a_184_;
v___y_212_ = v_a_185_;
v___y_213_ = v_a_186_;
v___y_214_ = v_a_187_;
v___y_215_ = v_a_188_;
v___y_216_ = v_a_189_;
goto v___jp_208_;
}
v___jp_197_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = l_Lean_Elab_Term_mkExplicitBinder(v___x_196_, v___y_205_);
v___x_207_ = l_Lean_Elab_Term_elabBinder___redArg(v___x_206_, v___y_200_, v___y_204_, v___y_203_, v___y_198_, v___y_201_, v___y_199_, v___y_202_);
return v___x_207_;
}
v___jp_208_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___f_222_; 
v___x_217_ = lean_unsigned_to_nat(4u);
v___x_218_ = l_Lean_Syntax_getArg(v_catch___182_, v___x_217_);
lean_dec(v_catch___182_);
v___x_219_ = lean_box(v___x_192_);
v___f_220_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0___boxed), 11, 2);
lean_closure_set(v___f_220_, 0, v___x_218_);
lean_closure_set(v___f_220_, 1, v___x_219_);
v___x_221_ = lean_box(v___x_192_);
lean_inc(v_eType_x3f_209_);
lean_inc_ref(v___y_210_);
lean_inc_ref(v_monadInfo_194_);
v___f_222_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed), 16, 8);
lean_closure_set(v___f_222_, 0, v_lifter_180_);
lean_closure_set(v___f_222_, 1, v___f_220_);
lean_closure_set(v___f_222_, 2, v___x_195_);
lean_closure_set(v___f_222_, 3, v___x_221_);
lean_closure_set(v___f_222_, 4, v_monadInfo_194_);
lean_closure_set(v___f_222_, 5, v_body_181_);
lean_closure_set(v___f_222_, 6, v___y_210_);
lean_closure_set(v___f_222_, 7, v_eType_x3f_209_);
if (lean_obj_tag(v_eType_x3f_209_) == 0)
{
uint8_t v___x_223_; lean_object* v___x_224_; 
v___x_223_ = 0;
v___x_224_ = l_Lean_mkHole(v___x_196_, v___x_223_);
v___y_198_ = v___y_213_;
v___y_199_ = v___y_215_;
v___y_200_ = v___f_222_;
v___y_201_ = v___y_214_;
v___y_202_ = v___y_216_;
v___y_203_ = v___y_212_;
v___y_204_ = v___y_211_;
v___y_205_ = v___x_224_;
goto v___jp_197_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v_eType_x3f_209_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v_eType_x3f_209_, 1);
v___y_198_ = v___y_213_;
v___y_199_ = v___y_215_;
v___y_200_ = v___f_222_;
v___y_201_ = v___y_214_;
v___y_202_ = v___y_216_;
v___y_203_ = v___y_212_;
v___y_204_ = v___y_211_;
v___y_205_ = v_val_225_;
goto v___jp_197_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_lifter_180_ = stack[0].m_obj;
lean_object* v_body_181_ = stack[1].m_obj;
lean_object* v_catch___182_ = stack[2].m_obj;
lean_object* v_a_183_ = stack[3].m_obj;
lean_object* v_a_184_ = stack[4].m_obj;
lean_object* v_a_185_ = stack[5].m_obj;
lean_object* v_a_186_ = stack[6].m_obj;
lean_object* v_a_187_ = stack[7].m_obj;
lean_object* v_a_188_ = stack[8].m_obj;
lean_object* v_a_189_ = stack[9].m_obj;
lean_object* v_res_234_;
v_res_234_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_lifter_180_, v_body_181_, v_catch___182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___boxed(lean_object* v_lifter_235_, lean_object* v_body_236_, lean_object* v_catch___237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_lifter_235_, v_body_236_, v_catch___237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec_ref(v_a_238_);
return v_res_246_;
}
}
lean_object* l_Lean_Elab_Do_elabDoTry___lam__0(lean_object* v_trySeq_247_, uint8_t v___x_248_, lean_object* v_cont_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Elab_Do_elabDoSeq(v_trySeq_247_, v_cont_249_, v___x_248_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
return v___x_258_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoTry___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_trySeq_247_ = stack[0].m_obj;
uint8_t v___x_248_ = stack[1].m_num;
lean_object* v_cont_249_ = stack[2].m_obj;
lean_object* v___y_250_ = stack[3].m_obj;
lean_object* v___y_251_ = stack[4].m_obj;
lean_object* v___y_252_ = stack[5].m_obj;
lean_object* v___y_253_ = stack[6].m_obj;
lean_object* v___y_254_ = stack[7].m_obj;
lean_object* v___y_255_ = stack[8].m_obj;
lean_object* v___y_256_ = stack[9].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Lean_Elab_Do_elabDoTry___lam__0(v_trySeq_247_, v___x_248_, v_cont_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___lam__0___boxed(lean_object* v_trySeq_260_, lean_object* v___x_261_, lean_object* v_cont_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
uint8_t v___x_14197__boxed_271_; lean_object* v_res_272_; 
v___x_14197__boxed_271_ = lean_unbox(v___x_261_);
v_res_272_ = l_Lean_Elab_Do_elabDoTry___lam__0(v_trySeq_260_, v___x_14197__boxed_271_, v_cont_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_272_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(lean_object* v_as_276_, size_t v_i_277_, size_t v_stop_278_, lean_object* v_b_279_){
_start:
{
lean_object* v___y_281_; uint8_t v___x_285_; 
v___x_285_ = lean_usize_dec_eq(v_i_277_, v_stop_278_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_array_uget_borrowed(v_as_276_, v_i_277_);
v___x_287_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
lean_inc(v___x_286_);
v___x_288_ = l_Lean_Syntax_isOfKind(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
v___y_281_ = v_b_279_;
goto v___jp_280_;
}
else
{
lean_object* v___x_289_; lean_object* v_x_290_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v_x_290_ = l_Lean_Syntax_getArg(v___x_286_, v___x_289_);
v___x_293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__1));
lean_inc(v_x_290_);
v___x_294_ = l_Lean_Syntax_isOfKind(v_x_290_, v___x_293_);
if (v___x_294_ == 0)
{
lean_dec(v_x_290_);
v___y_281_ = v_b_279_;
goto v___jp_280_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = lean_unsigned_to_nat(2u);
v___x_296_ = l_Lean_Syntax_getArg(v___x_286_, v___x_295_);
v___x_297_ = l_Lean_Syntax_isNone(v___x_296_);
if (v___x_297_ == 0)
{
uint8_t v___x_298_; 
v___x_298_ = l_Lean_Syntax_matchesNull(v___x_296_, v___x_295_);
if (v___x_298_ == 0)
{
lean_dec(v_x_290_);
v___y_281_ = v_b_279_;
goto v___jp_280_;
}
else
{
goto v___jp_291_;
}
}
else
{
lean_dec(v___x_296_);
goto v___jp_291_;
}
}
v___jp_291_:
{
lean_object* v___x_292_; 
v___x_292_ = lean_array_push(v_b_279_, v_x_290_);
v___y_281_ = v___x_292_;
goto v___jp_280_;
}
}
}
else
{
return v_b_279_;
}
v___jp_280_:
{
size_t v___x_282_; size_t v___x_283_; 
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_add(v_i_277_, v___x_282_);
v_i_277_ = v___x_283_;
v_b_279_ = v___y_281_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_276_ = stack[0].m_obj;
size_t v_i_277_ = stack[1].m_num;
size_t v_stop_278_ = stack[2].m_num;
lean_object* v_b_279_ = stack[3].m_obj;
lean_object* v_res_299_;
v_res_299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(v_as_276_, v_i_277_, v_stop_278_, v_b_279_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___boxed(lean_object* v_as_300_, lean_object* v_i_301_, lean_object* v_stop_302_, lean_object* v_b_303_){
_start:
{
size_t v_i_boxed_304_; size_t v_stop_boxed_305_; lean_object* v_res_306_; 
v_i_boxed_304_ = lean_unbox_usize(v_i_301_);
lean_dec(v_i_301_);
v_stop_boxed_305_ = lean_unbox_usize(v_stop_302_);
lean_dec(v_stop_302_);
v_res_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(v_as_300_, v_i_boxed_304_, v_stop_boxed_305_, v_b_303_);
lean_dec_ref(v_as_300_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2(lean_object* v_as_309_, lean_object* v_start_310_, lean_object* v_stop_311_){
_start:
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0));
v___x_313_ = lean_nat_dec_lt(v_start_310_, v_stop_311_);
if (v___x_313_ == 0)
{
return v___x_312_;
}
else
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_array_get_size(v_as_309_);
v___x_315_ = lean_nat_dec_le(v_stop_311_, v___x_314_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; 
v___x_316_ = lean_nat_dec_lt(v_start_310_, v___x_314_);
if (v___x_316_ == 0)
{
return v___x_312_;
}
else
{
size_t v___x_317_; size_t v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_usize_of_nat(v_start_310_);
v___x_318_ = lean_usize_of_nat(v___x_314_);
v___x_319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(v_as_309_, v___x_317_, v___x_318_, v___x_312_);
return v___x_319_;
}
}
else
{
size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_usize_of_nat(v_start_310_);
v___x_321_ = lean_usize_of_nat(v_stop_311_);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(v_as_309_, v___x_320_, v___x_321_, v___x_312_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2___boxed(lean_object* v_as_323_, lean_object* v_start_324_, lean_object* v_stop_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2(v_as_323_, v_start_324_, v_stop_325_);
lean_dec(v_stop_325_);
lean_dec(v_start_324_);
lean_dec_ref(v_as_323_);
return v_res_326_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(lean_object* v_msgData_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v_env_334_; uint8_t v___x_335_; lean_object* v_env_336_; lean_object* v___x_337_; lean_object* v_toCold_338_; lean_object* v_mctx_339_; lean_object* v_lctx_340_; lean_object* v_options_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_333_ = lean_st_ref_get(v___y_331_);
v_env_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc_ref(v_env_334_);
lean_dec(v___x_333_);
v___x_335_ = 0;
v_env_336_ = l_Lean_Environment_setRecordingDeps(v_env_334_, v___x_335_);
v___x_337_ = lean_st_ref_get(v___y_329_);
v_toCold_338_ = lean_ctor_get(v___y_330_, 0);
v_mctx_339_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_mctx_339_);
lean_dec(v___x_337_);
v_lctx_340_ = lean_ctor_get(v___y_328_, 2);
v_options_341_ = lean_ctor_get(v_toCold_338_, 2);
lean_inc_ref(v_options_341_);
lean_inc_ref(v_lctx_340_);
v___x_342_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_342_, 0, v_env_336_);
lean_ctor_set(v___x_342_, 1, v_mctx_339_);
lean_ctor_set(v___x_342_, 2, v_lctx_340_);
lean_ctor_set(v___x_342_, 3, v_options_341_);
v___x_343_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v_msgData_327_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_327_ = stack[0].m_obj;
lean_object* v___y_328_ = stack[1].m_obj;
lean_object* v___y_329_ = stack[2].m_obj;
lean_object* v___y_330_ = stack[3].m_obj;
lean_object* v___y_331_ = stack[4].m_obj;
lean_object* v_res_345_;
v_res_345_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msgData_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4___boxed(lean_object* v_msgData_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msgData_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_352_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_ref_359_; lean_object* v___x_360_; lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_369_; 
v_ref_359_ = lean_ctor_get(v___y_356_, 2);
v___x_360_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_369_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_inc(v_ref_359_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_ref_359_);
lean_ctor_set(v___x_365_, 1, v_a_361_);
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 1);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_353_ = stack[0].m_obj;
lean_object* v___y_354_ = stack[1].m_obj;
lean_object* v___y_355_ = stack[2].m_obj;
lean_object* v___y_356_ = stack[3].m_obj;
lean_object* v___y_357_ = stack[4].m_obj;
lean_object* v_res_370_;
v_res_370_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg___boxed(lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v_msg_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_377_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__3));
v___x_387_ = l_String_toRawSubstring_x27(v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8(void){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Array_mkArray0___redArg();
return v___x_393_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(lean_object* v_a_421_, lean_object* v_as_422_, size_t v_i_423_, size_t v_stop_424_, lean_object* v_b_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___y_435_; uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_eq(v_i_423_, v_stop_424_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1));
v___x_442_ = lean_array_uget_borrowed(v_as_422_, v_i_423_);
lean_inc(v___x_442_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_442_, v___x_441_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_inc(v___x_442_);
lean_inc_ref(v_a_421_);
v___x_444_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_a_421_, v_b_425_, v___x_442_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
v___y_435_ = v___x_444_;
goto v___jp_434_;
}
else
{
lean_object* v_toCold_445_; lean_object* v_ref_446_; lean_object* v_quotContext_447_; lean_object* v_currMacroScope_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v_toCold_445_ = lean_ctor_get(v___y_431_, 0);
v_ref_446_ = lean_ctor_get(v___y_431_, 2);
v_quotContext_447_ = lean_ctor_get(v_toCold_445_, 8);
v_currMacroScope_448_ = lean_ctor_get(v_toCold_445_, 9);
v___x_449_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = l_Lean_Syntax_getArg(v___x_442_, v___x_450_);
v___x_452_ = l_Lean_SourceInfo_fromRef(v_ref_446_, v___x_440_);
v___x_453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__2));
lean_inc_n(v___x_452_, 12);
v___x_454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4);
v___x_456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__5));
lean_inc(v_currMacroScope_448_);
lean_inc(v_quotContext_447_);
v___x_457_ = l_Lean_addMacroScope(v_quotContext_447_, v___x_456_, v_currMacroScope_448_);
v___x_458_ = lean_box(0);
v___x_459_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_459_, 0, v___x_452_);
lean_ctor_set(v___x_459_, 1, v___x_455_);
lean_ctor_set(v___x_459_, 2, v___x_457_);
lean_ctor_set(v___x_459_, 3, v___x_458_);
v___x_460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__7));
v___x_461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8);
v___x_462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_462_, 0, v___x_452_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
v___x_463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__9));
v___x_464_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_452_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11));
v___x_466_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13));
v___x_467_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15));
v___x_468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__16));
v___x_469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_452_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18));
lean_inc_ref(v___x_459_);
lean_inc_ref_n(v___x_462_, 5);
v___x_471_ = l_Lean_Syntax_node2(v___x_452_, v___x_470_, v___x_462_, v___x_459_);
v___x_472_ = l_Lean_Syntax_node1(v___x_452_, v___x_460_, v___x_471_);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__19));
v___x_474_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_452_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Lean_Syntax_node7(v___x_452_, v___x_467_, v___x_469_, v___x_462_, v___x_462_, v___x_462_, v___x_472_, v___x_474_, v___x_451_);
v___x_476_ = l_Lean_Syntax_node2(v___x_452_, v___x_466_, v___x_475_, v___x_462_);
v___x_477_ = l_Lean_Syntax_node1(v___x_452_, v___x_460_, v___x_476_);
v___x_478_ = l_Lean_Syntax_node1(v___x_452_, v___x_465_, v___x_477_);
v___x_479_ = l_Lean_Syntax_node5(v___x_452_, v___x_449_, v___x_454_, v___x_459_, v___x_462_, v___x_464_, v___x_478_);
lean_inc_ref(v_a_421_);
v___x_480_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_a_421_, v_b_425_, v___x_479_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
v___y_435_ = v___x_480_;
goto v___jp_434_;
}
}
else
{
lean_object* v___x_481_; 
lean_dec_ref(v_a_421_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v_b_425_);
return v___x_481_;
}
v___jp_434_:
{
if (lean_obj_tag(v___y_435_) == 0)
{
lean_object* v_a_436_; size_t v___x_437_; size_t v___x_438_; 
v_a_436_ = lean_ctor_get(v___y_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___y_435_, 1);
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_add(v_i_423_, v___x_437_);
v_i_423_ = v___x_438_;
v_b_425_ = v_a_436_;
goto _start;
}
else
{
lean_dec_ref(v_a_421_);
return v___y_435_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_421_ = stack[0].m_obj;
lean_object* v_as_422_ = stack[1].m_obj;
size_t v_i_423_ = stack[2].m_num;
size_t v_stop_424_ = stack[3].m_num;
lean_object* v_b_425_ = stack[4].m_obj;
lean_object* v___y_426_ = stack[5].m_obj;
lean_object* v___y_427_ = stack[6].m_obj;
lean_object* v___y_428_ = stack[7].m_obj;
lean_object* v___y_429_ = stack[8].m_obj;
lean_object* v___y_430_ = stack[9].m_obj;
lean_object* v___y_431_ = stack[10].m_obj;
lean_object* v___y_432_ = stack[11].m_obj;
lean_object* v_res_482_;
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(v_a_421_, v_as_422_, v_i_423_, v_stop_424_, v_b_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___boxed(lean_object* v_a_483_, lean_object* v_as_484_, lean_object* v_i_485_, lean_object* v_stop_486_, lean_object* v_b_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
size_t v_i_boxed_496_; size_t v_stop_boxed_497_; lean_object* v_res_498_; 
v_i_boxed_496_ = lean_unbox_usize(v_i_485_);
lean_dec(v_i_485_);
v_stop_boxed_497_ = lean_unbox_usize(v_stop_486_);
lean_dec(v_stop_486_);
v_res_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(v_a_483_, v_as_484_, v_i_boxed_496_, v_stop_boxed_497_, v_b_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec_ref(v_as_484_);
return v_res_498_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(size_t v_sz_499_, size_t v_i_500_, lean_object* v_bs_501_){
_start:
{
uint8_t v___x_502_; 
v___x_502_ = lean_usize_dec_lt(v_i_500_, v_sz_499_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v_bs_501_);
return v___x_503_;
}
else
{
lean_object* v_v_504_; lean_object* v___x_505_; lean_object* v_bs_x27_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v_v_504_ = lean_array_uget(v_bs_501_, v_i_500_);
v___x_505_ = lean_unsigned_to_nat(0u);
v_bs_x27_506_ = lean_array_uset(v_bs_501_, v_i_500_, v___x_505_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_500_, v___x_507_);
v___x_509_ = lean_array_uset(v_bs_x27_506_, v_i_500_, v_v_504_);
v_i_500_ = v___x_508_;
v_bs_501_ = v___x_509_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_499_ = stack[0].m_num;
size_t v_i_500_ = stack[1].m_num;
lean_object* v_bs_501_ = stack[2].m_obj;
lean_object* v_res_511_;
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_499_, v_i_500_, v_bs_501_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0___boxed(lean_object* v_sz_512_, lean_object* v_i_513_, lean_object* v_bs_514_){
_start:
{
size_t v_sz_boxed_515_; size_t v_i_boxed_516_; lean_object* v_res_517_; 
v_sz_boxed_515_ = lean_unbox_usize(v_sz_512_);
lean_dec(v_sz_512_);
v_i_boxed_516_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_boxed_515_, v_i_boxed_516_, v_bs_514_);
return v_res_517_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoTry___closed__11(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__10));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
lean_object* l_Lean_Elab_Do_elabDoTry(lean_object* v_stx_545_, lean_object* v_dec_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v_body_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; 
v___x_578_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__1));
lean_inc(v_stx_545_);
v___x_579_ = l_Lean_Syntax_isOfKind(v_stx_545_, v___x_578_);
if (v___x_579_ == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v_dec_546_);
lean_dec(v_stx_545_);
v___x_645_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; size_t v_sz_649_; size_t v___x_650_; lean_object* v___x_651_; 
v___x_646_ = lean_unsigned_to_nat(2u);
v___x_647_ = l_Lean_Syntax_getArg(v_stx_545_, v___x_646_);
v___x_648_ = l_Lean_Syntax_getArgs(v___x_647_);
lean_dec(v___x_647_);
v_sz_649_ = lean_array_size(v___x_648_);
v___x_650_ = ((size_t)0ULL);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_649_, v___x_650_, v___x_648_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v___x_652_; 
lean_dec_ref(v_dec_546_);
lean_dec(v_stx_545_);
v___x_652_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_652_;
}
else
{
lean_object* v_val_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_747_; 
v_val_653_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_747_ == 0)
{
v___x_655_ = v___x_651_;
v_isShared_656_ = v_isSharedCheck_747_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_val_653_);
lean_dec(v___x_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_747_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___x_698_; lean_object* v_trySeq_699_; lean_object* v___x_700_; lean_object* v___f_701_; lean_object* v_finSeq_x3f_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_unsigned_to_nat(1u);
v_trySeq_699_ = l_Lean_Syntax_getArg(v_stx_545_, v___x_698_);
v___x_700_ = lean_box(v___x_579_);
v___f_701_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoTry___lam__0___boxed), 11, 2);
lean_closure_set(v___f_701_, 0, v_trySeq_699_);
lean_closure_set(v___f_701_, 1, v___x_700_);
v___x_733_ = lean_unsigned_to_nat(3u);
v___x_734_ = l_Lean_Syntax_getArg(v_stx_545_, v___x_733_);
v___x_735_ = l_Lean_Syntax_isNone(v___x_734_);
if (v___x_735_ == 0)
{
uint8_t v___x_736_; 
lean_inc(v___x_734_);
v___x_736_ = l_Lean_Syntax_matchesNull(v___x_734_, v___x_698_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec(v___x_734_);
lean_dec_ref(v___f_701_);
lean_del_object(v___x_655_);
lean_dec(v_val_653_);
lean_dec_ref(v_dec_546_);
lean_dec(v_stx_545_);
v___x_737_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = l_Lean_Syntax_getArg(v___x_734_, v___x_657_);
lean_dec(v___x_734_);
v___x_739_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__13));
lean_inc(v___x_738_);
v___x_740_ = l_Lean_Syntax_isOfKind(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v___x_738_);
lean_dec_ref(v___f_701_);
lean_del_object(v___x_655_);
lean_dec(v_val_653_);
lean_dec_ref(v_dec_546_);
lean_dec(v_stx_545_);
v___x_741_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_741_;
}
else
{
lean_object* v_finSeq_x3f_742_; lean_object* v___x_744_; 
v_finSeq_x3f_742_ = l_Lean_Syntax_getArg(v___x_738_, v___x_698_);
lean_dec(v___x_738_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_finSeq_x3f_742_);
v___x_744_ = v___x_655_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_finSeq_x3f_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
v_finSeq_x3f_703_ = v___x_744_;
v___y_704_ = v_a_547_;
v___y_705_ = v_a_548_;
v___y_706_ = v_a_549_;
v___y_707_ = v_a_550_;
v___y_708_ = v_a_551_;
v___y_709_ = v_a_552_;
v___y_710_ = v_a_553_;
goto v___jp_702_;
}
}
}
}
else
{
lean_object* v___x_746_; 
lean_dec(v___x_734_);
lean_del_object(v___x_655_);
v___x_746_ = lean_box(0);
v_finSeq_x3f_703_ = v___x_746_;
v___y_704_ = v_a_547_;
v___y_705_ = v_a_548_;
v___y_706_ = v_a_549_;
v___y_707_ = v_a_550_;
v___y_708_ = v_a_551_;
v___y_709_ = v_a_552_;
v___y_710_ = v_a_553_;
goto v___jp_702_;
}
v___jp_658_:
{
lean_object* v_monadInfo_669_; lean_object* v___x_670_; 
v_monadInfo_669_ = lean_ctor_get(v___y_662_, 0);
v___x_670_ = l_Lean_Elab_Do_inferControlInfoElem(v_stx_545_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_a_671_, v_dec_546_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_n(v_a_673_, 2);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_Elab_Do_EffectForwarder_lift(v_a_673_, v___y_659_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; uint8_t v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v___x_676_ = lean_nat_dec_lt(v___x_657_, v___y_660_);
if (v___x_676_ == 0)
{
lean_dec(v___y_660_);
lean_dec(v_val_653_);
v___y_581_ = v_a_671_;
v___y_582_ = v___y_662_;
v___y_583_ = v___y_663_;
v___y_584_ = v_a_673_;
v___y_585_ = v_monadInfo_669_;
v___y_586_ = v___y_668_;
v___y_587_ = v___y_667_;
v___y_588_ = v___y_661_;
v___y_589_ = v___y_666_;
v___y_590_ = v___y_664_;
v___y_591_ = v___y_665_;
v___y_592_ = v___x_674_;
goto v___jp_580_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = lean_nat_dec_le(v___y_660_, v___y_660_);
if (v___x_677_ == 0)
{
if (v___x_676_ == 0)
{
lean_dec(v___y_660_);
lean_dec(v_val_653_);
v___y_581_ = v_a_671_;
v___y_582_ = v___y_662_;
v___y_583_ = v___y_663_;
v___y_584_ = v_a_673_;
v___y_585_ = v_monadInfo_669_;
v___y_586_ = v___y_668_;
v___y_587_ = v___y_667_;
v___y_588_ = v___y_661_;
v___y_589_ = v___y_666_;
v___y_590_ = v___y_664_;
v___y_591_ = v___y_665_;
v___y_592_ = v___x_674_;
goto v___jp_580_;
}
else
{
size_t v___x_678_; lean_object* v___x_679_; 
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_678_ = lean_usize_of_nat(v___y_660_);
lean_dec(v___y_660_);
lean_inc(v_a_673_);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(v_a_673_, v_val_653_, v___x_650_, v___x_678_, v_a_675_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v_val_653_);
v___y_581_ = v_a_671_;
v___y_582_ = v___y_662_;
v___y_583_ = v___y_663_;
v___y_584_ = v_a_673_;
v___y_585_ = v_monadInfo_669_;
v___y_586_ = v___y_668_;
v___y_587_ = v___y_667_;
v___y_588_ = v___y_661_;
v___y_589_ = v___y_666_;
v___y_590_ = v___y_664_;
v___y_591_ = v___y_665_;
v___y_592_ = v___x_679_;
goto v___jp_580_;
}
}
else
{
size_t v___x_680_; lean_object* v___x_681_; 
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_680_ = lean_usize_of_nat(v___y_660_);
lean_dec(v___y_660_);
lean_inc(v_a_673_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(v_a_673_, v_val_653_, v___x_650_, v___x_680_, v_a_675_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v_val_653_);
v___y_581_ = v_a_671_;
v___y_582_ = v___y_662_;
v___y_583_ = v___y_663_;
v___y_584_ = v_a_673_;
v___y_585_ = v_monadInfo_669_;
v___y_586_ = v___y_668_;
v___y_587_ = v___y_667_;
v___y_588_ = v___y_661_;
v___y_589_ = v___y_666_;
v___y_590_ = v___y_664_;
v___y_591_ = v___y_665_;
v___y_592_ = v___x_681_;
goto v___jp_580_;
}
}
}
else
{
lean_dec(v_a_673_);
lean_dec(v_a_671_);
lean_dec(v___y_661_);
lean_dec(v___y_660_);
lean_dec(v_val_653_);
return v___x_674_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_a_671_);
lean_dec(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_val_653_);
v_a_682_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_672_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_672_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v_val_653_);
lean_dec_ref(v_dec_546_);
v_a_690_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_670_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_670_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
v___jp_702_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_array_get_size(v_val_653_);
v___x_712_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2(v_val_653_, v___x_657_, v___x_711_);
v___x_713_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_712_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
lean_dec_ref(v___x_712_);
if (lean_obj_tag(v___x_713_) == 0)
{
uint8_t v___x_714_; 
lean_dec_ref_known(v___x_713_, 1);
v___x_714_ = lean_nat_dec_eq(v___x_711_, v___x_657_);
if (v___x_714_ == 0)
{
v___y_659_ = v___f_701_;
v___y_660_ = v___x_711_;
v___y_661_ = v_finSeq_x3f_703_;
v___y_662_ = v___y_704_;
v___y_663_ = v___y_705_;
v___y_664_ = v___y_706_;
v___y_665_ = v___y_707_;
v___y_666_ = v___y_708_;
v___y_667_ = v___y_709_;
v___y_668_ = v___y_710_;
goto v___jp_658_;
}
else
{
if (lean_obj_tag(v_finSeq_x3f_703_) == 0)
{
if (v___x_579_ == 0)
{
v___y_659_ = v___f_701_;
v___y_660_ = v___x_711_;
v___y_661_ = v_finSeq_x3f_703_;
v___y_662_ = v___y_704_;
v___y_663_ = v___y_705_;
v___y_664_ = v___y_706_;
v___y_665_ = v___y_707_;
v___y_666_ = v___y_708_;
v___y_667_ = v___y_709_;
v___y_668_ = v___y_710_;
goto v___jp_658_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v___f_701_);
lean_dec(v_val_653_);
lean_dec_ref(v_dec_546_);
lean_dec(v_stx_545_);
v___x_715_ = lean_obj_once(&l_Lean_Elab_Do_elabDoTry___closed__11, &l_Lean_Elab_Do_elabDoTry___closed__11_once, _init_l_Lean_Elab_Do_elabDoTry___closed__11);
v___x_716_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v___x_715_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
v___y_659_ = v___f_701_;
v___y_660_ = v___x_711_;
v___y_661_ = v_finSeq_x3f_703_;
v___y_662_ = v___y_704_;
v___y_663_ = v___y_705_;
v___y_664_ = v___y_706_;
v___y_665_ = v___y_707_;
v___y_666_ = v___y_708_;
v___y_667_ = v___y_709_;
v___y_668_ = v___y_710_;
goto v___jp_658_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_finSeq_x3f_703_);
lean_dec_ref(v___f_701_);
lean_dec(v_val_653_);
lean_dec_ref(v_dec_546_);
lean_dec(v_stx_545_);
v_a_725_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_713_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_713_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
v___jp_555_:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v___y_557_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v___x_568_ = l_Lean_Elab_Do_DoElemCont_withDeadCodeFromInfo(v_a_567_, v___y_556_);
lean_dec_ref(v___y_556_);
v___x_569_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v___x_568_, v_body_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_569_;
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec_ref(v_body_558_);
lean_dec_ref(v___y_556_);
v_a_570_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_566_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_566_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
v___jp_580_:
{
if (lean_obj_tag(v___y_592_) == 0)
{
if (lean_obj_tag(v___y_588_) == 0)
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v___y_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___y_592_, 1);
v___y_556_ = v___y_581_;
v___y_557_ = v___y_584_;
v_body_558_ = v_a_593_;
v___y_559_ = v___y_582_;
v___y_560_ = v___y_583_;
v___y_561_ = v___y_590_;
v___y_562_ = v___y_591_;
v___y_563_ = v___y_589_;
v___y_564_ = v___y_587_;
v___y_565_ = v___y_586_;
goto v___jp_555_;
}
else
{
lean_object* v_a_594_; lean_object* v_val_595_; lean_object* v___x_596_; uint8_t v___x_597_; lean_object* v___x_598_; 
v_a_594_ = lean_ctor_get(v___y_592_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___y_592_, 1);
v_val_595_ = lean_ctor_get(v___y_588_, 0);
lean_inc(v_val_595_);
lean_dec_ref_known(v___y_588_, 1);
v___x_596_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__3));
v___x_597_ = 0;
v___x_598_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_596_, v___x_597_, v___y_582_, v___y_591_, v___y_589_, v___y_587_, v___y_586_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = l_Lean_Expr_mvarId_x21(v_a_599_);
lean_inc(v_val_595_);
v___x_601_ = l_Lean_Elab_Term_registerMVarErrorHoleInfo___redArg(v___x_600_, v_val_595_, v___y_590_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_602_; 
lean_dec_ref_known(v___x_601_, 1);
lean_inc(v_a_599_);
v___x_602_ = l_Lean_Elab_Do_DoElemCont_mkPure___redArg(v_a_599_, v___y_587_, v___y_586_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = lean_box(v___x_579_);
v___x_605_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_605_, 0, v_val_595_);
lean_closure_set(v___x_605_, 1, v_a_603_);
lean_closure_set(v___x_605_, 2, v___x_604_);
lean_inc(v_a_599_);
v___x_606_ = l_Lean_Elab_Do_enterFinally(v_a_599_, v___x_605_, v___y_582_, v___y_583_, v___y_590_, v___y_591_, v___y_589_, v___y_587_, v___y_586_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v_m_608_; lean_object* v_u_609_; lean_object* v_v_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v_m_608_ = lean_ctor_get(v___y_585_, 0);
v_u_609_ = lean_ctor_get(v___y_585_, 1);
v_v_610_ = lean_ctor_get(v___y_585_, 2);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__5));
v___x_612_ = lean_box(0);
lean_inc(v_v_610_);
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v_v_610_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_inc(v_u_609_);
v___x_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_614_, 0, v_u_609_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
lean_inc_ref(v___x_614_);
v___x_615_ = l_Lean_mkConst(v___x_611_, v___x_614_);
lean_inc_ref(v_m_608_);
v___x_616_ = l_Lean_Expr_app___override(v___x_615_, v_m_608_);
v___x_617_ = lean_box(0);
v___x_618_ = l_Lean_Elab_Term_mkInstMVar(v___x_616_, v___x_617_, v___y_583_, v___y_590_, v___y_591_, v___y_589_, v___y_587_, v___y_586_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__7));
lean_inc_ref(v___x_614_);
v___x_621_ = l_Lean_mkConst(v___x_620_, v___x_614_);
lean_inc_ref(v_m_608_);
v___x_622_ = l_Lean_Expr_app___override(v___x_621_, v_m_608_);
v___x_623_ = l_Lean_Elab_Term_mkInstMVar(v___x_622_, v___x_617_, v___y_583_, v___y_590_, v___y_591_, v___y_589_, v___y_587_, v___y_586_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_liftedDoBlockResultType_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v_liftedDoBlockResultType_625_ = lean_ctor_get(v___y_584_, 5);
v___x_626_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__9));
v___x_627_ = l_Lean_mkConst(v___x_626_, v___x_614_);
lean_inc_ref(v_liftedDoBlockResultType_625_);
lean_inc_ref(v_m_608_);
v___x_628_ = l_Lean_mkApp7(v___x_627_, v_m_608_, v_liftedDoBlockResultType_625_, v_a_599_, v_a_619_, v_a_624_, v_a_594_, v_a_607_);
v___y_556_ = v___y_581_;
v___y_557_ = v___y_584_;
v_body_558_ = v___x_628_;
v___y_559_ = v___y_582_;
v___y_560_ = v___y_583_;
v___y_561_ = v___y_590_;
v___y_562_ = v___y_591_;
v___y_563_ = v___y_589_;
v___y_564_ = v___y_587_;
v___y_565_ = v___y_586_;
goto v___jp_555_;
}
else
{
lean_dec(v_a_619_);
lean_dec_ref_known(v___x_614_, 2);
lean_dec(v_a_607_);
lean_dec(v_a_599_);
lean_dec(v_a_594_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_581_);
return v___x_623_;
}
}
else
{
lean_dec_ref_known(v___x_614_, 2);
lean_dec(v_a_607_);
lean_dec(v_a_599_);
lean_dec(v_a_594_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_581_);
return v___x_618_;
}
}
else
{
lean_dec(v_a_599_);
lean_dec(v_a_594_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_581_);
return v___x_606_;
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_a_599_);
lean_dec(v_val_595_);
lean_dec(v_a_594_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_581_);
v_a_629_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_602_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_602_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_a_599_);
lean_dec(v_val_595_);
lean_dec(v_a_594_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_581_);
v_a_637_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_601_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_601_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_dec(v_val_595_);
lean_dec(v_a_594_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_581_);
return v___x_598_;
}
}
}
else
{
lean_dec(v___y_588_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_581_);
return v___y_592_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoTry_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_545_ = stack[0].m_obj;
lean_object* v_dec_546_ = stack[1].m_obj;
lean_object* v_a_547_ = stack[2].m_obj;
lean_object* v_a_548_ = stack[3].m_obj;
lean_object* v_a_549_ = stack[4].m_obj;
lean_object* v_a_550_ = stack[5].m_obj;
lean_object* v_a_551_ = stack[6].m_obj;
lean_object* v_a_552_ = stack[7].m_obj;
lean_object* v_a_553_ = stack[8].m_obj;
lean_object* v_res_748_;
v_res_748_ = l_Lean_Elab_Do_elabDoTry(v_stx_545_, v_dec_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
stack->m_obj
 = v_res_748_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___boxed(lean_object* v_stx_749_, lean_object* v_dec_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Elab_Do_elabDoTry(v_stx_749_, v_dec_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_759_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3(lean_object* v_00_u03b1_760_, lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v_msg_761_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
return v___x_770_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_761_ = stack[1].m_obj;
lean_object* v___y_762_ = stack[2].m_obj;
lean_object* v___y_763_ = stack[3].m_obj;
lean_object* v___y_764_ = stack[4].m_obj;
lean_object* v___y_765_ = stack[5].m_obj;
lean_object* v___y_766_ = stack[6].m_obj;
lean_object* v___y_767_ = stack[7].m_obj;
lean_object* v___y_768_ = stack[8].m_obj;
lean_object* v_res_771_;
v_res_771_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3(lean_box(0), v_msg_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
stack->m_obj
 = v_res_771_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___boxed(lean_object* v_00_u03b1_772_, lean_object* v_msg_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3(v_00_u03b1_772_, v_msg_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec_ref(v___y_774_);
return v_res_782_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1(){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_792_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_793_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__1));
v___x_794_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3));
v___x_795_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoTry___boxed), 10, 0);
v___x_796_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_792_, v___x_793_, v___x_794_, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_797_;
v_res_797_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1();
stack->m_obj
 = v_res_797_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___boxed(lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1();
return v_res_799_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Control(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_TryCatch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_TryCatch(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Control(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_TryCatch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_TryCatch(builtin);
}
#ifdef __cplusplus
}
#endif
