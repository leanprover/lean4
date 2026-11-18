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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkFreshResultType___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_registerMVarErrorHoleInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkPure___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_enterFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___boxed(lean_object* v_00_u03b1_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0(v_00_u03b1_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(lean_object* v___x_29_, uint8_t v___x_30_, lean_object* v_cont_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Elab_Do_elabDoSeq(v___x_29_, v_cont_31_, v___x_30_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0___boxed(lean_object* v___x_41_, lean_object* v___x_42_, lean_object* v_cont_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
uint8_t v___x_3941__boxed_52_; lean_object* v_res_53_; 
v___x_3941__boxed_52_ = lean_unbox(v___x_42_);
v_res_53_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(v___x_41_, v___x_3941__boxed_52_, v_cont_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(lean_object* v_lifter_67_, lean_object* v___f_68_, lean_object* v___x_69_, uint8_t v___x_70_, lean_object* v_eType_x3f_71_, lean_object* v_monadInfo_72_, lean_object* v_body_73_, lean_object* v___y_74_, lean_object* v_x_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_catcher_84_; lean_object* v___y_85_; lean_object* v___x_102_; 
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
lean_inc(v___y_79_);
lean_inc_ref(v___y_78_);
lean_inc_ref(v_x_75_);
v___x_102_ = lean_infer_type(v_x_75_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_104_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc_n(v_a_103_, 2);
lean_dec_ref_known(v___x_102_, 1);
v___x_104_ = l_Lean_Meta_getDecLevel(v_a_103_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_104_) == 0)
{
if (lean_obj_tag(v_eType_x3f_71_) == 0)
{
lean_object* v_a_105_; lean_object* v_m_106_; lean_object* v_u_107_; lean_object* v_v_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v_m_106_ = lean_ctor_get(v_monadInfo_72_, 0);
lean_inc_ref_n(v_m_106_, 2);
v_u_107_ = lean_ctor_get(v_monadInfo_72_, 1);
lean_inc(v_u_107_);
v_v_108_ = lean_ctor_get(v_monadInfo_72_, 2);
lean_inc(v_v_108_);
lean_dec_ref(v_monadInfo_72_);
v___x_109_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1));
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v_v_108_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_112_, 0, v_u_107_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v_a_105_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
lean_inc_ref(v___x_113_);
v___x_114_ = l_Lean_mkConst(v___x_109_, v___x_113_);
lean_inc(v_a_103_);
v___x_115_ = l_Lean_mkAppB(v___x_114_, v_a_103_, v_m_106_);
v___x_116_ = lean_box(0);
v___x_117_ = l_Lean_Elab_Term_mkInstMVar(v___x_115_, v___x_116_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v_liftedDoBlockResultType_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_117_, 1);
v_liftedDoBlockResultType_119_ = lean_ctor_get(v_lifter_67_, 5);
v___x_120_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3));
v___x_121_ = l_Lean_mkConst(v___x_120_, v___x_113_);
lean_inc_ref(v_liftedDoBlockResultType_119_);
v___x_122_ = lean_alloc_closure((void*)(l_Lean_mkApp6), 7, 6);
lean_closure_set(v___x_122_, 0, v___x_121_);
lean_closure_set(v___x_122_, 1, v_a_103_);
lean_closure_set(v___x_122_, 2, v_m_106_);
lean_closure_set(v___x_122_, 3, v_a_118_);
lean_closure_set(v___x_122_, 4, v_liftedDoBlockResultType_119_);
lean_closure_set(v___x_122_, 5, v_body_73_);
v_catcher_84_ = v___x_122_;
v___y_85_ = v___y_74_;
goto v___jp_83_;
}
else
{
lean_dec_ref_known(v___x_113_, 2);
lean_dec_ref(v_m_106_);
lean_dec(v_a_103_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_body_73_);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_lifter_67_);
return v___x_117_;
}
}
else
{
lean_object* v_a_123_; lean_object* v_m_124_; lean_object* v_u_125_; lean_object* v_v_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_a_123_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_104_, 1);
v_m_124_ = lean_ctor_get(v_monadInfo_72_, 0);
lean_inc_ref_n(v_m_124_, 2);
v_u_125_ = lean_ctor_get(v_monadInfo_72_, 1);
lean_inc(v_u_125_);
v_v_126_ = lean_ctor_get(v_monadInfo_72_, 2);
lean_inc(v_v_126_);
lean_dec_ref(v_monadInfo_72_);
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5));
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v_v_126_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v_u_125_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v_a_123_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
lean_inc_ref(v___x_131_);
v___x_132_ = l_Lean_mkConst(v___x_127_, v___x_131_);
lean_inc(v_a_103_);
v___x_133_ = l_Lean_mkAppB(v___x_132_, v_a_103_, v_m_124_);
v___x_134_ = lean_box(0);
v___x_135_ = l_Lean_Elab_Term_mkInstMVar(v___x_133_, v___x_134_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v_liftedDoBlockResultType_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v_liftedDoBlockResultType_137_ = lean_ctor_get(v_lifter_67_, 5);
v___x_138_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7));
v___x_139_ = l_Lean_mkConst(v___x_138_, v___x_131_);
lean_inc_ref(v_liftedDoBlockResultType_137_);
v___x_140_ = lean_alloc_closure((void*)(l_Lean_mkApp6), 7, 6);
lean_closure_set(v___x_140_, 0, v___x_139_);
lean_closure_set(v___x_140_, 1, v_a_103_);
lean_closure_set(v___x_140_, 2, v_m_124_);
lean_closure_set(v___x_140_, 3, v_a_136_);
lean_closure_set(v___x_140_, 4, v_liftedDoBlockResultType_137_);
lean_closure_set(v___x_140_, 5, v_body_73_);
v_catcher_84_ = v___x_140_;
v___y_85_ = v___y_74_;
goto v___jp_83_;
}
else
{
lean_dec_ref_known(v___x_131_, 2);
lean_dec_ref(v_m_124_);
lean_dec(v_a_103_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_body_73_);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_lifter_67_);
return v___x_135_;
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec(v_a_103_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_body_73_);
lean_dec_ref(v_monadInfo_72_);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_lifter_67_);
v_a_141_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_104_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_104_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_dec_ref(v_x_75_);
lean_dec_ref(v_body_73_);
lean_dec_ref(v_monadInfo_72_);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_lifter_67_);
return v___x_102_;
}
v___jp_83_:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Elab_Do_EffectForwarder_lift(v_lifter_67_, v___f_68_, v___y_85_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_a_87_);
lean_dec_ref_known(v___x_86_, 1);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_69_);
v___x_89_ = lean_array_push(v___x_88_, v_x_75_);
v___x_90_ = 0;
v___x_91_ = 1;
v___x_92_ = l_Lean_Meta_mkLambdaFVars(v___x_89_, v_a_87_, v___x_90_, v___x_70_, v___x_90_, v___x_70_, v___x_91_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec_ref(v___x_89_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_101_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_101_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_101_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_apply_1(v_catcher_84_, v_a_93_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_97_);
v___x_99_ = v___x_95_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_dec_ref(v_catcher_84_);
return v___x_92_;
}
}
else
{
lean_dec_ref(v_catcher_84_);
lean_dec_ref(v_x_75_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed(lean_object* v_lifter_149_, lean_object* v___f_150_, lean_object* v___x_151_, lean_object* v___x_152_, lean_object* v_eType_x3f_153_, lean_object* v_monadInfo_154_, lean_object* v_body_155_, lean_object* v___y_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
uint8_t v___x_4000__boxed_165_; lean_object* v_res_166_; 
v___x_4000__boxed_165_ = lean_unbox(v___x_152_);
v_res_166_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(v_lifter_149_, v___f_150_, v___x_151_, v___x_4000__boxed_165_, v_eType_x3f_153_, v_monadInfo_154_, v_body_155_, v___y_156_, v_x_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec_ref(v___y_156_);
lean_dec(v_eType_x3f_153_);
lean_dec(v___x_151_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(lean_object* v_lifter_176_, lean_object* v_body_177_, lean_object* v_catch___178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
lean_inc(v_catch___178_);
v___x_188_ = l_Lean_Syntax_isOfKind(v_catch___178_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
lean_dec(v_catch___178_);
lean_dec_ref(v_body_177_);
lean_dec_ref(v_lifter_176_);
v___x_189_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_189_;
}
else
{
lean_object* v_monadInfo_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v_eType_x3f_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_monadInfo_190_ = lean_ctor_get(v_a_179_, 0);
v___x_191_ = lean_unsigned_to_nat(1u);
v___x_192_ = l_Lean_Syntax_getArg(v_catch___178_, v___x_191_);
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = l_Lean_Syntax_getArg(v_catch___178_, v___x_222_);
v___x_224_ = l_Lean_Syntax_isNone(v___x_223_);
if (v___x_224_ == 0)
{
uint8_t v___x_225_; 
lean_inc(v___x_223_);
v___x_225_ = l_Lean_Syntax_matchesNull(v___x_223_, v___x_222_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
lean_dec(v___x_223_);
lean_dec(v___x_192_);
lean_dec(v_catch___178_);
lean_dec_ref(v_body_177_);
lean_dec_ref(v_lifter_176_);
v___x_226_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = l_Lean_Syntax_getArg(v___x_223_, v___x_191_);
lean_dec(v___x_223_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
v_eType_x3f_205_ = v___x_228_;
v___y_206_ = v_a_179_;
v___y_207_ = v_a_180_;
v___y_208_ = v_a_181_;
v___y_209_ = v_a_182_;
v___y_210_ = v_a_183_;
v___y_211_ = v_a_184_;
v___y_212_ = v_a_185_;
goto v___jp_204_;
}
}
else
{
lean_object* v___x_229_; 
lean_dec(v___x_223_);
v___x_229_ = lean_box(0);
v_eType_x3f_205_ = v___x_229_;
v___y_206_ = v_a_179_;
v___y_207_ = v_a_180_;
v___y_208_ = v_a_181_;
v___y_209_ = v_a_182_;
v___y_210_ = v_a_183_;
v___y_211_ = v_a_184_;
v___y_212_ = v_a_185_;
goto v___jp_204_;
}
v___jp_193_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = l_Lean_Elab_Term_mkExplicitBinder(v___x_192_, v___y_201_);
v___x_203_ = l_Lean_Elab_Term_elabBinder___redArg(v___x_202_, v___y_197_, v___y_195_, v___y_200_, v___y_199_, v___y_198_, v___y_196_, v___y_194_);
return v___x_203_;
}
v___jp_204_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___f_218_; 
v___x_213_ = lean_unsigned_to_nat(4u);
v___x_214_ = l_Lean_Syntax_getArg(v_catch___178_, v___x_213_);
lean_dec(v_catch___178_);
v___x_215_ = lean_box(v___x_188_);
v___f_216_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0___boxed), 11, 2);
lean_closure_set(v___f_216_, 0, v___x_214_);
lean_closure_set(v___f_216_, 1, v___x_215_);
v___x_217_ = lean_box(v___x_188_);
lean_inc_ref(v___y_206_);
lean_inc_ref(v_monadInfo_190_);
lean_inc(v_eType_x3f_205_);
v___f_218_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed), 16, 8);
lean_closure_set(v___f_218_, 0, v_lifter_176_);
lean_closure_set(v___f_218_, 1, v___f_216_);
lean_closure_set(v___f_218_, 2, v___x_191_);
lean_closure_set(v___f_218_, 3, v___x_217_);
lean_closure_set(v___f_218_, 4, v_eType_x3f_205_);
lean_closure_set(v___f_218_, 5, v_monadInfo_190_);
lean_closure_set(v___f_218_, 6, v_body_177_);
lean_closure_set(v___f_218_, 7, v___y_206_);
if (lean_obj_tag(v_eType_x3f_205_) == 0)
{
uint8_t v___x_219_; lean_object* v___x_220_; 
v___x_219_ = 0;
v___x_220_ = l_Lean_mkHole(v___x_192_, v___x_219_);
v___y_194_ = v___y_212_;
v___y_195_ = v___y_207_;
v___y_196_ = v___y_211_;
v___y_197_ = v___f_218_;
v___y_198_ = v___y_210_;
v___y_199_ = v___y_209_;
v___y_200_ = v___y_208_;
v___y_201_ = v___x_220_;
goto v___jp_193_;
}
else
{
lean_object* v_val_221_; 
v_val_221_ = lean_ctor_get(v_eType_x3f_205_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v_eType_x3f_205_, 1);
v___y_194_ = v___y_212_;
v___y_195_ = v___y_207_;
v___y_196_ = v___y_211_;
v___y_197_ = v___f_218_;
v___y_198_ = v___y_210_;
v___y_199_ = v___y_209_;
v___y_200_ = v___y_208_;
v___y_201_ = v_val_221_;
goto v___jp_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___boxed(lean_object* v_lifter_230_, lean_object* v_body_231_, lean_object* v_catch___232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_lifter_230_, v_body_231_, v_catch___232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___lam__0(lean_object* v_trySeq_242_, uint8_t v___x_243_, lean_object* v_cont_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Elab_Do_elabDoSeq(v_trySeq_242_, v_cont_244_, v___x_243_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___lam__0___boxed(lean_object* v_trySeq_254_, lean_object* v___x_255_, lean_object* v_cont_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v___x_16717__boxed_265_; lean_object* v_res_266_; 
v___x_16717__boxed_265_ = lean_unbox(v___x_255_);
v_res_266_ = l_Lean_Elab_Do_elabDoTry___lam__0(v_trySeq_254_, v___x_16717__boxed_265_, v_cont_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(lean_object* v_as_270_, size_t v_i_271_, size_t v_stop_272_, lean_object* v_b_273_){
_start:
{
lean_object* v___y_275_; uint8_t v___x_279_; 
v___x_279_ = lean_usize_dec_eq(v_i_271_, v_stop_272_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_array_uget_borrowed(v_as_270_, v_i_271_);
v___x_281_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
lean_inc(v___x_280_);
v___x_282_ = l_Lean_Syntax_isOfKind(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
v___y_275_ = v_b_273_;
goto v___jp_274_;
}
else
{
lean_object* v___x_283_; lean_object* v_x_284_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_283_ = lean_unsigned_to_nat(1u);
v_x_284_ = l_Lean_Syntax_getArg(v___x_280_, v___x_283_);
v___x_287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___closed__1));
lean_inc(v_x_284_);
v___x_288_ = l_Lean_Syntax_isOfKind(v_x_284_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec(v_x_284_);
v___y_275_ = v_b_273_;
goto v___jp_274_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_unsigned_to_nat(2u);
v___x_290_ = l_Lean_Syntax_getArg(v___x_280_, v___x_289_);
v___x_291_ = l_Lean_Syntax_isNone(v___x_290_);
if (v___x_291_ == 0)
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_Syntax_matchesNull(v___x_290_, v___x_289_);
if (v___x_292_ == 0)
{
lean_dec(v_x_284_);
v___y_275_ = v_b_273_;
goto v___jp_274_;
}
else
{
goto v___jp_285_;
}
}
else
{
lean_dec(v___x_290_);
goto v___jp_285_;
}
}
v___jp_285_:
{
lean_object* v___x_286_; 
v___x_286_ = lean_array_push(v_b_273_, v_x_284_);
v___y_275_ = v___x_286_;
goto v___jp_274_;
}
}
}
else
{
return v_b_273_;
}
v___jp_274_:
{
size_t v___x_276_; size_t v___x_277_; 
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_add(v_i_271_, v___x_276_);
v_i_271_ = v___x_277_;
v_b_273_ = v___y_275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2___boxed(lean_object* v_as_293_, lean_object* v_i_294_, lean_object* v_stop_295_, lean_object* v_b_296_){
_start:
{
size_t v_i_boxed_297_; size_t v_stop_boxed_298_; lean_object* v_res_299_; 
v_i_boxed_297_ = lean_unbox_usize(v_i_294_);
lean_dec(v_i_294_);
v_stop_boxed_298_ = lean_unbox_usize(v_stop_295_);
lean_dec(v_stop_295_);
v_res_299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(v_as_293_, v_i_boxed_297_, v_stop_boxed_298_, v_b_296_);
lean_dec_ref(v_as_293_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2(lean_object* v_as_302_, lean_object* v_start_303_, lean_object* v_stop_304_){
_start:
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0));
v___x_306_ = lean_nat_dec_lt(v_start_303_, v_stop_304_);
if (v___x_306_ == 0)
{
return v___x_305_;
}
else
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_array_get_size(v_as_302_);
v___x_308_ = lean_nat_dec_le(v_stop_304_, v___x_307_);
if (v___x_308_ == 0)
{
uint8_t v___x_309_; 
v___x_309_ = lean_nat_dec_lt(v_start_303_, v___x_307_);
if (v___x_309_ == 0)
{
return v___x_305_;
}
else
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_usize_of_nat(v_start_303_);
v___x_311_ = lean_usize_of_nat(v___x_307_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(v_as_302_, v___x_310_, v___x_311_, v___x_305_);
return v___x_312_;
}
}
else
{
size_t v___x_313_; size_t v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_usize_of_nat(v_start_303_);
v___x_314_ = lean_usize_of_nat(v_stop_304_);
v___x_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2_spec__2(v_as_302_, v___x_313_, v___x_314_, v___x_305_);
return v___x_315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2___boxed(lean_object* v_as_316_, lean_object* v_start_317_, lean_object* v_stop_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2(v_as_316_, v_start_317_, v_stop_318_);
lean_dec(v_stop_318_);
lean_dec(v_start_317_);
lean_dec_ref(v_as_316_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_env_327_; uint8_t v___x_328_; lean_object* v_env_329_; lean_object* v___x_330_; lean_object* v_toCold_331_; lean_object* v_mctx_332_; lean_object* v_lctx_333_; lean_object* v_options_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = 0;
v_env_329_ = l_Lean_Environment_setRecordingDeps(v_env_327_, v___x_328_);
v___x_330_ = lean_st_ref_get(v___y_322_);
v_toCold_331_ = lean_ctor_get(v___y_323_, 0);
v_mctx_332_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_mctx_332_);
lean_dec(v___x_330_);
v_lctx_333_ = lean_ctor_get(v___y_321_, 2);
v_options_334_ = lean_ctor_get(v_toCold_331_, 2);
lean_inc_ref(v_options_334_);
lean_inc_ref(v_lctx_333_);
v___x_335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_335_, 0, v_env_329_);
lean_ctor_set(v___x_335_, 1, v_mctx_332_);
lean_ctor_set(v___x_335_, 2, v_lctx_333_);
lean_ctor_set(v___x_335_, 3, v_options_334_);
v___x_336_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_msgData_320_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4___boxed(lean_object* v_msgData_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msgData_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(lean_object* v_msg_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_ref_351_; lean_object* v___x_352_; lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_361_; 
v_ref_351_ = lean_ctor_get(v___y_348_, 2);
v___x_352_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msg_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_361_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_361_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_inc(v_ref_351_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_ref_351_);
lean_ctor_set(v___x_357_, 1, v_a_353_);
if (v_isShared_356_ == 0)
{
lean_ctor_set_tag(v___x_355_, 1);
lean_ctor_set(v___x_355_, 0, v___x_357_);
v___x_359_ = v___x_355_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg___boxed(lean_object* v_msg_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v_msg_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
return v_res_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__3));
v___x_378_ = l_String_toRawSubstring_x27(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8(void){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Array_mkArray0___redArg();
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(lean_object* v_a_412_, lean_object* v_as_413_, size_t v_i_414_, size_t v_stop_415_, lean_object* v_b_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___y_426_; uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_eq(v_i_414_, v_stop_415_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__1));
v___x_433_ = lean_array_uget_borrowed(v_as_413_, v_i_414_);
lean_inc(v___x_433_);
v___x_434_ = l_Lean_Syntax_isOfKind(v___x_433_, v___x_432_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_inc(v___x_433_);
lean_inc_ref(v_a_412_);
v___x_435_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_a_412_, v_b_416_, v___x_433_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
v___y_426_ = v___x_435_;
goto v___jp_425_;
}
else
{
lean_object* v_toCold_436_; lean_object* v_ref_437_; lean_object* v_quotContext_438_; lean_object* v_currMacroScope_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_toCold_436_ = lean_ctor_get(v___y_422_, 0);
v_ref_437_ = lean_ctor_get(v___y_422_, 2);
v_quotContext_438_ = lean_ctor_get(v_toCold_436_, 8);
v_currMacroScope_439_ = lean_ctor_get(v_toCold_436_, 9);
v___x_440_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = l_Lean_Syntax_getArg(v___x_433_, v___x_441_);
v___x_443_ = l_Lean_SourceInfo_fromRef(v_ref_437_, v___x_431_);
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__2));
lean_inc_n(v___x_443_, 12);
v___x_445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__4);
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__5));
lean_inc(v_currMacroScope_439_);
lean_inc(v_quotContext_438_);
v___x_448_ = l_Lean_addMacroScope(v_quotContext_438_, v___x_447_, v_currMacroScope_439_);
v___x_449_ = lean_box(0);
v___x_450_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_450_, 0, v___x_443_);
lean_ctor_set(v___x_450_, 1, v___x_446_);
lean_ctor_set(v___x_450_, 2, v___x_448_);
lean_ctor_set(v___x_450_, 3, v___x_449_);
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__7));
v___x_452_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__8);
v___x_453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_453_, 0, v___x_443_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_452_);
v___x_454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__9));
v___x_455_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_443_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__11));
v___x_457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__13));
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__15));
v___x_459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__16));
v___x_460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_443_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__18));
lean_inc_ref(v___x_450_);
lean_inc_ref_n(v___x_453_, 5);
v___x_462_ = l_Lean_Syntax_node2(v___x_443_, v___x_461_, v___x_453_, v___x_450_);
v___x_463_ = l_Lean_Syntax_node1(v___x_443_, v___x_451_, v___x_462_);
v___x_464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__19));
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_443_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_Syntax_node7(v___x_443_, v___x_458_, v___x_460_, v___x_453_, v___x_453_, v___x_453_, v___x_463_, v___x_465_, v___x_442_);
v___x_467_ = l_Lean_Syntax_node2(v___x_443_, v___x_457_, v___x_466_, v___x_453_);
v___x_468_ = l_Lean_Syntax_node1(v___x_443_, v___x_451_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___x_443_, v___x_456_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node5(v___x_443_, v___x_440_, v___x_445_, v___x_450_, v___x_453_, v___x_455_, v___x_469_);
lean_inc_ref(v_a_412_);
v___x_471_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_a_412_, v_b_416_, v___x_470_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
v___y_426_ = v___x_471_;
goto v___jp_425_;
}
}
else
{
lean_object* v___x_472_; 
lean_dec_ref(v_a_412_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v_b_416_);
return v___x_472_;
}
v___jp_425_:
{
if (lean_obj_tag(v___y_426_) == 0)
{
lean_object* v_a_427_; size_t v___x_428_; size_t v___x_429_; 
v_a_427_ = lean_ctor_get(v___y_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___y_426_, 1);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_add(v_i_414_, v___x_428_);
v_i_414_ = v___x_429_;
v_b_416_ = v_a_427_;
goto _start;
}
else
{
lean_dec_ref(v_a_412_);
return v___y_426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1___boxed(lean_object* v_a_473_, lean_object* v_as_474_, lean_object* v_i_475_, lean_object* v_stop_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
size_t v_i_boxed_486_; size_t v_stop_boxed_487_; lean_object* v_res_488_; 
v_i_boxed_486_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_stop_boxed_487_ = lean_unbox_usize(v_stop_476_);
lean_dec(v_stop_476_);
v_res_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(v_a_473_, v_as_474_, v_i_boxed_486_, v_stop_boxed_487_, v_b_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec_ref(v_as_474_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(size_t v_sz_489_, size_t v_i_490_, lean_object* v_bs_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_bs_491_);
return v___x_493_;
}
else
{
lean_object* v_v_494_; lean_object* v___x_495_; lean_object* v_bs_x27_496_; size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; 
v_v_494_ = lean_array_uget(v_bs_491_, v_i_490_);
v___x_495_ = lean_unsigned_to_nat(0u);
v_bs_x27_496_ = lean_array_uset(v_bs_491_, v_i_490_, v___x_495_);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_add(v_i_490_, v___x_497_);
v___x_499_ = lean_array_uset(v_bs_x27_496_, v_i_490_, v_v_494_);
v_i_490_ = v___x_498_;
v_bs_491_ = v___x_499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0___boxed(lean_object* v_sz_501_, lean_object* v_i_502_, lean_object* v_bs_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_501_);
lean_dec(v_sz_501_);
v_i_boxed_505_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_boxed_504_, v_i_boxed_505_, v_bs_503_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoTry___closed__11(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__10));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry(lean_object* v_stx_534_, lean_object* v_dec_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v_body_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___x_567_; uint8_t v___x_568_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v_a_582_; 
v___x_567_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__1));
lean_inc(v_stx_534_);
v___x_568_ = l_Lean_Syntax_isOfKind(v_stx_534_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_dec_535_);
lean_dec(v_stx_534_);
v___x_643_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; size_t v_sz_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___x_644_ = lean_unsigned_to_nat(2u);
v___x_645_ = l_Lean_Syntax_getArg(v_stx_534_, v___x_644_);
v___x_646_ = l_Lean_Syntax_getArgs(v___x_645_);
lean_dec(v___x_645_);
v_sz_647_ = lean_array_size(v___x_646_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_647_, v___x_648_, v___x_646_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v_dec_535_);
lean_dec(v_stx_534_);
v___x_650_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_650_;
}
else
{
lean_object* v_val_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_747_; 
v_val_651_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_747_ == 0)
{
v___x_653_ = v___x_649_;
v_isShared_654_ = v_isSharedCheck_747_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_val_651_);
lean_dec(v___x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_747_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___x_695_; lean_object* v_trySeq_696_; lean_object* v___x_697_; lean_object* v___f_698_; lean_object* v_finTk_x3f_700_; lean_object* v_finSeq_x3f_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_unsigned_to_nat(1u);
v_trySeq_696_ = l_Lean_Syntax_getArg(v_stx_534_, v___x_695_);
v___x_697_ = lean_box(v___x_568_);
v___f_698_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoTry___lam__0___boxed), 11, 2);
lean_closure_set(v___f_698_, 0, v_trySeq_696_);
lean_closure_set(v___f_698_, 1, v___x_697_);
v___x_731_ = lean_unsigned_to_nat(3u);
v___x_732_ = l_Lean_Syntax_getArg(v_stx_534_, v___x_731_);
v___x_733_ = l_Lean_Syntax_isNone(v___x_732_);
if (v___x_733_ == 0)
{
uint8_t v___x_734_; 
lean_inc(v___x_732_);
v___x_734_ = l_Lean_Syntax_matchesNull(v___x_732_, v___x_695_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; 
lean_dec(v___x_732_);
lean_dec_ref(v___f_698_);
lean_del_object(v___x_653_);
lean_dec(v_val_651_);
lean_dec_ref(v_dec_535_);
lean_dec(v_stx_534_);
v___x_735_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_735_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = l_Lean_Syntax_getArg(v___x_732_, v___x_655_);
lean_dec(v___x_732_);
v___x_737_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__13));
lean_inc(v___x_736_);
v___x_738_ = l_Lean_Syntax_isOfKind(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
lean_dec(v___x_736_);
lean_dec_ref(v___f_698_);
lean_del_object(v___x_653_);
lean_dec(v_val_651_);
lean_dec_ref(v_dec_535_);
lean_dec(v_stx_534_);
v___x_739_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_739_;
}
else
{
lean_object* v_finTk_x3f_740_; lean_object* v_finSeq_x3f_741_; lean_object* v___x_743_; 
v_finTk_x3f_740_ = l_Lean_Syntax_getArg(v___x_736_, v___x_655_);
v_finSeq_x3f_741_ = l_Lean_Syntax_getArg(v___x_736_, v___x_695_);
lean_dec(v___x_736_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_finTk_x3f_740_);
v___x_743_ = v___x_653_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_finTk_x3f_740_);
v___x_743_ = v_reuseFailAlloc_745_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_744_, 0, v_finSeq_x3f_741_);
v_finTk_x3f_700_ = v___x_743_;
v_finSeq_x3f_701_ = v___x_744_;
v___y_702_ = v_a_536_;
v___y_703_ = v_a_537_;
v___y_704_ = v_a_538_;
v___y_705_ = v_a_539_;
v___y_706_ = v_a_540_;
v___y_707_ = v_a_541_;
v___y_708_ = v_a_542_;
goto v___jp_699_;
}
}
}
}
else
{
lean_object* v___x_746_; 
lean_dec(v___x_732_);
lean_del_object(v___x_653_);
v___x_746_ = lean_box(0);
v_finTk_x3f_700_ = v___x_746_;
v_finSeq_x3f_701_ = v___x_746_;
v___y_702_ = v_a_536_;
v___y_703_ = v_a_537_;
v___y_704_ = v_a_538_;
v___y_705_ = v_a_539_;
v___y_706_ = v_a_540_;
v___y_707_ = v_a_541_;
v___y_708_ = v_a_542_;
goto v___jp_699_;
}
v___jp_656_:
{
lean_object* v_monadInfo_668_; lean_object* v___x_669_; 
v_monadInfo_668_ = lean_ctor_get(v___y_661_, 0);
v___x_669_ = l_Lean_Elab_Do_inferControlInfoElem(v_stx_534_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_a_670_, v_dec_535_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_n(v_a_672_, 2);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = l_Lean_Elab_Do_EffectForwarder_lift(v_a_672_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; uint8_t v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = lean_nat_dec_lt(v___x_655_, v___y_658_);
if (v___x_675_ == 0)
{
lean_dec(v___y_658_);
lean_dec(v_val_651_);
v___y_570_ = v___y_657_;
v___y_571_ = v___y_662_;
v___y_572_ = v___y_667_;
v___y_573_ = v___y_663_;
v___y_574_ = v_a_672_;
v___y_575_ = v___y_661_;
v___y_576_ = v_monadInfo_668_;
v___y_577_ = v___y_664_;
v___y_578_ = v_a_670_;
v___y_579_ = v___y_659_;
v___y_580_ = v___y_665_;
v___y_581_ = v___y_666_;
v_a_582_ = v_a_674_;
goto v___jp_569_;
}
else
{
size_t v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_usize_of_nat(v___y_658_);
lean_dec(v___y_658_);
lean_inc(v_a_672_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__1(v_a_672_, v_val_651_, v___x_648_, v___x_676_, v_a_674_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v_val_651_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v___y_570_ = v___y_657_;
v___y_571_ = v___y_662_;
v___y_572_ = v___y_667_;
v___y_573_ = v___y_663_;
v___y_574_ = v_a_672_;
v___y_575_ = v___y_661_;
v___y_576_ = v_monadInfo_668_;
v___y_577_ = v___y_664_;
v___y_578_ = v_a_670_;
v___y_579_ = v___y_659_;
v___y_580_ = v___y_665_;
v___y_581_ = v___y_666_;
v_a_582_ = v_a_678_;
goto v___jp_569_;
}
else
{
lean_dec(v_a_672_);
lean_dec(v_a_670_);
lean_dec(v___y_659_);
lean_dec(v___y_657_);
return v___x_677_;
}
}
}
else
{
lean_dec(v_a_672_);
lean_dec(v_a_670_);
lean_dec(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v_val_651_);
return v___x_673_;
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v_a_670_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v_val_651_);
v_a_679_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_671_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_671_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v_val_651_);
lean_dec_ref(v_dec_535_);
v_a_687_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_669_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_669_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
v___jp_699_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_array_get_size(v_val_651_);
v___x_710_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__2(v_val_651_, v___x_655_, v___x_709_);
v___x_711_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_710_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec_ref(v___x_710_);
if (lean_obj_tag(v___x_711_) == 0)
{
uint8_t v___x_712_; 
lean_dec_ref_known(v___x_711_, 1);
v___x_712_ = lean_nat_dec_eq(v___x_709_, v___x_655_);
if (v___x_712_ == 0)
{
v___y_657_ = v_finSeq_x3f_701_;
v___y_658_ = v___x_709_;
v___y_659_ = v_finTk_x3f_700_;
v___y_660_ = v___f_698_;
v___y_661_ = v___y_702_;
v___y_662_ = v___y_703_;
v___y_663_ = v___y_704_;
v___y_664_ = v___y_705_;
v___y_665_ = v___y_706_;
v___y_666_ = v___y_707_;
v___y_667_ = v___y_708_;
goto v___jp_656_;
}
else
{
if (lean_obj_tag(v_finSeq_x3f_701_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_finTk_x3f_700_);
lean_dec_ref(v___f_698_);
lean_dec(v_val_651_);
lean_dec_ref(v_dec_535_);
lean_dec(v_stx_534_);
v___x_713_ = lean_obj_once(&l_Lean_Elab_Do_elabDoTry___closed__11, &l_Lean_Elab_Do_elabDoTry___closed__11_once, _init_l_Lean_Elab_Do_elabDoTry___closed__11);
v___x_714_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v___x_713_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
v___y_657_ = v_finSeq_x3f_701_;
v___y_658_ = v___x_709_;
v___y_659_ = v_finTk_x3f_700_;
v___y_660_ = v___f_698_;
v___y_661_ = v___y_702_;
v___y_662_ = v___y_703_;
v___y_663_ = v___y_704_;
v___y_664_ = v___y_705_;
v___y_665_ = v___y_706_;
v___y_666_ = v___y_707_;
v___y_667_ = v___y_708_;
goto v___jp_656_;
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_finSeq_x3f_701_);
lean_dec(v_finTk_x3f_700_);
lean_dec_ref(v___f_698_);
lean_dec(v_val_651_);
lean_dec_ref(v_dec_535_);
lean_dec(v_stx_534_);
v_a_723_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_711_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_711_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
}
v___jp_544_:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v___y_545_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_555_, 1);
v___x_557_ = l_Lean_Elab_Do_DoElemCont_withDeadCodeFromInfo(v_a_556_, v___y_546_);
lean_dec_ref(v___y_546_);
v___x_558_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v___x_557_, v_body_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec_ref(v_body_547_);
lean_dec_ref(v___y_546_);
v_a_559_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_555_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
v___jp_569_:
{
if (lean_obj_tag(v___y_579_) == 1)
{
if (lean_obj_tag(v___y_570_) == 1)
{
lean_object* v_val_583_; lean_object* v_val_584_; lean_object* v_toCold_585_; lean_object* v_currRecDepth_586_; lean_object* v_ref_587_; uint16_t v_optionFlags_588_; uint8_t v_suppressElabErrors_589_; uint8_t v_checkDeprecated_590_; uint8_t v_isRecordingDeps_591_; lean_object* v___x_592_; uint8_t v___x_593_; lean_object* v_ref_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_val_583_ = lean_ctor_get(v___y_579_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v___y_579_, 1);
v_val_584_ = lean_ctor_get(v___y_570_, 0);
lean_inc(v_val_584_);
lean_dec_ref_known(v___y_570_, 1);
v_toCold_585_ = lean_ctor_get(v___y_581_, 0);
v_currRecDepth_586_ = lean_ctor_get(v___y_581_, 1);
v_ref_587_ = lean_ctor_get(v___y_581_, 2);
v_optionFlags_588_ = lean_ctor_get_uint16(v___y_581_, sizeof(void*)*3);
v_suppressElabErrors_589_ = lean_ctor_get_uint8(v___y_581_, sizeof(void*)*3 + 2);
v_checkDeprecated_590_ = lean_ctor_get_uint8(v___y_581_, sizeof(void*)*3 + 3);
v_isRecordingDeps_591_ = lean_ctor_get_uint8(v___y_581_, sizeof(void*)*3 + 4);
v___x_592_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__3));
v___x_593_ = 0;
v_ref_594_ = l_Lean_replaceRef(v_val_583_, v_ref_587_);
lean_dec(v_val_583_);
lean_inc(v_currRecDepth_586_);
lean_inc_ref(v_toCold_585_);
v___x_595_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_595_, 0, v_toCold_585_);
lean_ctor_set(v___x_595_, 1, v_currRecDepth_586_);
lean_ctor_set(v___x_595_, 2, v_ref_594_);
lean_ctor_set_uint16(v___x_595_, sizeof(void*)*3, v_optionFlags_588_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*3 + 2, v_suppressElabErrors_589_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*3 + 3, v_checkDeprecated_590_);
lean_ctor_set_uint8(v___x_595_, sizeof(void*)*3 + 4, v_isRecordingDeps_591_);
v___x_596_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_592_, v___x_593_, v___y_575_, v___y_577_, v___y_580_, v___x_595_, v___y_572_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = l_Lean_Expr_mvarId_x21(v_a_597_);
lean_inc(v_val_584_);
v___x_599_ = l_Lean_Elab_Term_registerMVarErrorHoleInfo___redArg(v___x_598_, v_val_584_, v___y_573_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v___x_600_; 
lean_dec_ref_known(v___x_599_, 1);
lean_inc(v_a_597_);
v___x_600_ = l_Lean_Elab_Do_DoElemCont_mkPure___redArg(v_a_597_, v___x_595_, v___y_572_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = lean_box(v___x_568_);
lean_inc(v_val_584_);
v___x_603_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_603_, 0, v_val_584_);
lean_closure_set(v___x_603_, 1, v_a_601_);
lean_closure_set(v___x_603_, 2, v___x_602_);
lean_inc(v_a_597_);
v___x_604_ = l_Lean_Elab_Do_enterFinally(v_val_584_, v_a_597_, v___x_603_, v___y_575_, v___y_571_, v___y_573_, v___y_577_, v___y_580_, v___x_595_, v___y_572_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_m_606_; lean_object* v_u_607_; lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v_m_606_ = lean_ctor_get(v___y_576_, 0);
v_u_607_ = lean_ctor_get(v___y_576_, 1);
v_v_608_ = lean_ctor_get(v___y_576_, 2);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__5));
v___x_610_ = lean_box(0);
lean_inc(v_v_608_);
v___x_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_611_, 0, v_v_608_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
lean_inc(v_u_607_);
v___x_612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_612_, 0, v_u_607_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
lean_inc_ref(v___x_612_);
v___x_613_ = l_Lean_mkConst(v___x_609_, v___x_612_);
lean_inc_ref(v_m_606_);
v___x_614_ = l_Lean_Expr_app___override(v___x_613_, v_m_606_);
v___x_615_ = lean_box(0);
v___x_616_ = l_Lean_Elab_Term_mkInstMVar(v___x_614_, v___x_615_, v___y_571_, v___y_573_, v___y_577_, v___y_580_, v___x_595_, v___y_572_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__7));
lean_inc_ref(v___x_612_);
v___x_619_ = l_Lean_mkConst(v___x_618_, v___x_612_);
lean_inc_ref(v_m_606_);
v___x_620_ = l_Lean_Expr_app___override(v___x_619_, v_m_606_);
v___x_621_ = l_Lean_Elab_Term_mkInstMVar(v___x_620_, v___x_615_, v___y_571_, v___y_573_, v___y_577_, v___y_580_, v___x_595_, v___y_572_);
lean_dec_ref_known(v___x_595_, 3);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v_liftedDoBlockResultType_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v_liftedDoBlockResultType_623_ = lean_ctor_get(v___y_574_, 5);
v___x_624_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__9));
v___x_625_ = l_Lean_mkConst(v___x_624_, v___x_612_);
lean_inc_ref(v_liftedDoBlockResultType_623_);
lean_inc_ref(v_m_606_);
v___x_626_ = l_Lean_mkApp7(v___x_625_, v_m_606_, v_liftedDoBlockResultType_623_, v_a_597_, v_a_617_, v_a_622_, v_a_582_, v_a_605_);
v___y_545_ = v___y_574_;
v___y_546_ = v___y_578_;
v_body_547_ = v___x_626_;
v___y_548_ = v___y_575_;
v___y_549_ = v___y_571_;
v___y_550_ = v___y_573_;
v___y_551_ = v___y_577_;
v___y_552_ = v___y_580_;
v___y_553_ = v___y_581_;
v___y_554_ = v___y_572_;
goto v___jp_544_;
}
else
{
lean_dec(v_a_617_);
lean_dec_ref_known(v___x_612_, 2);
lean_dec(v_a_605_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_582_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_574_);
return v___x_621_;
}
}
else
{
lean_dec_ref_known(v___x_612_, 2);
lean_dec(v_a_605_);
lean_dec(v_a_597_);
lean_dec_ref_known(v___x_595_, 3);
lean_dec_ref(v_a_582_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_574_);
return v___x_616_;
}
}
else
{
lean_dec(v_a_597_);
lean_dec_ref_known(v___x_595_, 3);
lean_dec_ref(v_a_582_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_574_);
return v___x_604_;
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_a_597_);
lean_dec_ref_known(v___x_595_, 3);
lean_dec(v_val_584_);
lean_dec_ref(v_a_582_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_574_);
v_a_627_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_600_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_600_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_a_597_);
lean_dec_ref_known(v___x_595_, 3);
lean_dec(v_val_584_);
lean_dec_ref(v_a_582_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_574_);
v_a_635_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_599_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_599_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_595_, 3);
lean_dec(v_val_584_);
lean_dec_ref(v_a_582_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v___y_574_);
return v___x_596_;
}
}
else
{
lean_dec_ref_known(v___y_579_, 1);
lean_dec(v___y_570_);
v___y_545_ = v___y_574_;
v___y_546_ = v___y_578_;
v_body_547_ = v_a_582_;
v___y_548_ = v___y_575_;
v___y_549_ = v___y_571_;
v___y_550_ = v___y_573_;
v___y_551_ = v___y_577_;
v___y_552_ = v___y_580_;
v___y_553_ = v___y_581_;
v___y_554_ = v___y_572_;
goto v___jp_544_;
}
}
else
{
lean_dec(v___y_579_);
lean_dec(v___y_570_);
v___y_545_ = v___y_574_;
v___y_546_ = v___y_578_;
v_body_547_ = v_a_582_;
v___y_548_ = v___y_575_;
v___y_549_ = v___y_571_;
v___y_550_ = v___y_573_;
v___y_551_ = v___y_577_;
v___y_552_ = v___y_580_;
v___y_553_ = v___y_581_;
v___y_554_ = v___y_572_;
goto v___jp_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___boxed(lean_object* v_stx_748_, lean_object* v_dec_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Elab_Do_elabDoTry(v_stx_748_, v_dec_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec_ref(v_a_750_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3(lean_object* v_00_u03b1_759_, lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v_msg_760_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___boxed(lean_object* v_00_u03b1_770_, lean_object* v_msg_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3(v_00_u03b1_770_, v_msg_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v___y_772_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1(){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_791_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__1));
v___x_792_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___closed__3));
v___x_793_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoTry___boxed), 10, 0);
v___x_794_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_790_, v___x_791_, v___x_792_, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1___boxed(lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoTry___regBuiltin_Lean_Elab_Do_elabDoTry__1();
return v_res_796_;
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
