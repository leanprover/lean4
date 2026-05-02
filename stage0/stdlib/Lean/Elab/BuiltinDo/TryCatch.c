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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Do_ControlLifter_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_ControlLifter_restoreCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkFreshResultType___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_registerMVarErrorHoleInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkPure___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_enterFinally(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_ControlLifter_ofCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "doCatchMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 106, 10, 98, 177, 11, 181, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "catch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__14_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__19_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_4680__boxed_52_; lean_object* v_res_53_; 
v___x_4680__boxed_52_ = lean_unbox(v___x_42_);
v_res_53_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0(v___x_41_, v___x_4680__boxed_52_, v_cont_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(lean_object* v_lifter_67_, lean_object* v___f_68_, lean_object* v___x_69_, uint8_t v___x_70_, lean_object* v_monadInfo_71_, lean_object* v_body_72_, lean_object* v___y_73_, lean_object* v_eType_x3f_74_, lean_object* v_x_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_catcher_84_; lean_object* v___y_85_; lean_object* v___y_86_; lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_90_; lean_object* v___y_91_; lean_object* v___x_108_; 
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
lean_inc(v___y_79_);
lean_inc_ref(v___y_78_);
lean_inc_ref(v_x_75_);
v___x_108_ = lean_infer_type(v_x_75_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_n(v_a_109_, 2);
lean_dec_ref(v___x_108_);
v___x_110_ = l_Lean_Meta_getDecLevel(v_a_109_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref(v___x_110_);
if (lean_obj_tag(v_eType_x3f_74_) == 0)
{
goto v___jp_112_;
}
else
{
if (v___x_70_ == 0)
{
goto v___jp_112_;
}
else
{
lean_object* v_m_130_; lean_object* v_u_131_; lean_object* v_v_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_m_130_ = lean_ctor_get(v_monadInfo_71_, 0);
lean_inc_ref_n(v_m_130_, 2);
v_u_131_ = lean_ctor_get(v_monadInfo_71_, 1);
lean_inc(v_u_131_);
v_v_132_ = lean_ctor_get(v_monadInfo_71_, 2);
lean_inc(v_v_132_);
lean_dec_ref(v_monadInfo_71_);
v___x_133_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__5));
v___x_134_ = lean_box(0);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v_v_132_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v_u_131_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_137_, 0, v_a_111_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
lean_inc_ref(v___x_137_);
v___x_138_ = l_Lean_mkConst(v___x_133_, v___x_137_);
lean_inc(v_a_109_);
v___x_139_ = l_Lean_mkAppB(v___x_138_, v_a_109_, v_m_130_);
v___x_140_ = lean_box(0);
v___x_141_ = l_Lean_Elab_Term_mkInstMVar(v___x_139_, v___x_140_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v_liftedDoBlockResultType_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref(v___x_141_);
v_liftedDoBlockResultType_143_ = lean_ctor_get(v_lifter_67_, 5);
v___x_144_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__7));
v___x_145_ = l_Lean_mkConst(v___x_144_, v___x_137_);
lean_inc_ref(v_liftedDoBlockResultType_143_);
v___x_146_ = lean_alloc_closure((void*)(l_Lean_mkApp6), 7, 6);
lean_closure_set(v___x_146_, 0, v___x_145_);
lean_closure_set(v___x_146_, 1, v_a_109_);
lean_closure_set(v___x_146_, 2, v_m_130_);
lean_closure_set(v___x_146_, 3, v_a_142_);
lean_closure_set(v___x_146_, 4, v_liftedDoBlockResultType_143_);
lean_closure_set(v___x_146_, 5, v_body_72_);
v_catcher_84_ = v___x_146_;
v___y_85_ = v___y_73_;
v___y_86_ = v___y_76_;
v___y_87_ = v___y_77_;
v___y_88_ = v___y_78_;
v___y_89_ = v___y_79_;
v___y_90_ = v___y_80_;
v___y_91_ = v___y_81_;
goto v___jp_83_;
}
else
{
lean_dec_ref(v___x_137_);
lean_dec_ref(v_m_130_);
lean_dec(v_a_109_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_body_72_);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_lifter_67_);
return v___x_141_;
}
}
}
v___jp_112_:
{
lean_object* v_m_113_; lean_object* v_u_114_; lean_object* v_v_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_m_113_ = lean_ctor_get(v_monadInfo_71_, 0);
lean_inc_ref_n(v_m_113_, 2);
v_u_114_ = lean_ctor_get(v_monadInfo_71_, 1);
lean_inc(v_u_114_);
v_v_115_ = lean_ctor_get(v_monadInfo_71_, 2);
lean_inc(v_v_115_);
lean_dec_ref(v_monadInfo_71_);
v___x_116_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__1));
v___x_117_ = lean_box(0);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v_v_115_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v_u_114_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v_a_111_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_inc_ref(v___x_120_);
v___x_121_ = l_Lean_mkConst(v___x_116_, v___x_120_);
lean_inc(v_a_109_);
v___x_122_ = l_Lean_mkAppB(v___x_121_, v_a_109_, v_m_113_);
v___x_123_ = lean_box(0);
v___x_124_ = l_Lean_Elab_Term_mkInstMVar(v___x_122_, v___x_123_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v_liftedDoBlockResultType_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref(v___x_124_);
v_liftedDoBlockResultType_126_ = lean_ctor_get(v_lifter_67_, 5);
v___x_127_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___closed__3));
v___x_128_ = l_Lean_mkConst(v___x_127_, v___x_120_);
lean_inc_ref(v_liftedDoBlockResultType_126_);
v___x_129_ = lean_alloc_closure((void*)(l_Lean_mkApp6), 7, 6);
lean_closure_set(v___x_129_, 0, v___x_128_);
lean_closure_set(v___x_129_, 1, v_a_109_);
lean_closure_set(v___x_129_, 2, v_m_113_);
lean_closure_set(v___x_129_, 3, v_a_125_);
lean_closure_set(v___x_129_, 4, v_liftedDoBlockResultType_126_);
lean_closure_set(v___x_129_, 5, v_body_72_);
v_catcher_84_ = v___x_129_;
v___y_85_ = v___y_73_;
v___y_86_ = v___y_76_;
v___y_87_ = v___y_77_;
v___y_88_ = v___y_78_;
v___y_89_ = v___y_79_;
v___y_90_ = v___y_80_;
v___y_91_ = v___y_81_;
goto v___jp_83_;
}
else
{
lean_dec_ref(v___x_120_);
lean_dec_ref(v_m_113_);
lean_dec(v_a_109_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_body_72_);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_lifter_67_);
return v___x_124_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_a_109_);
lean_dec_ref(v_x_75_);
lean_dec_ref(v_body_72_);
lean_dec_ref(v_monadInfo_71_);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_lifter_67_);
v_a_147_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_110_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_110_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
lean_dec_ref(v_x_75_);
lean_dec_ref(v_body_72_);
lean_dec_ref(v_monadInfo_71_);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_lifter_67_);
return v___x_108_;
}
v___jp_83_:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Elab_Do_ControlLifter_lift(v_lifter_67_, v___f_68_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc(v_a_93_);
lean_dec_ref(v___x_92_);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_69_);
v___x_95_ = lean_array_push(v___x_94_, v_x_75_);
v___x_96_ = 0;
v___x_97_ = 1;
v___x_98_ = l_Lean_Meta_mkLambdaFVars(v___x_95_, v_a_93_, v___x_96_, v___x_70_, v___x_96_, v___x_70_, v___x_97_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec_ref(v___x_95_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_107_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_apply_1(v_catcher_84_, v_a_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
else
{
lean_dec_ref(v_catcher_84_);
return v___x_98_;
}
}
else
{
lean_dec_ref(v_catcher_84_);
lean_dec_ref(v_x_75_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed(lean_object* v_lifter_155_, lean_object* v___f_156_, lean_object* v___x_157_, lean_object* v___x_158_, lean_object* v_monadInfo_159_, lean_object* v_body_160_, lean_object* v___y_161_, lean_object* v_eType_x3f_162_, lean_object* v_x_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
uint8_t v___x_4739__boxed_171_; lean_object* v_res_172_; 
v___x_4739__boxed_171_ = lean_unbox(v___x_158_);
v_res_172_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1(v_lifter_155_, v___f_156_, v___x_157_, v___x_4739__boxed_171_, v_monadInfo_159_, v_body_160_, v___y_161_, v_eType_x3f_162_, v_x_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v_eType_x3f_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___x_157_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(lean_object* v_lifter_182_, lean_object* v_body_183_, lean_object* v_catch___184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
lean_inc(v_catch___184_);
v___x_194_ = l_Lean_Syntax_isOfKind(v_catch___184_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec(v_catch___184_);
lean_dec_ref(v_body_183_);
lean_dec_ref(v_lifter_182_);
v___x_195_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_195_;
}
else
{
lean_object* v_monadInfo_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v_eType_x3f_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v_monadInfo_196_ = lean_ctor_get(v_a_185_, 0);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = l_Lean_Syntax_getArg(v_catch___184_, v___x_197_);
v___x_228_ = lean_unsigned_to_nat(2u);
v___x_229_ = l_Lean_Syntax_getArg(v_catch___184_, v___x_228_);
v___x_230_ = l_Lean_Syntax_isNone(v___x_229_);
if (v___x_230_ == 0)
{
uint8_t v___x_231_; 
lean_inc(v___x_229_);
v___x_231_ = l_Lean_Syntax_matchesNull(v___x_229_, v___x_228_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec(v___x_229_);
lean_dec(v___x_198_);
lean_dec(v_catch___184_);
lean_dec_ref(v_body_183_);
lean_dec_ref(v_lifter_182_);
v___x_232_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = l_Lean_Syntax_getArg(v___x_229_, v___x_197_);
lean_dec(v___x_229_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v_eType_x3f_211_ = v___x_234_;
v___y_212_ = v_a_185_;
v___y_213_ = v_a_186_;
v___y_214_ = v_a_187_;
v___y_215_ = v_a_188_;
v___y_216_ = v_a_189_;
v___y_217_ = v_a_190_;
v___y_218_ = v_a_191_;
goto v___jp_210_;
}
}
else
{
lean_object* v___x_235_; 
lean_dec(v___x_229_);
v___x_235_ = lean_box(0);
v_eType_x3f_211_ = v___x_235_;
v___y_212_ = v_a_185_;
v___y_213_ = v_a_186_;
v___y_214_ = v_a_187_;
v___y_215_ = v_a_188_;
v___y_216_ = v_a_189_;
v___y_217_ = v_a_190_;
v___y_218_ = v_a_191_;
goto v___jp_210_;
}
v___jp_199_:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = l_Lean_Elab_Term_mkExplicitBinder(v___x_198_, v___y_207_);
v___x_209_ = l_Lean_Elab_Term_elabBinder___redArg(v___x_208_, v___y_202_, v___y_203_, v___y_205_, v___y_206_, v___y_201_, v___y_204_, v___y_200_);
return v___x_209_;
}
v___jp_210_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___f_224_; 
v___x_219_ = lean_unsigned_to_nat(4u);
v___x_220_ = l_Lean_Syntax_getArg(v_catch___184_, v___x_219_);
lean_dec(v_catch___184_);
v___x_221_ = lean_box(v___x_194_);
v___f_222_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__0___boxed), 11, 2);
lean_closure_set(v___f_222_, 0, v___x_220_);
lean_closure_set(v___f_222_, 1, v___x_221_);
v___x_223_ = lean_box(v___x_194_);
lean_inc(v_eType_x3f_211_);
lean_inc_ref(v___y_212_);
lean_inc_ref(v_monadInfo_196_);
v___f_224_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___lam__1___boxed), 16, 8);
lean_closure_set(v___f_224_, 0, v_lifter_182_);
lean_closure_set(v___f_224_, 1, v___f_222_);
lean_closure_set(v___f_224_, 2, v___x_197_);
lean_closure_set(v___f_224_, 3, v___x_223_);
lean_closure_set(v___f_224_, 4, v_monadInfo_196_);
lean_closure_set(v___f_224_, 5, v_body_183_);
lean_closure_set(v___f_224_, 6, v___y_212_);
lean_closure_set(v___f_224_, 7, v_eType_x3f_211_);
if (lean_obj_tag(v_eType_x3f_211_) == 0)
{
uint8_t v___x_225_; lean_object* v___x_226_; 
v___x_225_ = 0;
v___x_226_ = l_Lean_mkHole(v___x_198_, v___x_225_);
v___y_200_ = v___y_218_;
v___y_201_ = v___y_216_;
v___y_202_ = v___f_224_;
v___y_203_ = v___y_213_;
v___y_204_ = v___y_217_;
v___y_205_ = v___y_214_;
v___y_206_ = v___y_215_;
v___y_207_ = v___x_226_;
goto v___jp_199_;
}
else
{
lean_object* v_val_227_; 
v_val_227_ = lean_ctor_get(v_eType_x3f_211_, 0);
lean_inc(v_val_227_);
lean_dec_ref(v_eType_x3f_211_);
v___y_200_ = v___y_218_;
v___y_201_ = v___y_216_;
v___y_202_ = v___f_224_;
v___y_203_ = v___y_213_;
v___y_204_ = v___y_217_;
v___y_205_ = v___y_214_;
v___y_206_ = v___y_215_;
v___y_207_ = v_val_227_;
goto v___jp_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___boxed(lean_object* v_lifter_236_, lean_object* v_body_237_, lean_object* v_catch___238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_lifter_236_, v_body_237_, v_catch___238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec_ref(v_a_239_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___lam__0(lean_object* v_trySeq_248_, uint8_t v___x_249_, lean_object* v_cont_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Elab_Do_elabDoSeq(v_trySeq_248_, v_cont_250_, v___x_249_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry___lam__0___boxed(lean_object* v_trySeq_260_, lean_object* v___x_261_, lean_object* v_cont_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
uint8_t v___x_15837__boxed_271_; lean_object* v_res_272_; 
v___x_15837__boxed_271_ = lean_unbox(v___x_261_);
v_res_272_ = l_Lean_Elab_Do_elabDoTry___lam__0(v_trySeq_260_, v___x_15837__boxed_271_, v_cont_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
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
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__3));
v___x_282_ = l_String_toRawSubstring_x27(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Array_mkArray0(lean_box(0));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(lean_object* v_a_316_, lean_object* v_as_317_, size_t v_i_318_, size_t v_stop_319_, lean_object* v_b_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___y_330_; uint8_t v___x_335_; 
v___x_335_ = lean_usize_dec_eq(v_i_318_, v_stop_319_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__1));
v___x_337_ = lean_array_uget_borrowed(v_as_317_, v_i_318_);
lean_inc(v___x_337_);
v___x_338_ = l_Lean_Syntax_isOfKind(v___x_337_, v___x_336_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_inc(v___x_337_);
lean_inc_ref(v_a_316_);
v___x_339_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_a_316_, v_b_320_, v___x_337_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
v___y_330_ = v___x_339_;
goto v___jp_329_;
}
else
{
lean_object* v_ref_340_; lean_object* v_quotContext_341_; lean_object* v_currMacroScope_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_ref_340_ = lean_ctor_get(v___y_326_, 5);
v_quotContext_341_ = lean_ctor_get(v___y_326_, 10);
v_currMacroScope_342_ = lean_ctor_get(v___y_326_, 11);
v___x_343_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = l_Lean_Syntax_getArg(v___x_337_, v___x_344_);
v___x_346_ = l_Lean_SourceInfo_fromRef(v_ref_340_, v___x_335_);
v___x_347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__2));
lean_inc_n(v___x_346_, 12);
v___x_348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__4);
v___x_350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__5));
lean_inc(v_currMacroScope_342_);
lean_inc(v_quotContext_341_);
v___x_351_ = l_Lean_addMacroScope(v_quotContext_341_, v___x_350_, v_currMacroScope_342_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_353_, 0, v___x_346_);
lean_ctor_set(v___x_353_, 1, v___x_349_);
lean_ctor_set(v___x_353_, 2, v___x_351_);
lean_ctor_set(v___x_353_, 3, v___x_352_);
v___x_354_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__7));
v___x_355_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__8);
v___x_356_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_356_, 0, v___x_346_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_355_);
v___x_357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__9));
v___x_358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_346_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__11));
v___x_360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__13));
v___x_361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__15));
v___x_362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__16));
v___x_363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_346_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__18));
lean_inc_ref(v___x_353_);
lean_inc_ref_n(v___x_356_, 5);
v___x_365_ = l_Lean_Syntax_node2(v___x_346_, v___x_364_, v___x_356_, v___x_353_);
v___x_366_ = l_Lean_Syntax_node1(v___x_346_, v___x_354_, v___x_365_);
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___closed__19));
v___x_368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_346_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = l_Lean_Syntax_node7(v___x_346_, v___x_361_, v___x_363_, v___x_356_, v___x_356_, v___x_356_, v___x_366_, v___x_368_, v___x_345_);
v___x_370_ = l_Lean_Syntax_node2(v___x_346_, v___x_360_, v___x_369_, v___x_356_);
v___x_371_ = l_Lean_Syntax_node1(v___x_346_, v___x_354_, v___x_370_);
v___x_372_ = l_Lean_Syntax_node1(v___x_346_, v___x_359_, v___x_371_);
v___x_373_ = l_Lean_Syntax_node5(v___x_346_, v___x_343_, v___x_348_, v___x_353_, v___x_356_, v___x_358_, v___x_372_);
lean_inc_ref(v_a_316_);
v___x_374_ = l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch(v_a_316_, v_b_320_, v___x_373_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
v___y_330_ = v___x_374_;
goto v___jp_329_;
}
}
else
{
lean_object* v___x_375_; 
lean_dec_ref(v_a_316_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_b_320_);
return v___x_375_;
}
v___jp_329_:
{
if (lean_obj_tag(v___y_330_) == 0)
{
lean_object* v_a_331_; size_t v___x_332_; size_t v___x_333_; 
v_a_331_ = lean_ctor_get(v___y_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref(v___y_330_);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_318_, v___x_332_);
v_i_318_ = v___x_333_;
v_b_320_ = v_a_331_;
goto _start;
}
else
{
lean_dec_ref(v_a_316_);
return v___y_330_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2___boxed(lean_object* v_a_376_, lean_object* v_as_377_, lean_object* v_i_378_, lean_object* v_stop_379_, lean_object* v_b_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
size_t v_i_boxed_389_; size_t v_stop_boxed_390_; lean_object* v_res_391_; 
v_i_boxed_389_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_stop_boxed_390_ = lean_unbox_usize(v_stop_379_);
lean_dec(v_stop_379_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(v_a_376_, v_as_377_, v_i_boxed_389_, v_stop_boxed_390_, v_b_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec_ref(v_as_377_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(lean_object* v_msgData_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; lean_object* v_env_399_; lean_object* v___x_400_; lean_object* v_mctx_401_; lean_object* v_lctx_402_; lean_object* v_options_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_398_ = lean_st_ref_get(v___y_396_);
v_env_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc_ref(v_env_399_);
lean_dec(v___x_398_);
v___x_400_ = lean_st_ref_get(v___y_394_);
v_mctx_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc_ref(v_mctx_401_);
lean_dec(v___x_400_);
v_lctx_402_ = lean_ctor_get(v___y_393_, 2);
v_options_403_ = lean_ctor_get(v___y_395_, 2);
lean_inc_ref(v_options_403_);
lean_inc_ref(v_lctx_402_);
v___x_404_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_404_, 0, v_env_399_);
lean_ctor_set(v___x_404_, 1, v_mctx_401_);
lean_ctor_set(v___x_404_, 2, v_lctx_402_);
lean_ctor_set(v___x_404_, 3, v_options_403_);
v___x_405_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_msgData_392_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4___boxed(lean_object* v_msgData_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msgData_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(lean_object* v_msg_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_ref_420_; lean_object* v___x_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_ref_420_ = lean_ctor_get(v___y_417_, 5);
v___x_421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3_spec__4(v_msg_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
lean_inc(v_ref_420_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v_ref_420_);
lean_ctor_set(v___x_426_, 1, v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 1);
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg___boxed(lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v_msg_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(lean_object* v_as_441_, size_t v_i_442_, size_t v_stop_443_, lean_object* v_b_444_){
_start:
{
lean_object* v___y_446_; uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_eq(v_i_442_, v_stop_443_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = lean_array_uget_borrowed(v_as_441_, v_i_442_);
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch___closed__4));
lean_inc(v___x_451_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
v___y_446_ = v_b_444_;
goto v___jp_445_;
}
else
{
lean_object* v___x_454_; lean_object* v_x_455_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v_x_455_ = l_Lean_Syntax_getArg(v___x_451_, v___x_454_);
v___x_458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___closed__1));
lean_inc(v_x_455_);
v___x_459_ = l_Lean_Syntax_isOfKind(v_x_455_, v___x_458_);
if (v___x_459_ == 0)
{
lean_dec(v_x_455_);
v___y_446_ = v_b_444_;
goto v___jp_445_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(2u);
v___x_461_ = l_Lean_Syntax_getArg(v___x_451_, v___x_460_);
v___x_462_ = l_Lean_Syntax_isNone(v___x_461_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; 
v___x_463_ = l_Lean_Syntax_matchesNull(v___x_461_, v___x_460_);
if (v___x_463_ == 0)
{
lean_dec(v_x_455_);
v___y_446_ = v_b_444_;
goto v___jp_445_;
}
else
{
goto v___jp_456_;
}
}
else
{
lean_dec(v___x_461_);
goto v___jp_456_;
}
}
v___jp_456_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_array_push(v_b_444_, v_x_455_);
v___y_446_ = v___x_457_;
goto v___jp_445_;
}
}
}
else
{
return v_b_444_;
}
v___jp_445_:
{
size_t v___x_447_; size_t v___x_448_; 
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_442_, v___x_447_);
v_i_442_ = v___x_448_;
v_b_444_ = v___y_446_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1___boxed(lean_object* v_as_464_, lean_object* v_i_465_, lean_object* v_stop_466_, lean_object* v_b_467_){
_start:
{
size_t v_i_boxed_468_; size_t v_stop_boxed_469_; lean_object* v_res_470_; 
v_i_boxed_468_ = lean_unbox_usize(v_i_465_);
lean_dec(v_i_465_);
v_stop_boxed_469_ = lean_unbox_usize(v_stop_466_);
lean_dec(v_stop_466_);
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(v_as_464_, v_i_boxed_468_, v_stop_boxed_469_, v_b_467_);
lean_dec_ref(v_as_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1(lean_object* v_as_473_, lean_object* v_start_474_, lean_object* v_stop_475_){
_start:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___closed__0));
v___x_477_ = lean_nat_dec_lt(v_start_474_, v_stop_475_);
if (v___x_477_ == 0)
{
return v___x_476_;
}
else
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_array_get_size(v_as_473_);
v___x_479_ = lean_nat_dec_le(v_stop_475_, v___x_478_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = lean_nat_dec_lt(v_start_474_, v___x_478_);
if (v___x_480_ == 0)
{
return v___x_476_;
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_usize_of_nat(v_start_474_);
v___x_482_ = lean_usize_of_nat(v___x_478_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(v_as_473_, v___x_481_, v___x_482_, v___x_476_);
return v___x_483_;
}
}
else
{
size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_usize_of_nat(v_start_474_);
v___x_485_ = lean_usize_of_nat(v_stop_475_);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1_spec__1(v_as_473_, v___x_484_, v___x_485_, v___x_476_);
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1___boxed(lean_object* v_as_487_, lean_object* v_start_488_, lean_object* v_stop_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1(v_as_487_, v_start_488_, v_stop_489_);
lean_dec(v_stop_489_);
lean_dec(v_start_488_);
lean_dec_ref(v_as_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(size_t v_sz_491_, size_t v_i_492_, lean_object* v_bs_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_lt(v_i_492_, v_sz_491_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_bs_493_);
return v___x_495_;
}
else
{
lean_object* v_v_496_; lean_object* v___x_497_; lean_object* v_bs_x27_498_; size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; 
v_v_496_ = lean_array_uget(v_bs_493_, v_i_492_);
v___x_497_ = lean_unsigned_to_nat(0u);
v_bs_x27_498_ = lean_array_uset(v_bs_493_, v_i_492_, v___x_497_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_492_, v___x_499_);
v___x_501_ = lean_array_uset(v_bs_x27_498_, v_i_492_, v_v_496_);
v_i_492_ = v___x_500_;
v_bs_493_ = v___x_501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0___boxed(lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_bs_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_507_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_boxed_506_, v_i_boxed_507_, v_bs_505_);
return v_res_508_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoTry___closed__11(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__10));
v___x_529_ = l_Lean_stringToMessageData(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoTry(lean_object* v_stx_536_, lean_object* v_dec_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___y_547_; lean_object* v_body_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___x_567_; uint8_t v___x_568_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; 
v___x_567_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__1));
lean_inc(v_stx_536_);
v___x_568_ = l_Lean_Syntax_isOfKind(v_stx_536_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_633_; 
lean_dec_ref(v_dec_537_);
lean_dec(v_stx_536_);
v___x_633_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; size_t v_sz_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_634_ = lean_unsigned_to_nat(2u);
v___x_635_ = l_Lean_Syntax_getArg(v_stx_536_, v___x_634_);
v___x_636_ = l_Lean_Syntax_getArgs(v___x_635_);
lean_dec(v___x_635_);
v_sz_637_ = lean_array_size(v___x_636_);
v___x_638_ = ((size_t)0ULL);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoTry_spec__0(v_sz_637_, v___x_638_, v___x_636_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v_dec_537_);
lean_dec(v_stx_536_);
v___x_640_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_640_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_747_; 
v_val_641_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_747_ == 0)
{
v___x_643_ = v___x_639_;
v_isShared_644_ = v_isSharedCheck_747_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v___x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_747_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___y_697_; lean_object* v___x_708_; lean_object* v_trySeq_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v_finSeq_x3f_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_unsigned_to_nat(1u);
v_trySeq_709_ = l_Lean_Syntax_getArg(v_stx_536_, v___x_708_);
v___x_710_ = lean_box(v___x_568_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoTry___lam__0___boxed), 11, 2);
lean_closure_set(v___f_711_, 0, v_trySeq_709_);
lean_closure_set(v___f_711_, 1, v___x_710_);
v___x_733_ = lean_unsigned_to_nat(3u);
v___x_734_ = l_Lean_Syntax_getArg(v_stx_536_, v___x_733_);
v___x_735_ = l_Lean_Syntax_isNone(v___x_734_);
if (v___x_735_ == 0)
{
uint8_t v___x_736_; 
lean_inc(v___x_734_);
v___x_736_ = l_Lean_Syntax_matchesNull(v___x_734_, v___x_708_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec(v___x_734_);
lean_dec_ref(v___f_711_);
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec_ref(v_dec_537_);
lean_dec(v_stx_536_);
v___x_737_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = l_Lean_Syntax_getArg(v___x_734_, v___x_645_);
lean_dec(v___x_734_);
v___x_739_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__13));
lean_inc(v___x_738_);
v___x_740_ = l_Lean_Syntax_isOfKind(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v___x_738_);
lean_dec_ref(v___f_711_);
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
lean_dec_ref(v_dec_537_);
lean_dec(v_stx_536_);
v___x_741_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_TryCatch_0__Lean_Elab_Do_elabDoCatch_spec__0___redArg();
return v___x_741_;
}
else
{
lean_object* v_finSeq_x3f_742_; lean_object* v___x_744_; 
v_finSeq_x3f_742_ = l_Lean_Syntax_getArg(v___x_738_, v___x_708_);
lean_dec(v___x_738_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_finSeq_x3f_742_);
v___x_744_ = v___x_643_;
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
v_finSeq_x3f_713_ = v___x_744_;
v___y_714_ = v_a_538_;
v___y_715_ = v_a_539_;
v___y_716_ = v_a_540_;
v___y_717_ = v_a_541_;
v___y_718_ = v_a_542_;
v___y_719_ = v_a_543_;
v___y_720_ = v_a_544_;
goto v___jp_712_;
}
}
}
}
else
{
lean_object* v___x_746_; 
lean_dec(v___x_734_);
lean_del_object(v___x_643_);
v___x_746_ = lean_box(0);
v_finSeq_x3f_713_ = v___x_746_;
v___y_714_ = v_a_538_;
v___y_715_ = v_a_539_;
v___y_716_ = v_a_540_;
v___y_717_ = v_a_541_;
v___y_718_ = v_a_542_;
v___y_719_ = v_a_543_;
v___y_720_ = v_a_544_;
goto v___jp_712_;
}
v___jp_646_:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Elab_Do_inferControlInfoElem(v_stx_536_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
v___x_659_ = l_Lean_Elab_Do_ControlLifter_ofCont(v_a_658_, v_dec_537_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v_a_658_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc_n(v_a_660_, 2);
lean_dec_ref(v___x_659_);
v___x_661_ = l_Lean_Elab_Do_ControlLifter_lift(v_a_660_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v_monadInfo_663_; uint8_t v___x_664_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
v_monadInfo_663_ = lean_ctor_get(v___y_650_, 0);
v___x_664_ = lean_nat_dec_lt(v___x_645_, v___y_647_);
if (v___x_664_ == 0)
{
lean_dec(v_a_662_);
lean_dec(v___y_647_);
lean_dec(v_val_641_);
v___y_570_ = v___y_651_;
v___y_571_ = v___y_655_;
v___y_572_ = v___y_650_;
v___y_573_ = v___y_648_;
v___y_574_ = v_monadInfo_663_;
v___y_575_ = v___y_656_;
v___y_576_ = v___y_653_;
v___y_577_ = v___y_652_;
v___y_578_ = v_a_660_;
v___y_579_ = v___y_654_;
v___y_580_ = v___x_661_;
goto v___jp_569_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_le(v___y_647_, v___y_647_);
if (v___x_665_ == 0)
{
if (v___x_664_ == 0)
{
lean_dec(v_a_662_);
lean_dec(v___y_647_);
lean_dec(v_val_641_);
v___y_570_ = v___y_651_;
v___y_571_ = v___y_655_;
v___y_572_ = v___y_650_;
v___y_573_ = v___y_648_;
v___y_574_ = v_monadInfo_663_;
v___y_575_ = v___y_656_;
v___y_576_ = v___y_653_;
v___y_577_ = v___y_652_;
v___y_578_ = v_a_660_;
v___y_579_ = v___y_654_;
v___y_580_ = v___x_661_;
goto v___jp_569_;
}
else
{
size_t v___x_666_; lean_object* v___x_667_; 
lean_dec_ref(v___x_661_);
v___x_666_ = lean_usize_of_nat(v___y_647_);
lean_dec(v___y_647_);
lean_inc(v_a_660_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(v_a_660_, v_val_641_, v___x_638_, v___x_666_, v_a_662_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v_val_641_);
v___y_570_ = v___y_651_;
v___y_571_ = v___y_655_;
v___y_572_ = v___y_650_;
v___y_573_ = v___y_648_;
v___y_574_ = v_monadInfo_663_;
v___y_575_ = v___y_656_;
v___y_576_ = v___y_653_;
v___y_577_ = v___y_652_;
v___y_578_ = v_a_660_;
v___y_579_ = v___y_654_;
v___y_580_ = v___x_667_;
goto v___jp_569_;
}
}
else
{
size_t v___x_668_; lean_object* v___x_669_; 
lean_dec_ref(v___x_661_);
v___x_668_ = lean_usize_of_nat(v___y_647_);
lean_dec(v___y_647_);
lean_inc(v_a_660_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoTry_spec__2(v_a_660_, v_val_641_, v___x_638_, v___x_668_, v_a_662_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v_val_641_);
v___y_570_ = v___y_651_;
v___y_571_ = v___y_655_;
v___y_572_ = v___y_650_;
v___y_573_ = v___y_648_;
v___y_574_ = v_monadInfo_663_;
v___y_575_ = v___y_656_;
v___y_576_ = v___y_653_;
v___y_577_ = v___y_652_;
v___y_578_ = v_a_660_;
v___y_579_ = v___y_654_;
v___y_580_ = v___x_669_;
goto v___jp_569_;
}
}
}
else
{
lean_dec(v_a_660_);
lean_dec(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v_val_641_);
return v___x_661_;
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v_val_641_);
v_a_670_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_659_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_659_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v_val_641_);
lean_dec_ref(v_dec_537_);
v_a_678_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_657_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_657_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
v___jp_686_:
{
if (v___y_697_ == 0)
{
v___y_647_ = v___y_687_;
v___y_648_ = v___y_691_;
v___y_649_ = v___y_690_;
v___y_650_ = v___y_696_;
v___y_651_ = v___y_692_;
v___y_652_ = v___y_695_;
v___y_653_ = v___y_694_;
v___y_654_ = v___y_689_;
v___y_655_ = v___y_688_;
v___y_656_ = v___y_693_;
goto v___jp_646_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_687_);
lean_dec(v_val_641_);
lean_dec_ref(v_dec_537_);
lean_dec(v_stx_536_);
v___x_698_ = lean_obj_once(&l_Lean_Elab_Do_elabDoTry___closed__11, &l_Lean_Elab_Do_elabDoTry___closed__11_once, _init_l_Lean_Elab_Do_elabDoTry___closed__11);
v___x_699_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoTry_spec__3___redArg(v___x_698_, v___y_694_, v___y_689_, v___y_688_, v___y_693_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
v___jp_712_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = lean_array_get_size(v_val_641_);
v___x_722_ = l_Array_filterMapM___at___00Lean_Elab_Do_elabDoTry_spec__1(v_val_641_, v___x_645_, v___x_721_);
v___x_723_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_722_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec_ref(v___x_722_);
if (lean_obj_tag(v___x_723_) == 0)
{
uint8_t v___x_724_; 
lean_dec_ref(v___x_723_);
v___x_724_ = lean_nat_dec_eq(v___x_721_, v___x_645_);
if (v___x_724_ == 0)
{
v___y_687_ = v___x_721_;
v___y_688_ = v___y_719_;
v___y_689_ = v___y_718_;
v___y_690_ = v___f_711_;
v___y_691_ = v_finSeq_x3f_713_;
v___y_692_ = v___y_715_;
v___y_693_ = v___y_720_;
v___y_694_ = v___y_717_;
v___y_695_ = v___y_716_;
v___y_696_ = v___y_714_;
v___y_697_ = v___x_724_;
goto v___jp_686_;
}
else
{
if (lean_obj_tag(v_finSeq_x3f_713_) == 0)
{
v___y_687_ = v___x_721_;
v___y_688_ = v___y_719_;
v___y_689_ = v___y_718_;
v___y_690_ = v___f_711_;
v___y_691_ = v_finSeq_x3f_713_;
v___y_692_ = v___y_715_;
v___y_693_ = v___y_720_;
v___y_694_ = v___y_717_;
v___y_695_ = v___y_716_;
v___y_696_ = v___y_714_;
v___y_697_ = v___x_724_;
goto v___jp_686_;
}
else
{
v___y_647_ = v___x_721_;
v___y_648_ = v_finSeq_x3f_713_;
v___y_649_ = v___f_711_;
v___y_650_ = v___y_714_;
v___y_651_ = v___y_715_;
v___y_652_ = v___y_716_;
v___y_653_ = v___y_717_;
v___y_654_ = v___y_718_;
v___y_655_ = v___y_719_;
v___y_656_ = v___y_720_;
goto v___jp_646_;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_finSeq_x3f_713_);
lean_dec_ref(v___f_711_);
lean_dec(v_val_641_);
lean_dec_ref(v_dec_537_);
lean_dec(v_stx_536_);
v_a_725_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_723_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_723_);
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
v___jp_546_:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Elab_Do_ControlLifter_restoreCont(v___y_547_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_558_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
lean_dec_ref(v___x_556_);
v___x_558_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_557_, v_body_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec_ref(v_body_548_);
v_a_559_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_556_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_556_);
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
if (lean_obj_tag(v___y_580_) == 0)
{
if (lean_obj_tag(v___y_573_) == 0)
{
lean_object* v_a_581_; 
v_a_581_ = lean_ctor_get(v___y_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___y_580_);
v___y_547_ = v___y_578_;
v_body_548_ = v_a_581_;
v___y_549_ = v___y_572_;
v___y_550_ = v___y_570_;
v___y_551_ = v___y_577_;
v___y_552_ = v___y_576_;
v___y_553_ = v___y_579_;
v___y_554_ = v___y_571_;
v___y_555_ = v___y_575_;
goto v___jp_546_;
}
else
{
lean_object* v_a_582_; lean_object* v_val_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v_a_582_ = lean_ctor_get(v___y_580_, 0);
lean_inc(v_a_582_);
lean_dec_ref(v___y_580_);
v_val_583_ = lean_ctor_get(v___y_573_, 0);
lean_inc(v_val_583_);
lean_dec_ref(v___y_573_);
v___x_584_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__3));
v___x_585_ = 0;
v___x_586_ = l_Lean_Elab_Do_mkFreshResultType___redArg(v___x_584_, v___x_585_, v___y_572_, v___y_576_, v___y_579_, v___y_571_, v___y_575_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref(v___x_586_);
v___x_588_ = l_Lean_Expr_mvarId_x21(v_a_587_);
lean_inc(v_val_583_);
v___x_589_ = l_Lean_Elab_Term_registerMVarErrorHoleInfo___redArg(v___x_588_, v_val_583_, v___y_577_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; 
lean_dec_ref(v___x_589_);
lean_inc(v_a_587_);
v___x_590_ = l_Lean_Elab_Do_DoElemCont_mkPure___redArg(v_a_587_, v___y_571_, v___y_575_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref(v___x_590_);
v___x_592_ = lean_box(v___x_568_);
v___x_593_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_593_, 0, v_val_583_);
lean_closure_set(v___x_593_, 1, v_a_591_);
lean_closure_set(v___x_593_, 2, v___x_592_);
lean_inc(v_a_587_);
v___x_594_ = l_Lean_Elab_Do_enterFinally(v_a_587_, v___x_593_, v___y_572_, v___y_570_, v___y_577_, v___y_576_, v___y_579_, v___y_571_, v___y_575_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v_m_596_; lean_object* v_u_597_; lean_object* v_v_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref(v___x_594_);
v_m_596_ = lean_ctor_get(v___y_574_, 0);
v_u_597_ = lean_ctor_get(v___y_574_, 1);
v_v_598_ = lean_ctor_get(v___y_574_, 2);
v___x_599_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__5));
v___x_600_ = lean_box(0);
lean_inc(v_v_598_);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v_v_598_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_inc(v_u_597_);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v_u_597_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc_ref(v___x_602_);
v___x_603_ = l_Lean_mkConst(v___x_599_, v___x_602_);
lean_inc_ref(v_m_596_);
v___x_604_ = l_Lean_Expr_app___override(v___x_603_, v_m_596_);
v___x_605_ = lean_box(0);
v___x_606_ = l_Lean_Elab_Term_mkInstMVar(v___x_604_, v___x_605_, v___y_570_, v___y_577_, v___y_576_, v___y_579_, v___y_571_, v___y_575_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__7));
lean_inc_ref(v___x_602_);
v___x_609_ = l_Lean_mkConst(v___x_608_, v___x_602_);
lean_inc_ref(v_m_596_);
v___x_610_ = l_Lean_Expr_app___override(v___x_609_, v_m_596_);
v___x_611_ = l_Lean_Elab_Term_mkInstMVar(v___x_610_, v___x_605_, v___y_570_, v___y_577_, v___y_576_, v___y_579_, v___y_571_, v___y_575_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v_liftedDoBlockResultType_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref(v___x_611_);
v_liftedDoBlockResultType_613_ = lean_ctor_get(v___y_578_, 5);
v___x_614_ = ((lean_object*)(l_Lean_Elab_Do_elabDoTry___closed__9));
v___x_615_ = l_Lean_mkConst(v___x_614_, v___x_602_);
lean_inc_ref(v_liftedDoBlockResultType_613_);
lean_inc_ref(v_m_596_);
v___x_616_ = l_Lean_mkApp7(v___x_615_, v_m_596_, v_liftedDoBlockResultType_613_, v_a_587_, v_a_607_, v_a_612_, v_a_582_, v_a_595_);
v___y_547_ = v___y_578_;
v_body_548_ = v___x_616_;
v___y_549_ = v___y_572_;
v___y_550_ = v___y_570_;
v___y_551_ = v___y_577_;
v___y_552_ = v___y_576_;
v___y_553_ = v___y_579_;
v___y_554_ = v___y_571_;
v___y_555_ = v___y_575_;
goto v___jp_546_;
}
else
{
lean_dec(v_a_607_);
lean_dec_ref(v___x_602_);
lean_dec(v_a_595_);
lean_dec(v_a_587_);
lean_dec(v_a_582_);
lean_dec_ref(v___y_578_);
return v___x_611_;
}
}
else
{
lean_dec_ref(v___x_602_);
lean_dec(v_a_595_);
lean_dec(v_a_587_);
lean_dec(v_a_582_);
lean_dec_ref(v___y_578_);
return v___x_606_;
}
}
else
{
lean_dec(v_a_587_);
lean_dec(v_a_582_);
lean_dec_ref(v___y_578_);
return v___x_594_;
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_a_587_);
lean_dec(v_val_583_);
lean_dec(v_a_582_);
lean_dec_ref(v___y_578_);
v_a_617_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_590_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_590_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_a_587_);
lean_dec(v_val_583_);
lean_dec(v_a_582_);
lean_dec_ref(v___y_578_);
v_a_625_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_589_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_589_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_dec(v_val_583_);
lean_dec(v_a_582_);
lean_dec_ref(v___y_578_);
return v___x_586_;
}
}
}
else
{
lean_dec_ref(v___y_578_);
lean_dec(v___y_573_);
return v___y_580_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_TryCatch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
