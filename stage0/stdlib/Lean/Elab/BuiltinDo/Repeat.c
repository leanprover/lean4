// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Repeat
// Imports: public import Lean.Elab.BuiltinDo.Basic meta import Lean.Parser.Do import Init.Repeat
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Do_mkPUnit___redArg(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_enterLoopBody___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instCCPOPi"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 4, 22, 67, 25, 201, 243, 223)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toCCPO"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MonadRepeat"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 97, 248, 121, 224, 7, 254, 148)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "defaultInstance"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 97, 248, 121, 224, 7, 254, 148)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 12, 160, 85, 174, 206, 107, 5)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__6_value),LEAN_SCALAR_PTR_LITERAL(113, 209, 180, 93, 84, 117, 67, 110)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__5_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "a terminal repeat loop requires the type to be nonempty"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__11;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Elab.BuiltinDo.Repeat"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "_private.Lean.Elab.BuiltinDo.Repeat.0.Lean.Elab.Do.elabDoRepeat.mkCont"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Invalid control info, expected no break"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__2;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 111, .m_capacity = 111, .m_length = 110, .m_data = "Invalid break from repeat loop, repeat loop is in a terminal position and has an expected type different from "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__5;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__7;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__8_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "__break"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 215, 125, 189, 6, 116, 156, 190)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__r"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(38, 26, 183, 93, 43, 136, 227, 87)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__1___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "__continue"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 5, 59, 16, 185, 44, 86, 109)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Repeat"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "loop"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoRepeat_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoRepeat_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doRepeat"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 14, 140, 183, 155, 194, 124, 178)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__3_value;
static const lean_array_object l_Lean_Elab_Do_elabDoRepeat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabDoRepeat"};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(65, 84, 114, 24, 25, 111, 206, 161)}};
static const lean_object* l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v_b_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_11_ = lean_apply_9(v_k_1_, v_b_5_, v___y_2_, v___y_3_, v___y_4_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___lam__0___boxed(lean_object* v_k_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v_b_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___lam__0(v_k_12_, v___y_13_, v___y_14_, v___y_15_, v_b_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg(lean_object* v_name_23_, uint8_t v_bi_24_, lean_object* v_type_25_, lean_object* v_k_26_, uint8_t v_kind_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___f_36_; lean_object* v___x_37_; 
lean_inc(v___y_30_);
lean_inc_ref(v___y_29_);
lean_inc_ref(v___y_28_);
v___f_36_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_36_, 0, v_k_26_);
lean_closure_set(v___f_36_, 1, v___y_28_);
lean_closure_set(v___f_36_, 2, v___y_29_);
lean_closure_set(v___f_36_, 3, v___y_30_);
v___x_37_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_23_, v_bi_24_, v_type_25_, v___f_36_, v_kind_27_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
if (lean_obj_tag(v___x_37_) == 0)
{
return v___x_37_;
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_37_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_37_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___boxed(lean_object* v_name_46_, lean_object* v_bi_47_, lean_object* v_type_48_, lean_object* v_k_49_, lean_object* v_kind_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
uint8_t v_bi_boxed_59_; uint8_t v_kind_boxed_60_; lean_object* v_res_61_; 
v_bi_boxed_59_ = lean_unbox(v_bi_47_);
v_kind_boxed_60_ = lean_unbox(v_kind_50_);
v_res_61_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg(v_name_46_, v_bi_boxed_59_, v_type_48_, v_k_49_, v_kind_boxed_60_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0(lean_object* v_00_u03b1_62_, lean_object* v_name_63_, uint8_t v_bi_64_, lean_object* v_type_65_, lean_object* v_k_66_, uint8_t v_kind_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg(v_name_63_, v_bi_64_, v_type_65_, v_k_66_, v_kind_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___boxed(lean_object* v_00_u03b1_77_, lean_object* v_name_78_, lean_object* v_bi_79_, lean_object* v_type_80_, lean_object* v_k_81_, lean_object* v_kind_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
uint8_t v_bi_boxed_91_; uint8_t v_kind_boxed_92_; lean_object* v_res_93_; 
v_bi_boxed_91_ = lean_unbox(v_bi_79_);
v_kind_boxed_92_ = lean_unbox(v_kind_82_);
v_res_93_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0(v_00_u03b1_77_, v_name_78_, v_bi_boxed_91_, v_type_80_, v_k_81_, v_kind_boxed_92_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___boxed(lean_object* v_body_101_, lean_object* v_a_102_, lean_object* v_binderName_103_, lean_object* v_binderType_104_, lean_object* v_binderInfo_105_, lean_object* v_brk_x3f_106_, lean_object* v_var_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
uint8_t v_binderInfo_4996__boxed_116_; lean_object* v_res_117_; 
v_binderInfo_4996__boxed_116_ = lean_unbox(v_binderInfo_105_);
v_res_117_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0(v_body_101_, v_a_102_, v_binderName_103_, v_binderType_104_, v_binderInfo_4996__boxed_116_, v_brk_x3f_106_, v_var_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_117_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__11(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__10));
v___x_137_ = l_Lean_MessageData_ofFormat(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__12(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__11, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__11_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__11);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO(lean_object* v_ty_140_, lean_object* v_brk_x3f_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
if (lean_obj_tag(v_ty_140_) == 7)
{
lean_object* v_binderName_150_; lean_object* v_binderType_151_; lean_object* v_body_152_; uint8_t v_binderInfo_153_; lean_object* v___x_154_; 
v_binderName_150_ = lean_ctor_get(v_ty_140_, 0);
lean_inc(v_binderName_150_);
v_binderType_151_ = lean_ctor_get(v_ty_140_, 1);
lean_inc_ref_n(v_binderType_151_, 2);
v_body_152_ = lean_ctor_get(v_ty_140_, 2);
lean_inc_ref(v_body_152_);
v_binderInfo_153_ = lean_ctor_get_uint8(v_ty_140_, sizeof(void*)*3 + 8);
lean_dec_ref(v_ty_140_);
v___x_154_ = l_Lean_Meta_getLevel(v_binderType_151_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___f_157_; uint8_t v___x_158_; lean_object* v___x_159_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
v___x_156_ = lean_box(v_binderInfo_153_);
lean_inc_ref(v_binderType_151_);
lean_inc(v_binderName_150_);
v___f_157_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___boxed), 15, 6);
lean_closure_set(v___f_157_, 0, v_body_152_);
lean_closure_set(v___f_157_, 1, v_a_155_);
lean_closure_set(v___f_157_, 2, v_binderName_150_);
lean_closure_set(v___f_157_, 3, v_binderType_151_);
lean_closure_set(v___f_157_, 4, v___x_156_);
lean_closure_set(v___f_157_, 5, v_brk_x3f_141_);
v___x_158_ = 0;
v___x_159_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg(v_binderName_150_, v_binderInfo_153_, v_binderType_151_, v___f_157_, v___x_158_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
return v___x_159_;
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_body_152_);
lean_dec_ref(v_binderType_151_);
lean_dec(v_binderName_150_);
lean_dec(v_brk_x3f_141_);
v_a_160_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_154_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_154_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
else
{
lean_object* v_monadInfo_168_; lean_object* v_doBlockResultType_169_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v_inst_175_; lean_object* v_nonempty_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; 
v_monadInfo_168_ = lean_ctor_get(v_a_142_, 0);
v_doBlockResultType_169_ = lean_ctor_get(v_a_142_, 3);
if (lean_obj_tag(v_brk_x3f_141_) == 1)
{
lean_object* v_val_212_; lean_object* v_v_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_val_212_ = lean_ctor_get(v_brk_x3f_141_, 0);
lean_inc(v_val_212_);
lean_dec_ref(v_brk_x3f_141_);
v_v_213_ = lean_ctor_get(v_monadInfo_168_, 2);
v___x_214_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__7));
lean_inc(v_v_213_);
v___x_215_ = l_Lean_Level_succ___override(v_v_213_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = l_Lean_Expr_const___override(v___x_214_, v___x_217_);
v___x_219_ = l_Lean_mkAppB(v___x_218_, v_ty_140_, v_val_212_);
v_nonempty_182_ = v___x_219_;
v___y_183_ = v_a_145_;
v___y_184_ = v_a_146_;
v___y_185_ = v_a_147_;
v___y_186_ = v_a_148_;
goto v___jp_181_;
}
else
{
lean_object* v_v_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v_brk_x3f_141_);
v_v_220_ = lean_ctor_get(v_monadInfo_168_, 2);
v___x_221_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__8));
lean_inc(v_v_220_);
v___x_222_ = l_Lean_Level_succ___override(v_v_220_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_222_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = l_Lean_Expr_const___override(v___x_221_, v___x_224_);
v___x_226_ = l_Lean_Expr_app___override(v___x_225_, v_ty_140_);
v___x_227_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__12, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__12_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__12);
v___x_228_ = l_Lean_Elab_Term_mkInstMVar(v___x_226_, v___x_227_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref(v___x_228_);
v_nonempty_182_ = v_a_229_;
v___y_183_ = v_a_145_;
v___y_184_ = v_a_146_;
v___y_185_ = v_a_147_;
v___y_186_ = v_a_148_;
goto v___jp_181_;
}
else
{
return v___x_228_;
}
}
v___jp_170_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_176_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__0));
lean_inc_ref(v___y_171_);
v___x_177_ = l_Lean_Name_mkStr2(v___y_171_, v___x_176_);
v___x_178_ = l_Lean_Expr_const___override(v___x_177_, v___y_174_);
lean_inc_ref(v_doBlockResultType_169_);
v___x_179_ = l_Lean_mkApp4(v___x_178_, v___y_172_, v_inst_175_, v_doBlockResultType_169_, v___y_173_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
v___jp_181_:
{
lean_object* v_m_187_; lean_object* v_u_188_; lean_object* v_v_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_m_187_ = lean_ctor_get(v_monadInfo_168_, 0);
v_u_188_ = lean_ctor_get(v_monadInfo_168_, 1);
v_v_189_ = lean_ctor_get(v_monadInfo_168_, 2);
v___x_190_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__1));
v___x_191_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__2));
v___x_192_ = lean_box(0);
lean_inc(v_v_189_);
v___x_193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_193_, 0, v_v_189_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
lean_inc(v_u_188_);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v_u_188_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
lean_inc_ref(v___x_194_);
v___x_195_ = l_Lean_Expr_const___override(v___x_191_, v___x_194_);
lean_inc_ref(v_m_187_);
v___x_196_ = l_Lean_Expr_app___override(v___x_195_, v_m_187_);
v___x_197_ = lean_box(0);
v___x_198_ = l_Lean_Meta_trySynthInstance(v___x_196_, v___x_197_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v___x_198_);
if (lean_obj_tag(v_a_199_) == 1)
{
lean_object* v_a_200_; 
v_a_200_ = lean_ctor_get(v_a_199_, 0);
lean_inc(v_a_200_);
lean_dec_ref(v_a_199_);
lean_inc_ref(v_m_187_);
v___y_171_ = v___x_190_;
v___y_172_ = v_m_187_;
v___y_173_ = v_nonempty_182_;
v___y_174_ = v___x_194_;
v_inst_175_ = v_a_200_;
goto v___jp_170_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec(v_a_199_);
v___x_201_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___closed__4));
lean_inc_ref(v___x_194_);
v___x_202_ = l_Lean_Expr_const___override(v___x_201_, v___x_194_);
lean_inc_ref_n(v_m_187_, 2);
v___x_203_ = l_Lean_Expr_app___override(v___x_202_, v_m_187_);
v___y_171_ = v___x_190_;
v___y_172_ = v_m_187_;
v___y_173_ = v_nonempty_182_;
v___y_174_ = v___x_194_;
v_inst_175_ = v___x_203_;
goto v___jp_170_;
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v___x_194_);
lean_dec_ref(v_nonempty_182_);
v_a_204_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_198_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_198_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0(lean_object* v_body_230_, lean_object* v_a_231_, lean_object* v_binderName_232_, lean_object* v_binderType_233_, uint8_t v_binderInfo_234_, lean_object* v_brk_x3f_235_, lean_object* v_var_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_expr_instantiate1(v_body_230_, v_var_236_);
lean_inc_ref(v___x_245_);
v___x_246_ = l_Lean_Meta_getLevel(v___x_245_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___y_249_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref(v___x_246_);
if (lean_obj_tag(v_brk_x3f_235_) == 0)
{
v___y_249_ = v_brk_x3f_235_;
goto v___jp_248_;
}
else
{
lean_object* v_val_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_val_274_ = lean_ctor_get(v_brk_x3f_235_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_brk_x3f_235_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v_brk_x3f_235_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_val_274_);
lean_dec(v_brk_x3f_235_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_inc_ref(v_var_236_);
v___x_278_ = l_Lean_Expr_app___override(v_val_274_, v_var_236_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_278_);
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
v___y_249_ = v___x_280_;
goto v___jp_248_;
}
}
}
v___jp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO(v___x_245_, v___y_249_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; uint8_t v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v___x_250_);
v___x_252_ = lean_unsigned_to_nat(1u);
v___x_253_ = lean_mk_empty_array_with_capacity(v___x_252_);
v___x_254_ = lean_array_push(v___x_253_, v_var_236_);
v___x_255_ = 0;
v___x_256_ = 1;
v___x_257_ = 1;
v___x_258_ = l_Lean_Meta_mkLambdaFVars(v___x_254_, v_a_251_, v___x_255_, v___x_256_, v___x_255_, v___x_256_, v___x_257_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec_ref(v___x_254_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_273_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_273_ == 0)
{
v___x_261_ = v___x_258_;
v_isShared_262_ = v_isSharedCheck_273_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_273_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__3));
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v_a_247_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_266_, 0, v_a_231_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = l_Lean_Expr_const___override(v___x_263_, v___x_266_);
lean_inc_ref(v_binderType_233_);
v___x_268_ = l_Lean_Expr_lam___override(v_binderName_232_, v_binderType_233_, v_body_230_, v_binderInfo_234_);
v___x_269_ = l_Lean_mkApp3(v___x_267_, v_binderType_233_, v___x_268_, v_a_259_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_269_);
v___x_271_ = v___x_261_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
else
{
lean_dec(v_a_247_);
lean_dec_ref(v_binderType_233_);
lean_dec(v_binderName_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_body_230_);
return v___x_258_;
}
}
else
{
lean_dec(v_a_247_);
lean_dec_ref(v_var_236_);
lean_dec_ref(v_binderType_233_);
lean_dec(v_binderName_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_body_230_);
return v___x_250_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec_ref(v___x_245_);
lean_dec_ref(v_var_236_);
lean_dec(v_brk_x3f_235_);
lean_dec_ref(v_binderType_233_);
lean_dec(v_binderName_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_body_230_);
v_a_283_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_246_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_246_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___boxed(lean_object* v_ty_291_, lean_object* v_brk_x3f_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO(v_ty_291_, v_brk_x3f_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec_ref(v_a_293_);
return v_res_301_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0___closed__0(void){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v___f_313_; lean_object* v___x_2344__overap_314_; lean_object* v___x_315_; 
v___x_312_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0___closed__0, &l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0___closed__0);
v___f_313_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_313_, 0, v___x_312_);
v___x_2344__overap_314_ = lean_panic_fn_borrowed(v___f_313_, v_msg_303_);
lean_dec_ref(v___f_313_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc_ref(v___y_304_);
v___x_315_ = lean_apply_8(v___x_2344__overap_314_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, lean_box(0));
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0___boxed(lean_object* v_msg_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0(v_msg_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_325_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__3(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_box(0);
v___x_332_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__2));
v___x_333_ = l_Lean_mkConst(v___x_332_, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__7(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__6));
v___x_338_ = lean_unsigned_to_nat(35u);
v___x_339_ = lean_unsigned_to_nat(73u);
v___x_340_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__5));
v___x_341_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__4));
v___x_342_ = l_mkPanicMessageWithDecl(v___x_341_, v___x_340_, v___x_339_, v___x_338_, v___x_337_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont(lean_object* v_mutVars_343_, lean_object* v_var_344_, lean_object* v_ty_345_, lean_object* v_i_346_, lean_object* v_args_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_array_get_size(v_mutVars_343_);
v___x_357_ = lean_nat_dec_lt(v_i_346_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
lean_dec(v_i_346_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_nat_dec_eq(v___x_356_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Lean_mkAppN(v_var_344_, v_args_347_);
lean_dec_ref(v_args_347_);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec_ref(v_args_347_);
v___x_362_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__3, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__3);
v___x_363_ = l_Lean_Expr_app___override(v_var_344_, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
else
{
if (lean_obj_tag(v_ty_345_) == 7)
{
lean_object* v_binderType_365_; lean_object* v_body_366_; lean_object* v_ident_367_; lean_object* v_nm_368_; lean_object* v___x_369_; 
v_binderType_365_ = lean_ctor_get(v_ty_345_, 1);
v_body_366_ = lean_ctor_get(v_ty_345_, 2);
v_ident_367_ = lean_array_fget_borrowed(v_mutVars_343_, v_i_346_);
v_nm_368_ = l_Lean_TSyntax_getId(v_ident_367_);
v___x_369_ = l_Lean_Meta_getFVarFromUserName(v_nm_368_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___x_383_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc_n(v_a_370_, 2);
lean_dec_ref(v___x_369_);
lean_inc(v_a_354_);
lean_inc_ref(v_a_353_);
lean_inc(v_a_352_);
lean_inc_ref(v_a_351_);
v___x_383_ = lean_infer_type(v_a_370_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v___x_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_box(0);
v___x_387_ = 0;
lean_inc(v_a_370_);
lean_inc(v_ident_367_);
v___x_388_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_367_, v_a_370_, v___x_385_, v___x_385_, v___x_386_, v___x_387_, v___x_387_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec_ref(v___x_388_);
v___x_389_ = lean_expr_instantiate_rev(v_binderType_365_, v_args_347_);
lean_inc_ref(v___x_389_);
lean_inc(v_a_384_);
v___x_390_ = l_Lean_Meta_isExprDefEq(v_a_384_, v___x_389_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; uint8_t v___x_392_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref(v___x_390_);
v___x_392_ = lean_unbox(v_a_391_);
lean_dec(v_a_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_inc(v_a_370_);
v___x_393_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_385_, v___x_389_, v_a_384_, v_a_370_, v___x_385_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_dec_ref(v___x_393_);
v___y_372_ = v_a_348_;
v___y_373_ = v_a_349_;
v___y_374_ = v_a_350_;
v___y_375_ = v_a_351_;
v___y_376_ = v_a_352_;
v___y_377_ = v_a_353_;
v___y_378_ = v_a_354_;
goto v___jp_371_;
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_a_370_);
lean_dec_ref(v_args_347_);
lean_dec(v_i_346_);
lean_dec_ref(v_var_344_);
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_dec_ref(v___x_389_);
lean_dec(v_a_384_);
v___y_372_ = v_a_348_;
v___y_373_ = v_a_349_;
v___y_374_ = v_a_350_;
v___y_375_ = v_a_351_;
v___y_376_ = v_a_352_;
v___y_377_ = v_a_353_;
v___y_378_ = v_a_354_;
goto v___jp_371_;
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec_ref(v___x_389_);
lean_dec(v_a_384_);
lean_dec(v_a_370_);
lean_dec_ref(v_args_347_);
lean_dec(v_i_346_);
lean_dec_ref(v_var_344_);
v_a_402_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_390_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_390_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_384_);
lean_dec(v_a_370_);
lean_dec_ref(v_args_347_);
lean_dec(v_i_346_);
lean_dec_ref(v_var_344_);
v_a_410_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_388_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_388_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_dec(v_a_370_);
lean_dec_ref(v_args_347_);
lean_dec(v_i_346_);
lean_dec_ref(v_var_344_);
return v___x_383_;
}
v___jp_371_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = lean_nat_add(v_i_346_, v___x_379_);
lean_dec(v_i_346_);
v___x_381_ = lean_array_push(v_args_347_, v_a_370_);
v_ty_345_ = v_body_366_;
v_i_346_ = v___x_380_;
v_args_347_ = v___x_381_;
v_a_348_ = v___y_372_;
v_a_349_ = v___y_373_;
v_a_350_ = v___y_374_;
v_a_351_ = v___y_375_;
v_a_352_ = v___y_376_;
v_a_353_ = v___y_377_;
v_a_354_ = v___y_378_;
goto _start;
}
}
else
{
lean_dec_ref(v_args_347_);
lean_dec(v_i_346_);
lean_dec_ref(v_var_344_);
return v___x_369_;
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref(v_args_347_);
lean_dec(v_i_346_);
lean_dec_ref(v_var_344_);
v___x_418_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__7, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___closed__7);
v___x_419_ = l_panic___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont_spec__0(v___x_418_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___boxed(lean_object* v_mutVars_420_, lean_object* v_var_421_, lean_object* v_ty_422_, lean_object* v_i_423_, lean_object* v_args_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont(v_mutVars_420_, v_var_421_, v_ty_422_, v_i_423_, v_args_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec_ref(v_ty_422_);
lean_dec_ref(v_mutVars_420_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___redArg(lean_object* v_name_434_, lean_object* v_type_435_, lean_object* v_k_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = 0;
v___x_446_ = 0;
v___x_447_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg(v_name_434_, v___x_445_, v_type_435_, v_k_436_, v___x_446_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___redArg___boxed(lean_object* v_name_448_, lean_object* v_type_449_, lean_object* v_k_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___redArg(v_name_448_, v_type_449_, v_k_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_459_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__2(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__1));
v___x_464_ = l_Lean_MessageData_ofFormat(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__3(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__2, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__2);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__5(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__4));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__7(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__6));
v___x_472_ = l_Lean_stringToMessageData(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_box(0);
v___x_479_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__10));
v___x_480_ = l_Lean_mkConst(v___x_479_, v___x_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___lam__0___boxed(lean_object* v_i_481_, lean_object* v_vars_482_, lean_object* v_dec_483_, lean_object* v_mutVars_484_, lean_object* v_seqInfo_485_, lean_object* v_var_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___lam__0(v_i_481_, v_vars_482_, v_dec_483_, v_mutVars_484_, v_seqInfo_485_, v_var_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v_i_481_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont(lean_object* v_dec_496_, lean_object* v_mutVars_497_, lean_object* v_seqInfo_498_, lean_object* v_i_499_, lean_object* v_vars_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___y_510_; lean_object* v_brk_511_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v_ty_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; 
v___x_514_ = lean_array_get_size(v_mutVars_497_);
v___x_515_ = lean_nat_dec_lt(v_i_499_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v_monadInfo_617_; lean_object* v_doBlockResultType_618_; lean_object* v_m_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
lean_dec(v_i_499_);
lean_dec_ref(v_mutVars_497_);
v_monadInfo_617_ = lean_ctor_get(v_a_501_, 0);
v_doBlockResultType_618_ = lean_ctor_get(v_a_501_, 3);
v_m_619_ = lean_ctor_get(v_monadInfo_617_, 0);
lean_inc_ref(v_doBlockResultType_618_);
lean_inc_ref(v_m_619_);
v___x_620_ = l_Lean_Expr_app___override(v_m_619_, v_doBlockResultType_618_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_nat_dec_eq(v___x_514_, v___x_621_);
if (v___x_622_ == 0)
{
v_ty_517_ = v___x_620_;
v___y_518_ = v_a_501_;
v___y_519_ = v_a_502_;
v___y_520_ = v_a_503_;
v___y_521_ = v_a_504_;
v___y_522_ = v_a_505_;
v___y_523_ = v_a_506_;
v___y_524_ = v_a_507_;
goto v___jp_516_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11);
v___x_624_ = l_Lean_mkArrow(v___x_623_, v___x_620_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref(v___x_624_);
v_ty_517_ = v_a_625_;
v___y_518_ = v_a_501_;
v___y_519_ = v_a_502_;
v___y_520_ = v_a_503_;
v___y_521_ = v_a_504_;
v___y_522_ = v_a_505_;
v___y_523_ = v_a_506_;
v___y_524_ = v_a_507_;
goto v___jp_516_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v_vars_500_);
lean_dec_ref(v_seqInfo_498_);
lean_dec_ref(v_dec_496_);
v_a_626_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_624_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
else
{
lean_object* v_mutVar_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_mutVar_634_ = lean_array_fget_borrowed(v_mutVars_497_, v_i_499_);
v___x_635_ = l_Lean_TSyntax_getId(v_mutVar_634_);
lean_inc(v___x_635_);
v___x_636_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_635_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref(v___x_636_);
v___f_638_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___lam__0___boxed), 14, 5);
lean_closure_set(v___f_638_, 0, v_i_499_);
lean_closure_set(v___f_638_, 1, v_vars_500_);
lean_closure_set(v___f_638_, 2, v_dec_496_);
lean_closure_set(v___f_638_, 3, v_mutVars_497_);
lean_closure_set(v___f_638_, 4, v_seqInfo_498_);
v___x_639_ = l_Lean_LocalDecl_type(v_a_637_);
lean_dec(v_a_637_);
v___x_640_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___redArg(v___x_635_, v___x_639_, v___f_638_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
return v___x_640_;
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v___x_635_);
lean_dec_ref(v_vars_500_);
lean_dec(v_i_499_);
lean_dec_ref(v_seqInfo_498_);
lean_dec_ref(v_mutVars_497_);
lean_dec_ref(v_dec_496_);
v_a_641_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_636_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_636_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
v___jp_509_:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___y_510_);
lean_ctor_set(v___x_512_, 1, v_brk_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
v___jp_516_:
{
uint8_t v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = 1;
v___x_526_ = 1;
v___x_527_ = l_Lean_Meta_mkForallFVars(v_vars_500_, v_ty_517_, v___x_515_, v___x_525_, v___x_525_, v___x_526_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_527_) == 0)
{
uint8_t v_breaks_528_; 
v_breaks_528_ = lean_ctor_get_uint8(v_seqInfo_498_, sizeof(void*)*2);
lean_dec_ref(v_seqInfo_498_);
if (v_breaks_528_ == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; 
lean_dec_ref(v_vars_500_);
v_a_529_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_529_);
lean_dec_ref(v___x_527_);
v___x_530_ = l_Lean_Elab_Do_DoElemCont_elabAsSyntacticallyDeadCode(v_dec_496_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_531_; 
lean_dec_ref(v___x_530_);
v___x_531_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__3, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__3);
v___y_510_ = v_a_529_;
v_brk_511_ = v___x_531_;
goto v___jp_509_;
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_529_);
v_a_532_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_530_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_530_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_540_);
lean_dec_ref(v___x_527_);
v___x_541_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_518_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v_resultType_543_; lean_object* v___x_544_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc_n(v_a_542_, 2);
lean_dec_ref(v___x_541_);
v_resultType_543_ = lean_ctor_get(v_dec_496_, 1);
lean_inc_ref(v_resultType_543_);
v___x_544_ = l_Lean_Meta_isExprDefEq(v_resultType_543_, v_a_542_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; uint8_t v___x_546_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref(v___x_544_);
v___x_546_ = lean_unbox(v_a_545_);
lean_dec(v_a_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_ref(v_resultType_543_);
lean_dec_ref(v_vars_500_);
lean_dec_ref(v_dec_496_);
v___x_547_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__5, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__5);
v___x_548_ = l_Lean_MessageData_ofExpr(v_a_542_);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__7, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__7);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = l_Lean_indentExpr(v_resultType_543_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
v___y_510_ = v_a_540_;
v_brk_511_ = v___x_554_;
goto v___jp_509_;
}
else
{
lean_object* v___x_555_; 
lean_dec(v_a_542_);
v___x_555_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_496_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref(v___x_555_);
v___x_557_ = l_Lean_Meta_mkLambdaFVars(v_vars_500_, v_a_556_, v___x_515_, v___x_525_, v___x_515_, v___x_525_, v___x_526_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec_ref(v_vars_500_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref(v___x_557_);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_nat_dec_eq(v___x_514_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v_a_558_);
v___y_510_ = v_a_540_;
v_brk_511_ = v___x_561_;
goto v___jp_509_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__9));
v___x_563_ = l_Lean_Core_mkFreshUserName(v___x_562_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
v___x_565_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11, &l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11_once, _init_l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___closed__11);
v___x_566_ = 0;
v___x_567_ = l_Lean_Expr_lam___override(v_a_564_, v___x_565_, v_a_558_, v___x_566_);
v___x_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
v___y_510_ = v_a_540_;
v_brk_511_ = v___x_568_;
goto v___jp_509_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_a_558_);
lean_dec(v_a_540_);
v_a_569_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_563_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_563_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_540_);
v_a_577_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_557_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_557_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_a_540_);
lean_dec_ref(v_vars_500_);
v_a_585_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_555_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_555_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v_a_542_);
lean_dec(v_a_540_);
lean_dec_ref(v_vars_500_);
lean_dec_ref(v_dec_496_);
v_a_593_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_544_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_544_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_a_540_);
lean_dec_ref(v_vars_500_);
lean_dec_ref(v_dec_496_);
v_a_601_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_541_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_541_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_vars_500_);
lean_dec_ref(v_seqInfo_498_);
lean_dec_ref(v_dec_496_);
v_a_609_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_527_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_527_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___lam__0(lean_object* v_i_649_, lean_object* v_vars_650_, lean_object* v_dec_651_, lean_object* v_mutVars_652_, lean_object* v_seqInfo_653_, lean_object* v_var_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_add(v_i_649_, v___x_663_);
v___x_665_ = lean_array_push(v_vars_650_, v_var_654_);
v___x_666_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont(v_dec_651_, v_mutVars_652_, v_seqInfo_653_, v___x_664_, v___x_665_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont___boxed(lean_object* v_dec_667_, lean_object* v_mutVars_668_, lean_object* v_seqInfo_669_, lean_object* v_i_670_, lean_object* v_vars_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont(v_dec_667_, v_mutVars_668_, v_seqInfo_669_, v_i_670_, v_vars_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec_ref(v_a_672_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0(lean_object* v_00_u03b1_681_, lean_object* v_name_682_, lean_object* v_type_683_, lean_object* v_k_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___redArg(v_name_682_, v_type_683_, v_k_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0___boxed(lean_object* v_00_u03b1_694_, lean_object* v_name_695_, lean_object* v_type_696_, lean_object* v_k_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont_spec__0(v_00_u03b1_694_, v_name_695_, v_type_696_, v_k_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___y_698_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___redArg(lean_object* v_name_707_, lean_object* v_type_708_, lean_object* v_val_709_, lean_object* v_k_710_, uint8_t v_nondep_711_, uint8_t v_kind_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___f_721_; lean_object* v___x_722_; 
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
lean_inc_ref(v___y_713_);
v___f_721_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_721_, 0, v_k_710_);
lean_closure_set(v___f_721_, 1, v___y_713_);
lean_closure_set(v___f_721_, 2, v___y_714_);
lean_closure_set(v___f_721_, 3, v___y_715_);
v___x_722_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_707_, v_type_708_, v_val_709_, v___f_721_, v_nondep_711_, v_kind_712_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_722_) == 0)
{
return v___x_722_;
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___redArg___boxed(lean_object* v_name_731_, lean_object* v_type_732_, lean_object* v_val_733_, lean_object* v_k_734_, lean_object* v_nondep_735_, lean_object* v_kind_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
uint8_t v_nondep_boxed_745_; uint8_t v_kind_boxed_746_; lean_object* v_res_747_; 
v_nondep_boxed_745_ = lean_unbox(v_nondep_735_);
v_kind_boxed_746_ = lean_unbox(v_kind_736_);
v_res_747_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___redArg(v_name_731_, v_type_732_, v_val_733_, v_k_734_, v_nondep_boxed_745_, v_kind_boxed_746_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec_ref(v___y_737_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1(lean_object* v_00_u03b1_748_, lean_object* v_name_749_, lean_object* v_type_750_, lean_object* v_val_751_, lean_object* v_k_752_, uint8_t v_nondep_753_, uint8_t v_kind_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___redArg(v_name_749_, v_type_750_, v_val_751_, v_k_752_, v_nondep_753_, v_kind_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___boxed(lean_object* v_00_u03b1_764_, lean_object* v_name_765_, lean_object* v_type_766_, lean_object* v_val_767_, lean_object* v_k_768_, lean_object* v_nondep_769_, lean_object* v_kind_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
uint8_t v_nondep_boxed_779_; uint8_t v_kind_boxed_780_; lean_object* v_res_781_; 
v_nondep_boxed_779_ = lean_unbox(v_nondep_769_);
v_kind_boxed_780_ = lean_unbox(v_kind_770_);
v_res_781_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1(v_00_u03b1_764_, v_name_765_, v_type_766_, v_val_767_, v_k_768_, v_nondep_boxed_779_, v_kind_boxed_780_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0(lean_object* v_mutVars_784_, lean_object* v_ty_785_, lean_object* v_k_786_, lean_object* v_brk_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0___closed__0));
lean_inc_ref(v_brk_787_);
v___x_798_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___boxed), 13, 5);
lean_closure_set(v___x_798_, 0, v_mutVars_784_);
lean_closure_set(v___x_798_, 1, v_brk_787_);
lean_closure_set(v___x_798_, 2, v_ty_785_);
lean_closure_set(v___x_798_, 3, v___x_796_);
lean_closure_set(v___x_798_, 4, v___x_797_);
lean_inc(v___y_794_);
lean_inc_ref(v___y_793_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc_ref(v___y_788_);
v___x_799_ = lean_apply_9(v_k_786_, v___x_798_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, lean_box(0));
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; uint8_t v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_mk_empty_array_with_capacity(v___x_801_);
v___x_803_ = lean_array_push(v___x_802_, v_brk_787_);
v___x_804_ = 1;
v___x_805_ = 0;
v___x_806_ = 1;
v___x_807_ = l_Lean_Meta_mkLetFVars(v___x_803_, v_a_800_, v___x_804_, v___x_805_, v___x_806_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec_ref(v___x_803_);
return v___x_807_;
}
else
{
lean_dec_ref(v_brk_787_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0___boxed(lean_object* v_mutVars_808_, lean_object* v_ty_809_, lean_object* v_k_810_, lean_object* v_brk_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0(v_mutVars_808_, v_ty_809_, v_k_810_, v_brk_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v___y_812_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0_spec__0(lean_object* v_msgData_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; lean_object* v_env_828_; lean_object* v___x_829_; lean_object* v_mctx_830_; lean_object* v_lctx_831_; lean_object* v_options_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_827_ = lean_st_ref_get(v___y_825_);
v_env_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_ref(v_env_828_);
lean_dec(v___x_827_);
v___x_829_ = lean_st_ref_get(v___y_823_);
v_mctx_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc_ref(v_mctx_830_);
lean_dec(v___x_829_);
v_lctx_831_ = lean_ctor_get(v___y_822_, 2);
v_options_832_ = lean_ctor_get(v___y_824_, 2);
lean_inc_ref(v_options_832_);
lean_inc_ref(v_lctx_831_);
v___x_833_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_833_, 0, v_env_828_);
lean_ctor_set(v___x_833_, 1, v_mctx_830_);
lean_ctor_set(v___x_833_, 2, v_lctx_831_);
lean_ctor_set(v___x_833_, 3, v_options_832_);
v___x_834_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v_msgData_821_);
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0_spec__0___boxed(lean_object* v_msgData_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0_spec__0(v_msgData_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___redArg(lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_ref_849_; lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_ref_849_ = lean_ctor_get(v___y_846_, 5);
v___x_850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0_spec__0(v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
lean_inc(v_ref_849_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_ref_849_);
lean_ctor_set(v___x_855_, 1, v_a_851_);
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 1);
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___redArg___boxed(lean_object* v_msg_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___redArg(v_msg_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0(lean_object* v_00_u03b1_867_, lean_object* v_msg_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___redArg(v_msg_868_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___boxed(lean_object* v_00_u03b1_878_, lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0(v_00_u03b1_878_, v_msg_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v___y_880_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont(lean_object* v_mutVars_892_, lean_object* v_ty_893_, lean_object* v_brk_x3f_894_, lean_object* v_k_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
if (lean_obj_tag(v_brk_x3f_894_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref(v_ty_893_);
lean_dec_ref(v_mutVars_892_);
v_a_904_ = lean_ctor_get(v_brk_x3f_894_, 0);
lean_inc(v_a_904_);
lean_dec_ref(v_brk_x3f_894_);
v___x_905_ = lean_alloc_closure((void*)(l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__0___boxed), 10, 2);
lean_closure_set(v___x_905_, 0, lean_box(0));
lean_closure_set(v___x_905_, 1, v_a_904_);
lean_inc(v_a_902_);
lean_inc_ref(v_a_901_);
lean_inc(v_a_900_);
lean_inc_ref(v_a_899_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc_ref(v_a_896_);
v___x_906_ = lean_apply_9(v_k_895_, v___x_905_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, lean_box(0));
return v___x_906_;
}
else
{
lean_object* v_a_907_; lean_object* v___f_908_; lean_object* v___x_909_; uint8_t v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; 
v_a_907_ = lean_ctor_get(v_brk_x3f_894_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v_brk_x3f_894_);
lean_inc_ref(v_ty_893_);
v___f_908_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0___boxed), 12, 3);
lean_closure_set(v___f_908_, 0, v_mutVars_892_);
lean_closure_set(v___f_908_, 1, v_ty_893_);
lean_closure_set(v___f_908_, 2, v_k_895_);
v___x_909_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___closed__1));
v___x_910_ = 1;
v___x_911_ = 1;
v___x_912_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont_spec__1___redArg(v___x_909_, v_ty_893_, v_a_907_, v___f_908_, v___x_910_, v___x_911_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___boxed(lean_object* v_mutVars_913_, lean_object* v_ty_914_, lean_object* v_brk_x3f_915_, lean_object* v_k_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont(v_mutVars_913_, v_ty_914_, v_brk_x3f_915_, v_k_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_925_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_box(0);
v___x_927_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg(){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___closed__0);
v___x_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg___boxed(lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(lean_object* v_00_u03b1_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___boxed(lean_object* v_00_u03b1_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0(v_00_u03b1_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(lean_object* v_k_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v_b_958_, lean_object* v_c_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; 
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_961_);
lean_inc_ref(v___y_960_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc_ref(v___y_955_);
v___x_965_ = lean_apply_10(v_k_954_, v_b_958_, v_c_959_, v___y_955_, v___y_956_, v___y_957_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, lean_box(0));
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed(lean_object* v_k_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v_b_970_, lean_object* v_c_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0(v_k_966_, v___y_967_, v___y_968_, v___y_969_, v_b_970_, v_c_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(lean_object* v_type_978_, lean_object* v_k_979_, uint8_t v_cleanupAnnotations_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___f_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc_ref(v___y_981_);
v___f_989_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_989_, 0, v_k_979_);
lean_closure_set(v___f_989_, 1, v___y_981_);
lean_closure_set(v___f_989_, 2, v___y_982_);
lean_closure_set(v___f_989_, 3, v___y_983_);
v___x_990_ = 0;
v___x_991_ = lean_box(0);
v___x_992_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_990_, v___x_991_, v_type_978_, v___f_989_, v_cleanupAnnotations_980_, v___x_990_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_992_) == 0)
{
return v___x_992_;
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg___boxed(lean_object* v_type_1001_, lean_object* v_k_1002_, lean_object* v_cleanupAnnotations_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1012_; lean_object* v_res_1013_; 
v_cleanupAnnotations_boxed_1012_ = lean_unbox(v_cleanupAnnotations_1003_);
v_res_1013_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_type_1001_, v_k_1002_, v_cleanupAnnotations_boxed_1012_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1(lean_object* v_00_u03b1_1014_, lean_object* v_type_1015_, lean_object* v_k_1016_, uint8_t v_cleanupAnnotations_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___redArg(v_type_1015_, v_k_1016_, v_cleanupAnnotations_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_type_1028_, lean_object* v_k_1029_, lean_object* v_cleanupAnnotations_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1039_; lean_object* v_res_1040_; 
v_cleanupAnnotations_boxed_1039_ = lean_unbox(v_cleanupAnnotations_1030_);
v_res_1040_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1(v_00_u03b1_1027_, v_type_1028_, v_k_1029_, v_cleanupAnnotations_boxed_1039_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0(lean_object* v___x_1044_, lean_object* v_seq_1045_, uint8_t v___x_1046_, lean_object* v___x_1047_, lean_object* v_cntVar_1048_, lean_object* v_vars_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___lam__0___closed__1));
v___x_1060_ = l_Lean_Core_mkFreshUserName(v___x_1059_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_1051_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = 1;
v___x_1065_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1065_, 0, v_a_1061_);
lean_ctor_set(v___x_1065_, 1, v_a_1063_);
lean_ctor_set(v___x_1065_, 2, v___x_1044_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*3, v___x_1064_);
v___x_1066_ = l_Lean_Elab_Do_elabDoSeq(v_seq_1045_, v___x_1065_, v___x_1046_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; uint8_t v___x_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = 0;
v___x_1069_ = 1;
v___x_1070_ = l_Lean_Meta_mkLambdaFVars(v_vars_1049_, v_a_1067_, v___x_1068_, v___x_1046_, v___x_1068_, v___x_1046_, v___x_1069_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = lean_mk_empty_array_with_capacity(v___x_1047_);
v___x_1073_ = lean_array_push(v___x_1072_, v_cntVar_1048_);
v___x_1074_ = l_Lean_Meta_mkLambdaFVars(v___x_1073_, v_a_1071_, v___x_1068_, v___x_1046_, v___x_1068_, v___x_1046_, v___x_1069_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec_ref(v___x_1073_);
return v___x_1074_;
}
else
{
lean_dec_ref(v_cntVar_1048_);
return v___x_1070_;
}
}
else
{
lean_dec_ref(v_cntVar_1048_);
return v___x_1066_;
}
}
else
{
lean_dec(v_a_1061_);
lean_dec_ref(v_cntVar_1048_);
lean_dec(v_seq_1045_);
lean_dec_ref(v___x_1044_);
return v___x_1062_;
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_dec_ref(v_cntVar_1048_);
lean_dec(v_seq_1045_);
lean_dec_ref(v___x_1044_);
v_a_1075_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1060_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1060_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed(lean_object* v___x_1083_, lean_object* v_seq_1084_, lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_cntVar_1087_, lean_object* v_vars_1088_, lean_object* v_x_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v___x_9544__boxed_1098_; lean_object* v_res_1099_; 
v___x_9544__boxed_1098_ = lean_unbox(v___x_1085_);
v_res_1099_ = l_Lean_Elab_Do_elabDoRepeat___lam__0(v___x_1083_, v_seq_1084_, v___x_9544__boxed_1098_, v___x_1086_, v_cntVar_1087_, v_vars_1088_, v_x_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec_ref(v_x_1089_);
lean_dec_ref(v_vars_1088_);
lean_dec(v___x_1086_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__1(lean_object* v___y_1100_, lean_object* v_fst_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v_seq_1104_, uint8_t v___x_1105_, lean_object* v___x_1106_, lean_object* v_brk_1107_, lean_object* v_cntVar_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_1109_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___f_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref(v___x_1117_);
lean_inc_ref(v_fst_1101_);
lean_inc_ref(v_cntVar_1108_);
v___x_1119_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont___boxed), 13, 5);
lean_closure_set(v___x_1119_, 0, v___y_1100_);
lean_closure_set(v___x_1119_, 1, v_cntVar_1108_);
lean_closure_set(v___x_1119_, 2, v_fst_1101_);
lean_closure_set(v___x_1119_, 3, v___x_1102_);
lean_closure_set(v___x_1119_, 4, v___x_1103_);
v___x_1120_ = lean_box(v___x_1105_);
lean_inc_ref(v___x_1119_);
v___f_1121_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__0___boxed), 15, 5);
lean_closure_set(v___f_1121_, 0, v___x_1119_);
lean_closure_set(v___f_1121_, 1, v_seq_1104_);
lean_closure_set(v___f_1121_, 2, v___x_1120_);
lean_closure_set(v___f_1121_, 3, v___x_1106_);
lean_closure_set(v___f_1121_, 4, v_cntVar_1108_);
v___x_1122_ = 0;
v___x_1123_ = lean_box(v___x_1122_);
v___x_1124_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_Do_elabDoRepeat_spec__1___boxed), 12, 4);
lean_closure_set(v___x_1124_, 0, lean_box(0));
lean_closure_set(v___x_1124_, 1, v_fst_1101_);
lean_closure_set(v___x_1124_, 2, v___f_1121_);
lean_closure_set(v___x_1124_, 3, v___x_1123_);
v___x_1125_ = l_Lean_Elab_Do_enterLoopBody___redArg(v_brk_1107_, v___x_1119_, v_a_1118_, v___x_1124_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1125_;
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v_cntVar_1108_);
lean_dec_ref(v_brk_1107_);
lean_dec(v___x_1106_);
lean_dec(v_seq_1104_);
lean_dec_ref(v___x_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v_fst_1101_);
lean_dec_ref(v___y_1100_);
v_a_1126_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1117_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1117_);
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
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__1___boxed(lean_object** _args){
lean_object* v___y_1134_ = _args[0];
lean_object* v_fst_1135_ = _args[1];
lean_object* v___x_1136_ = _args[2];
lean_object* v___x_1137_ = _args[3];
lean_object* v_seq_1138_ = _args[4];
lean_object* v___x_1139_ = _args[5];
lean_object* v___x_1140_ = _args[6];
lean_object* v_brk_1141_ = _args[7];
lean_object* v_cntVar_1142_ = _args[8];
lean_object* v___y_1143_ = _args[9];
lean_object* v___y_1144_ = _args[10];
lean_object* v___y_1145_ = _args[11];
lean_object* v___y_1146_ = _args[12];
lean_object* v___y_1147_ = _args[13];
lean_object* v___y_1148_ = _args[14];
lean_object* v___y_1149_ = _args[15];
lean_object* v___y_1150_ = _args[16];
_start:
{
uint8_t v___x_9637__boxed_1151_; lean_object* v_res_1152_; 
v___x_9637__boxed_1151_ = lean_unbox(v___x_1139_);
v_res_1152_ = l_Lean_Elab_Do_elabDoRepeat___lam__1(v___y_1134_, v_fst_1135_, v___x_1136_, v___x_1137_, v_seq_1138_, v___x_9637__boxed_1151_, v___x_1140_, v_brk_1141_, v_cntVar_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__2(lean_object* v___y_1158_, lean_object* v_fst_1159_, lean_object* v___x_1160_, lean_object* v___x_1161_, lean_object* v_seq_1162_, uint8_t v___x_1163_, lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v_snd_1166_, lean_object* v_brk_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; 
v___x_1176_ = lean_box(v___x_1163_);
lean_inc_ref(v___x_1161_);
lean_inc(v___x_1160_);
lean_inc_ref_n(v_fst_1159_, 2);
lean_inc_ref(v___y_1158_);
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1177_, 0, v___y_1158_);
lean_closure_set(v___f_1177_, 1, v_fst_1159_);
lean_closure_set(v___f_1177_, 2, v___x_1160_);
lean_closure_set(v___f_1177_, 3, v___x_1161_);
lean_closure_set(v___f_1177_, 4, v_seq_1162_);
lean_closure_set(v___f_1177_, 5, v___x_1176_);
lean_closure_set(v___f_1177_, 6, v___x_1164_);
lean_closure_set(v___f_1177_, 7, v_brk_1167_);
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__1));
v___x_1179_ = 0;
v___x_1180_ = 1;
v___x_1181_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO_spec__0___redArg(v___x_1178_, v___x_1179_, v_fst_1159_, v___f_1177_, v___x_1180_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1183_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref(v___x_1181_);
lean_inc_ref(v_fst_1159_);
v___x_1183_ = l_Lean_Meta_getLevel(v_fst_1159_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___y_1186_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref(v___x_1183_);
if (lean_obj_tag(v_snd_1166_) == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v_snd_1166_);
v___x_1197_ = lean_box(0);
v___y_1186_ = v___x_1197_;
goto v___jp_1185_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v_snd_1166_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_snd_1166_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v_snd_1166_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v_snd_1166_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
v___y_1186_ = v___x_1203_;
goto v___jp_1185_;
}
}
}
v___jp_1185_:
{
lean_object* v___x_1187_; 
lean_inc_ref(v_fst_1159_);
v___x_1187_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO(v_fst_1159_, v___y_1186_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
v___x_1189_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__2));
v___x_1190_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___lam__2___closed__3));
v___x_1191_ = l_Lean_Name_mkStr3(v___x_1165_, v___x_1189_, v___x_1190_);
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1193_, 0, v_a_1184_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_Expr_const___override(v___x_1191_, v___x_1193_);
lean_inc_ref(v_fst_1159_);
v___x_1195_ = l_Lean_mkApp3(v___x_1194_, v_fst_1159_, v_a_1188_, v_a_1182_);
v___x_1196_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCont(v___y_1158_, v___x_1195_, v_fst_1159_, v___x_1160_, v___x_1161_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec_ref(v_fst_1159_);
lean_dec_ref(v___y_1158_);
return v___x_1196_;
}
else
{
lean_dec(v_a_1184_);
lean_dec(v_a_1182_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1161_);
lean_dec(v___x_1160_);
lean_dec_ref(v_fst_1159_);
lean_dec_ref(v___y_1158_);
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v_a_1182_);
lean_dec_ref(v_snd_1166_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1161_);
lean_dec(v___x_1160_);
lean_dec_ref(v_fst_1159_);
lean_dec_ref(v___y_1158_);
v_a_1206_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1183_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1183_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
else
{
lean_dec_ref(v_snd_1166_);
lean_dec_ref(v___x_1165_);
lean_dec_ref(v___x_1161_);
lean_dec(v___x_1160_);
lean_dec_ref(v_fst_1159_);
lean_dec_ref(v___y_1158_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___lam__2___boxed(lean_object** _args){
lean_object* v___y_1214_ = _args[0];
lean_object* v_fst_1215_ = _args[1];
lean_object* v___x_1216_ = _args[2];
lean_object* v___x_1217_ = _args[3];
lean_object* v_seq_1218_ = _args[4];
lean_object* v___x_1219_ = _args[5];
lean_object* v___x_1220_ = _args[6];
lean_object* v___x_1221_ = _args[7];
lean_object* v_snd_1222_ = _args[8];
lean_object* v_brk_1223_ = _args[9];
lean_object* v___y_1224_ = _args[10];
lean_object* v___y_1225_ = _args[11];
lean_object* v___y_1226_ = _args[12];
lean_object* v___y_1227_ = _args[13];
lean_object* v___y_1228_ = _args[14];
lean_object* v___y_1229_ = _args[15];
lean_object* v___y_1230_ = _args[16];
lean_object* v___y_1231_ = _args[17];
_start:
{
uint8_t v___x_9723__boxed_1232_; lean_object* v_res_1233_; 
v___x_9723__boxed_1232_ = lean_unbox(v___x_1219_);
v_res_1233_ = l_Lean_Elab_Do_elabDoRepeat___lam__2(v___y_1214_, v_fst_1215_, v___x_1216_, v___x_1217_, v_seq_1218_, v___x_9723__boxed_1232_, v___x_1220_, v___x_1221_, v_snd_1222_, v_brk_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec_ref(v___y_1224_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoRepeat_spec__2(lean_object* v_a_1234_, lean_object* v_as_1235_, size_t v_i_1236_, size_t v_stop_1237_, lean_object* v_b_1238_){
_start:
{
lean_object* v___y_1240_; uint8_t v___x_1244_; 
v___x_1244_ = lean_usize_dec_eq(v_i_1236_, v_stop_1237_);
if (v___x_1244_ == 0)
{
lean_object* v_reassigns_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_reassigns_1245_ = lean_ctor_get(v_a_1234_, 1);
v___x_1246_ = lean_array_uget_borrowed(v_as_1235_, v_i_1236_);
v___x_1247_ = l_Lean_TSyntax_getId(v___x_1246_);
v___x_1248_ = l_Lean_NameSet_contains(v_reassigns_1245_, v___x_1247_);
lean_dec(v___x_1247_);
if (v___x_1248_ == 0)
{
v___y_1240_ = v_b_1238_;
goto v___jp_1239_;
}
else
{
lean_object* v___x_1249_; 
lean_inc(v___x_1246_);
v___x_1249_ = lean_array_push(v_b_1238_, v___x_1246_);
v___y_1240_ = v___x_1249_;
goto v___jp_1239_;
}
}
else
{
return v_b_1238_;
}
v___jp_1239_:
{
size_t v___x_1241_; size_t v___x_1242_; 
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_add(v_i_1236_, v___x_1241_);
v_i_1236_ = v___x_1242_;
v_b_1238_ = v___y_1240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoRepeat_spec__2___boxed(lean_object* v_a_1250_, lean_object* v_as_1251_, lean_object* v_i_1252_, lean_object* v_stop_1253_, lean_object* v_b_1254_){
_start:
{
size_t v_i_boxed_1255_; size_t v_stop_boxed_1256_; lean_object* v_res_1257_; 
v_i_boxed_1255_ = lean_unbox_usize(v_i_1252_);
lean_dec(v_i_1252_);
v_stop_boxed_1256_ = lean_unbox_usize(v_stop_1253_);
lean_dec(v_stop_1253_);
v_res_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoRepeat_spec__2(v_a_1250_, v_as_1251_, v_i_boxed_1255_, v_stop_boxed_1256_, v_b_1254_);
lean_dec_ref(v_as_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat(lean_object* v_stx_1268_, lean_object* v_dec_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkCCPO___lam__0___closed__0));
v___x_1279_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__3));
lean_inc(v_stx_1268_);
v___x_1280_ = l_Lean_Syntax_isOfKind(v_stx_1268_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
lean_dec_ref(v_dec_1269_);
lean_dec(v_stx_1268_);
v___x_1281_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoRepeat_spec__0___redArg();
return v___x_1281_;
}
else
{
lean_object* v_fileName_1282_; lean_object* v_fileMap_1283_; lean_object* v_options_1284_; lean_object* v_currRecDepth_1285_; lean_object* v_maxRecDepth_1286_; lean_object* v_ref_1287_; lean_object* v_currNamespace_1288_; lean_object* v_openDecls_1289_; lean_object* v_initHeartbeats_1290_; lean_object* v_maxHeartbeats_1291_; lean_object* v_quotContext_1292_; lean_object* v_currMacroScope_1293_; uint8_t v_diag_1294_; lean_object* v_cancelTk_x3f_1295_; uint8_t v_suppressElabErrors_1296_; lean_object* v_inheritedTraceOptions_1297_; lean_object* v___x_1298_; lean_object* v_tk_1299_; lean_object* v___x_1300_; lean_object* v_seq_1301_; lean_object* v_ref_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_fileName_1282_ = lean_ctor_get(v_a_1275_, 0);
v_fileMap_1283_ = lean_ctor_get(v_a_1275_, 1);
v_options_1284_ = lean_ctor_get(v_a_1275_, 2);
v_currRecDepth_1285_ = lean_ctor_get(v_a_1275_, 3);
v_maxRecDepth_1286_ = lean_ctor_get(v_a_1275_, 4);
v_ref_1287_ = lean_ctor_get(v_a_1275_, 5);
v_currNamespace_1288_ = lean_ctor_get(v_a_1275_, 6);
v_openDecls_1289_ = lean_ctor_get(v_a_1275_, 7);
v_initHeartbeats_1290_ = lean_ctor_get(v_a_1275_, 8);
v_maxHeartbeats_1291_ = lean_ctor_get(v_a_1275_, 9);
v_quotContext_1292_ = lean_ctor_get(v_a_1275_, 10);
v_currMacroScope_1293_ = lean_ctor_get(v_a_1275_, 11);
v_diag_1294_ = lean_ctor_get_uint8(v_a_1275_, sizeof(void*)*14);
v_cancelTk_x3f_1295_ = lean_ctor_get(v_a_1275_, 12);
v_suppressElabErrors_1296_ = lean_ctor_get_uint8(v_a_1275_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1297_ = lean_ctor_get(v_a_1275_, 13);
v___x_1298_ = lean_unsigned_to_nat(0u);
v_tk_1299_ = l_Lean_Syntax_getArg(v_stx_1268_, v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(1u);
v_seq_1301_ = l_Lean_Syntax_getArg(v_stx_1268_, v___x_1300_);
lean_dec(v_stx_1268_);
v_ref_1302_ = l_Lean_replaceRef(v_tk_1299_, v_ref_1287_);
lean_dec(v_tk_1299_);
lean_inc_ref(v_inheritedTraceOptions_1297_);
lean_inc(v_cancelTk_x3f_1295_);
lean_inc(v_currMacroScope_1293_);
lean_inc(v_quotContext_1292_);
lean_inc(v_maxHeartbeats_1291_);
lean_inc(v_initHeartbeats_1290_);
lean_inc(v_openDecls_1289_);
lean_inc(v_currNamespace_1288_);
lean_inc(v_maxRecDepth_1286_);
lean_inc(v_currRecDepth_1285_);
lean_inc_ref(v_options_1284_);
lean_inc_ref(v_fileMap_1283_);
lean_inc_ref(v_fileName_1282_);
v___x_1303_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1303_, 0, v_fileName_1282_);
lean_ctor_set(v___x_1303_, 1, v_fileMap_1283_);
lean_ctor_set(v___x_1303_, 2, v_options_1284_);
lean_ctor_set(v___x_1303_, 3, v_currRecDepth_1285_);
lean_ctor_set(v___x_1303_, 4, v_maxRecDepth_1286_);
lean_ctor_set(v___x_1303_, 5, v_ref_1302_);
lean_ctor_set(v___x_1303_, 6, v_currNamespace_1288_);
lean_ctor_set(v___x_1303_, 7, v_openDecls_1289_);
lean_ctor_set(v___x_1303_, 8, v_initHeartbeats_1290_);
lean_ctor_set(v___x_1303_, 9, v_maxHeartbeats_1291_);
lean_ctor_set(v___x_1303_, 10, v_quotContext_1292_);
lean_ctor_set(v___x_1303_, 11, v_currMacroScope_1293_);
lean_ctor_set(v___x_1303_, 12, v_cancelTk_x3f_1295_);
lean_ctor_set(v___x_1303_, 13, v_inheritedTraceOptions_1297_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*14, v_diag_1294_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*14 + 1, v_suppressElabErrors_1296_);
lean_inc(v_seq_1301_);
v___x_1304_ = l_Lean_Elab_Do_inferControlInfoSeq(v_seq_1301_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v___x_1303_, v_a_1276_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___y_1307_; lean_object* v_mutVars_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1304_);
v_mutVars_1324_ = lean_ctor_get(v_a_1270_, 1);
v___x_1325_ = lean_array_get_size(v_mutVars_1324_);
v___x_1326_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__4));
v___x_1327_ = lean_nat_dec_lt(v___x_1298_, v___x_1325_);
if (v___x_1327_ == 0)
{
v___y_1307_ = v___x_1326_;
goto v___jp_1306_;
}
else
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_nat_dec_le(v___x_1325_, v___x_1325_);
if (v___x_1328_ == 0)
{
if (v___x_1327_ == 0)
{
v___y_1307_ = v___x_1326_;
goto v___jp_1306_;
}
else
{
size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((size_t)0ULL);
v___x_1330_ = lean_usize_of_nat(v___x_1325_);
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoRepeat_spec__2(v_a_1305_, v_mutVars_1324_, v___x_1329_, v___x_1330_, v___x_1326_);
v___y_1307_ = v___x_1331_;
goto v___jp_1306_;
}
}
else
{
size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = lean_usize_of_nat(v___x_1325_);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoRepeat_spec__2(v_a_1305_, v_mutVars_1324_, v___x_1332_, v___x_1333_, v___x_1326_);
v___y_1307_ = v___x_1334_;
goto v___jp_1306_;
}
}
v___jp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont___lam__0___closed__0));
lean_inc_ref(v___y_1307_);
v___x_1309_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_mkBreakCont(v_dec_1269_, v___y_1307_, v_a_1305_, v___x_1298_, v___x_1308_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v___x_1303_, v_a_1276_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; lean_object* v___x_1313_; lean_object* v___f_1314_; lean_object* v___x_1315_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1309_);
v_fst_1311_ = lean_ctor_get(v_a_1310_, 0);
lean_inc_n(v_fst_1311_, 2);
v_snd_1312_ = lean_ctor_get(v_a_1310_, 1);
lean_inc_n(v_snd_1312_, 2);
lean_dec(v_a_1310_);
v___x_1313_ = lean_box(v___x_1280_);
lean_inc_ref(v___y_1307_);
v___f_1314_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___lam__2___boxed), 18, 9);
lean_closure_set(v___f_1314_, 0, v___y_1307_);
lean_closure_set(v___f_1314_, 1, v_fst_1311_);
lean_closure_set(v___f_1314_, 2, v___x_1298_);
lean_closure_set(v___f_1314_, 3, v___x_1308_);
lean_closure_set(v___f_1314_, 4, v_seq_1301_);
lean_closure_set(v___f_1314_, 5, v___x_1313_);
lean_closure_set(v___f_1314_, 6, v___x_1300_);
lean_closure_set(v___f_1314_, 7, v___x_1278_);
lean_closure_set(v___f_1314_, 8, v_snd_1312_);
v___x_1315_ = l___private_Lean_Elab_BuiltinDo_Repeat_0__Lean_Elab_Do_elabDoRepeat_withBreakCont(v___y_1307_, v_fst_1311_, v_snd_1312_, v___f_1314_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v___x_1303_, v_a_1276_);
lean_dec_ref(v___x_1303_);
return v___x_1315_;
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v___y_1307_);
lean_dec_ref(v___x_1303_);
lean_dec(v_seq_1301_);
v_a_1316_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1309_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1309_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v___x_1303_);
lean_dec(v_seq_1301_);
lean_dec_ref(v_dec_1269_);
v_a_1335_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1304_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1304_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___boxed(lean_object* v_stx_1343_, lean_object* v_dec_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Elab_Do_elabDoRepeat(v_stx_1343_, v_dec_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec_ref(v_a_1345_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1(){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1363_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_1364_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___closed__3));
v___x_1365_ = ((lean_object*)(l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___closed__3));
v___x_1366_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoRepeat___boxed), 10, 0);
v___x_1367_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1363_, v___x_1364_, v___x_1365_, v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1___boxed(lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
return v_res_1369_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Repeat(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoRepeat___regBuiltin_Lean_Elab_Do_elabDoRepeat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Repeat(uint8_t builtin) {
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
lean_object* initialize_Init_Repeat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_Repeat(builtin);
}
#ifdef __cplusplus
}
#endif
