// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Syntax
// Imports: public import Lean.Elab.BuiltinNotation public import Std.Do.Triple.Basic
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_dec(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termSpred(_)"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 240, 91, 148, 237, 191, 255, 193)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20_value;
static lean_once_cell_t l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Notation"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(66, 246, 126, 200, 193, 235, 124, 8)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value;
static lean_once_cell_t l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delab___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PostCond"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "noThrow"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value),LEAN_SCALAR_PTR_LITERAL(16, 55, 64, 24, 30, 138, 86, 160)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 10, .m_data = "term_⇓_=>_"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value),LEAN_SCALAR_PTR_LITERAL(1, 118, 219, 9, 44, 173, 117, 117)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⇓"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 138, 197, 137, 5, 150, 182)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value),LEAN_SCALAR_PTR_LITERAL(219, 88, 117, 139, 154, 102, 4, 51)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(30, 245, 70, 4, 244, 90, 84, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(231, 31, 105, 226, 127, 101, 182, 126)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 231, 200, 31, 60, 125, 42, 107)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(28, 197, 134, 35, 116, 153, 12, 206)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unexpandPostCondNoThrow"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(159, 119, 250, 196, 50, 251, 159, 237)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mayThrow"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 136, 136, 54, 72, 103, 208, 40)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "term_⇓\?_=>_"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value),LEAN_SCALAR_PTR_LITERAL(84, 52, 46, 60, 233, 87, 205, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⇓\?"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 138, 197, 137, 5, 150, 182)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 252, 207, 107, 212, 83, 11, 103)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "unexpandPostCondMayThrow"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 115, 97, 176, 4, 84, 201, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "triple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 3, 229, 14, 94, 184, 116, 193)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "spred("};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Assertion"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(199, 193, 192, 53, 36, 133, 171, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(31, 48, 165, 224, 255, 99, 7, 166)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PostShape"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(1, 175, 203, 13, 190, 221, 208, 89)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(209, 91, 166, 6, 71, 210, 197, 93)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Wrong level 0 "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Type of "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " is not a type application: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabTriple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 227, 204, 83, 125, 199, 55, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___boxed(lean_object*);
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20));
v___x_44_ = l_String_toRawSubstring_x27(v___x_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Array_mkArray0(lean_box(0));
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(lean_object* v_x_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3));
lean_inc(v_x_106_);
v___x_110_ = l_Lean_Syntax_isOfKind(v_x_106_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8));
lean_inc(v_x_106_);
v___x_112_ = l_Lean_Syntax_isOfKind(v_x_106_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10));
lean_inc(v_x_106_);
v___x_114_ = l_Lean_Syntax_isOfKind(v_x_106_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_115_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11));
v___x_116_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12));
lean_inc(v_x_106_);
v___x_117_ = l_Lean_Syntax_isOfKind(v_x_106_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14));
lean_inc(v_x_106_);
v___x_119_ = l_Lean_Syntax_isOfKind(v_x_106_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v_x_106_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = l_Lean_Syntax_getArg(v_x_106_, v___x_121_);
v___x_123_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16));
lean_inc(v___x_122_);
v___x_124_ = l_Lean_Syntax_isOfKind(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_dec(v___x_122_);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v_x_106_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = l_Lean_Syntax_getArg(v___x_122_, v___x_126_);
lean_dec(v___x_122_);
v___x_128_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18));
lean_inc(v___x_127_);
v___x_129_ = l_Lean_Syntax_isOfKind(v___x_127_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec(v___x_127_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v_x_106_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_Syntax_getArg(v___x_127_, v___x_121_);
lean_dec(v___x_127_);
v___x_132_ = lean_box(0);
v___x_133_ = l_Lean_Syntax_matchesIdent(v___x_131_, v___x_132_);
lean_dec(v___x_131_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v_x_106_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = lean_unsigned_to_nat(3u);
v___x_136_ = l_Lean_Syntax_getArg(v_x_106_, v___x_135_);
lean_inc(v___x_136_);
v___x_137_ = l_Lean_Syntax_matchesNull(v___x_136_, v___x_126_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
lean_dec(v___x_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_x_106_);
return v___x_138_;
}
else
{
lean_object* v_P_139_; lean_object* v___x_140_; 
v_P_139_ = l_Lean_Syntax_getArg(v_x_106_, v___x_126_);
lean_dec(v_x_106_);
v___x_140_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_139_, v___y_107_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_168_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_168_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_168_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_168_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v_ref_145_; lean_object* v_quotContext_146_; lean_object* v_currMacroScope_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v_ref_145_ = lean_ctor_get(v___y_107_, 5);
v_quotContext_146_ = lean_ctor_get(v___y_107_, 10);
v_currMacroScope_147_ = lean_ctor_get(v___y_107_, 11);
v___x_148_ = l_Lean_Syntax_getArg(v___x_136_, v___x_121_);
lean_dec(v___x_136_);
v___x_149_ = l_Lean_SourceInfo_fromRef(v_ref_145_, v___x_117_);
v___x_150_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19));
lean_inc_n(v___x_149_, 7);
v___x_151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
lean_inc(v_currMacroScope_147_);
lean_inc(v_quotContext_146_);
v___x_153_ = l_Lean_addMacroScope(v_quotContext_146_, v___x_132_, v_currMacroScope_147_);
v___x_154_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40));
v___x_155_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_155_, 0, v___x_149_);
lean_ctor_set(v___x_155_, 1, v___x_152_);
lean_ctor_set(v___x_155_, 2, v___x_153_);
lean_ctor_set(v___x_155_, 3, v___x_154_);
v___x_156_ = l_Lean_Syntax_node1(v___x_149_, v___x_128_, v___x_155_);
v___x_157_ = l_Lean_Syntax_node2(v___x_149_, v___x_123_, v___x_151_, v___x_156_);
v___x_158_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41));
v___x_159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_149_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
v___x_161_ = l_Lean_Syntax_node1(v___x_149_, v___x_160_, v___x_148_);
v___x_162_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44));
v___x_163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_149_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Lean_Syntax_node5(v___x_149_, v___x_118_, v___x_157_, v_a_141_, v___x_159_, v___x_161_, v___x_163_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_164_);
v___x_166_ = v___x_143_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
else
{
lean_dec(v___x_136_);
return v___x_140_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = l_Lean_Syntax_getArg(v_x_106_, v___x_169_);
v___x_171_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46));
lean_inc(v___x_170_);
v___x_172_ = l_Lean_Syntax_isOfKind(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_dec(v___x_170_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_x_106_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = l_Lean_Syntax_getArg(v___x_170_, v___x_169_);
v___x_176_ = l_Lean_Syntax_matchesNull(v___x_175_, v___x_174_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; 
lean_dec(v___x_170_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v_x_106_);
return v___x_177_;
}
else
{
lean_object* v___x_178_; lean_object* v_b_179_; lean_object* v___x_180_; 
lean_dec(v_x_106_);
v___x_178_ = lean_unsigned_to_nat(3u);
v_b_179_ = l_Lean_Syntax_getArg(v___x_170_, v___x_178_);
v___x_180_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_b_179_, v___y_107_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_202_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_202_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_202_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_202_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_ref_185_; lean_object* v___x_186_; lean_object* v_xs_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v_ref_185_ = lean_ctor_get(v___y_107_, 5);
v___x_186_ = l_Lean_Syntax_getArg(v___x_170_, v___x_174_);
lean_dec(v___x_170_);
v_xs_187_ = l_Lean_Syntax_getArgs(v___x_186_);
lean_dec(v___x_186_);
v___x_188_ = l_Lean_SourceInfo_fromRef(v_ref_185_, v___x_114_);
lean_inc_n(v___x_188_, 5);
v___x_189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_115_);
v___x_190_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
v___x_191_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
v___x_192_ = l_Array_append___redArg(v___x_191_, v_xs_187_);
lean_dec_ref(v_xs_187_);
v___x_193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_193_, 0, v___x_188_);
lean_ctor_set(v___x_193_, 1, v___x_190_);
lean_ctor_set(v___x_193_, 2, v___x_192_);
v___x_194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_194_, 0, v___x_188_);
lean_ctor_set(v___x_194_, 1, v___x_190_);
lean_ctor_set(v___x_194_, 2, v___x_191_);
v___x_195_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48));
v___x_196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_188_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = l_Lean_Syntax_node4(v___x_188_, v___x_171_, v___x_193_, v___x_194_, v___x_196_, v_a_181_);
v___x_198_ = l_Lean_Syntax_node2(v___x_188_, v___x_116_, v___x_189_, v___x_197_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_198_);
v___x_200_ = v___x_183_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_dec(v___x_170_);
return v___x_180_;
}
}
}
}
}
else
{
lean_object* v___x_203_; lean_object* v_t_204_; lean_object* v___x_205_; 
v___x_203_ = lean_unsigned_to_nat(3u);
v_t_204_ = l_Lean_Syntax_getArg(v_x_106_, v___x_203_);
v___x_205_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_t_204_, v___y_107_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; lean_object* v_e_208_; lean_object* v___x_209_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref(v___x_205_);
v___x_207_ = lean_unsigned_to_nat(5u);
v_e_208_ = l_Lean_Syntax_getArg(v_x_106_, v___x_207_);
v___x_209_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_e_208_, v___y_107_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_228_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_228_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_228_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_228_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_ref_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v_ref_214_ = lean_ctor_get(v___y_107_, 5);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = l_Lean_Syntax_getArg(v_x_106_, v___x_215_);
lean_dec(v_x_106_);
v___x_217_ = l_Lean_SourceInfo_fromRef(v_ref_214_, v___x_112_);
v___x_218_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49));
lean_inc_n(v___x_217_, 3);
v___x_219_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50));
v___x_221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_217_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51));
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_217_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Lean_Syntax_node6(v___x_217_, v___x_113_, v___x_219_, v___x_216_, v___x_221_, v_a_206_, v___x_223_, v_a_210_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_224_);
v___x_226_ = v___x_212_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
else
{
lean_dec(v_a_206_);
lean_dec(v_x_106_);
return v___x_209_;
}
}
else
{
lean_dec(v_x_106_);
return v___x_205_;
}
}
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l_Lean_Syntax_getArg(v_x_106_, v___x_229_);
v___x_231_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16));
lean_inc(v___x_230_);
v___x_232_ = l_Lean_Syntax_isOfKind(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
lean_dec(v___x_230_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_x_106_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = l_Lean_Syntax_getArg(v___x_230_, v___x_234_);
lean_dec(v___x_230_);
v___x_236_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18));
lean_inc(v___x_235_);
v___x_237_ = l_Lean_Syntax_isOfKind(v___x_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
lean_dec(v___x_235_);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v_x_106_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_239_ = l_Lean_Syntax_getArg(v___x_235_, v___x_229_);
lean_dec(v___x_235_);
v___x_240_ = lean_box(0);
v___x_241_ = l_Lean_Syntax_matchesIdent(v___x_239_, v___x_240_);
lean_dec(v___x_239_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v_x_106_);
return v___x_242_;
}
else
{
lean_object* v_P_243_; lean_object* v___x_244_; 
v_P_243_ = l_Lean_Syntax_getArg(v_x_106_, v___x_234_);
lean_dec(v_x_106_);
v___x_244_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_243_, v___y_107_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_267_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_267_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_267_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_267_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_ref_249_; lean_object* v_quotContext_250_; lean_object* v_currMacroScope_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v_ref_249_ = lean_ctor_get(v___y_107_, 5);
v_quotContext_250_ = lean_ctor_get(v___y_107_, 10);
v_currMacroScope_251_ = lean_ctor_get(v___y_107_, 11);
v___x_252_ = l_Lean_SourceInfo_fromRef(v_ref_249_, v___x_110_);
v___x_253_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19));
lean_inc_n(v___x_252_, 5);
v___x_254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
lean_inc(v_currMacroScope_251_);
lean_inc(v_quotContext_250_);
v___x_256_ = l_Lean_addMacroScope(v_quotContext_250_, v___x_240_, v_currMacroScope_251_);
v___x_257_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40));
v___x_258_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_258_, 0, v___x_252_);
lean_ctor_set(v___x_258_, 1, v___x_255_);
lean_ctor_set(v___x_258_, 2, v___x_256_);
lean_ctor_set(v___x_258_, 3, v___x_257_);
v___x_259_ = l_Lean_Syntax_node1(v___x_252_, v___x_236_, v___x_258_);
v___x_260_ = l_Lean_Syntax_node2(v___x_252_, v___x_231_, v___x_254_, v___x_259_);
v___x_261_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44));
v___x_262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_252_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_Lean_Syntax_node3(v___x_252_, v___x_111_, v___x_260_, v_a_245_, v___x_262_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_263_);
v___x_265_ = v___x_247_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
return v___x_244_;
}
}
}
}
}
}
else
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = l_Lean_Syntax_getArg(v_x_106_, v___x_268_);
lean_dec(v_x_106_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___boxed(lean_object* v_x_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_271_, v___y_272_);
lean_dec_ref(v___y_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(lean_object* v_child_275_, lean_object* v_childIdx_276_, lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_subExpr_285_; lean_object* v_optionsPerPos_286_; lean_object* v_currNamespace_287_; lean_object* v_openDecls_288_; uint8_t v_inPattern_289_; lean_object* v_depth_290_; lean_object* v_pos_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_subExpr_285_ = lean_ctor_get(v___y_278_, 3);
v_optionsPerPos_286_ = lean_ctor_get(v___y_278_, 0);
v_currNamespace_287_ = lean_ctor_get(v___y_278_, 1);
v_openDecls_288_ = lean_ctor_get(v___y_278_, 2);
v_inPattern_289_ = lean_ctor_get_uint8(v___y_278_, sizeof(void*)*5);
v_depth_290_ = lean_ctor_get(v___y_278_, 4);
v_pos_291_ = lean_ctor_get(v_subExpr_285_, 1);
v___x_292_ = l_Lean_SubExpr_Pos_push(v_pos_291_, v_childIdx_276_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_child_275_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_inc(v_depth_290_);
lean_inc(v_openDecls_288_);
lean_inc(v_currNamespace_287_);
lean_inc(v_optionsPerPos_286_);
v___x_294_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_294_, 0, v_optionsPerPos_286_);
lean_ctor_set(v___x_294_, 1, v_currNamespace_287_);
lean_ctor_set(v___x_294_, 2, v_openDecls_288_);
lean_ctor_set(v___x_294_, 3, v___x_293_);
lean_ctor_set(v___x_294_, 4, v_depth_290_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*5, v_inPattern_289_);
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
lean_inc(v___y_281_);
lean_inc_ref(v___y_280_);
lean_inc(v___y_279_);
v___x_295_ = lean_apply_7(v_x_277_, v___x_294_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, lean_box(0));
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg___boxed(lean_object* v_child_296_, lean_object* v_childIdx_297_, lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_296_, v_childIdx_297_, v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(lean_object* v___y_307_){
_start:
{
lean_object* v_subExpr_309_; lean_object* v_expr_310_; lean_object* v___x_311_; 
v_subExpr_309_ = lean_ctor_get(v___y_307_, 3);
v_expr_310_ = lean_ctor_get(v_subExpr_309_, 0);
lean_inc_ref(v_expr_310_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v_expr_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg___boxed(lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_312_);
lean_dec_ref(v___y_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(lean_object* v_x_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_323_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_316_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref(v___x_323_);
v___x_325_ = l_Lean_Expr_appArg_x21(v_a_324_);
lean_dec(v_a_324_);
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v___x_325_, v___x_326_, v_x_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg___boxed(lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_336_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5));
v___x_352_ = lean_mk_syntax_ident(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0));
v___x_370_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_369_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_442_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_442_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_442_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_442_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12));
lean_inc(v_a_371_);
v___x_376_ = l_Lean_Syntax_isOfKind(v_a_371_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v_ref_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v_ref_377_ = lean_ctor_get(v_a_366_, 5);
v___x_378_ = l_Lean_SourceInfo_fromRef(v_ref_377_, v___x_376_);
v___x_379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_380_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
v___x_381_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_378_);
v___x_382_ = l_Lean_Syntax_node1(v___x_378_, v___x_381_, v_a_371_);
v___x_383_ = l_Lean_Syntax_node2(v___x_378_, v___x_379_, v___x_380_, v___x_382_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_383_);
v___x_385_ = v___x_373_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = l_Lean_Syntax_getArg(v_a_371_, v___x_387_);
v___x_389_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46));
lean_inc(v___x_388_);
v___x_390_ = l_Lean_Syntax_isOfKind(v___x_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v_ref_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
lean_dec(v___x_388_);
v_ref_391_ = lean_ctor_get(v_a_366_, 5);
v___x_392_ = l_Lean_SourceInfo_fromRef(v_ref_391_, v___x_390_);
v___x_393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_394_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
v___x_395_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_392_);
v___x_396_ = l_Lean_Syntax_node1(v___x_392_, v___x_395_, v_a_371_);
v___x_397_ = l_Lean_Syntax_node2(v___x_392_, v___x_393_, v___x_394_, v___x_396_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_397_);
v___x_399_ = v___x_373_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = l_Lean_Syntax_getArg(v___x_388_, v___x_387_);
v___x_403_ = l_Lean_Syntax_matchesNull(v___x_402_, v___x_401_);
if (v___x_403_ == 0)
{
lean_object* v_ref_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
lean_dec(v___x_388_);
v_ref_404_ = lean_ctor_get(v_a_366_, 5);
v___x_405_ = l_Lean_SourceInfo_fromRef(v_ref_404_, v___x_403_);
v___x_406_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_407_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
v___x_408_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_405_);
v___x_409_ = l_Lean_Syntax_node1(v___x_405_, v___x_408_, v_a_371_);
v___x_410_ = l_Lean_Syntax_node2(v___x_405_, v___x_406_, v___x_407_, v___x_409_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_410_);
v___x_412_ = v___x_373_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
lean_del_object(v___x_373_);
lean_dec(v_a_371_);
v___x_414_ = lean_unsigned_to_nat(3u);
v___x_415_ = l_Lean_Syntax_getArg(v___x_388_, v___x_414_);
v___x_416_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_415_, v_a_366_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_441_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_441_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_441_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_441_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_ref_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v_ref_421_ = lean_ctor_get(v_a_366_, 5);
v___x_422_ = l_Lean_Syntax_getArg(v___x_388_, v___x_401_);
lean_dec(v___x_388_);
v___x_423_ = l_Lean_Syntax_getArgs(v___x_422_);
lean_dec(v___x_422_);
v___x_424_ = 0;
v___x_425_ = l_Lean_SourceInfo_fromRef(v_ref_421_, v___x_424_);
v___x_426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8));
v___x_427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10));
v___x_428_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
lean_inc_n(v___x_425_, 4);
v___x_429_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_429_, 0, v___x_425_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_428_);
v___x_430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11));
v___x_431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_425_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
v___x_433_ = l_Array_append___redArg(v___x_428_, v___x_423_);
lean_dec_ref(v___x_423_);
v___x_434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_434_, 0, v___x_425_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
lean_ctor_set(v___x_434_, 2, v___x_433_);
v___x_435_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48));
v___x_436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_425_);
lean_ctor_set(v___x_436_, 1, v___x_435_);
v___x_437_ = l_Lean_Syntax_node5(v___x_425_, v___x_426_, v___x_429_, v___x_431_, v___x_434_, v___x_436_, v_a_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_437_);
v___x_439_ = v___x_419_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_dec(v___x_388_);
return v___x_416_;
}
}
}
}
}
}
else
{
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___boxed(lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
lean_dec(v_a_448_);
lean_dec_ref(v_a_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_451_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___boxed(lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(lean_object* v_00_u03b1_467_, lean_object* v_child_468_, lean_object* v_childIdx_469_, lean_object* v_x_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_468_, v_childIdx_469_, v_x_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___boxed(lean_object* v_00_u03b1_479_, lean_object* v_child_480_, lean_object* v_childIdx_481_, lean_object* v_x_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(v_00_u03b1_479_, v_child_480_, v_childIdx_481_, v_x_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(lean_object* v_00_u03b1_491_, lean_object* v_x_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___boxed(lean_object* v_00_u03b1_501_, lean_object* v_x_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(v_00_u03b1_501_, v_x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_511_, v___y_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___boxed(lean_object* v_x_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(v_x_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1(){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_568_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0));
v___x_570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15));
v___x_571_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___boxed), 7, 0);
v___x_572_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_568_, v___x_569_, v___x_570_, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___boxed(lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
return v_res_574_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1));
v___x_582_ = lean_mk_syntax_ident(v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0));
v___x_597_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_596_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_669_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_669_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_669_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_669_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12));
lean_inc(v_a_598_);
v___x_603_ = l_Lean_Syntax_isOfKind(v_a_598_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v_ref_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v_ref_604_ = lean_ctor_get(v_a_593_, 5);
v___x_605_ = l_Lean_SourceInfo_fromRef(v_ref_604_, v___x_603_);
v___x_606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_607_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
v___x_608_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_605_);
v___x_609_ = l_Lean_Syntax_node1(v___x_605_, v___x_608_, v_a_598_);
v___x_610_ = l_Lean_Syntax_node2(v___x_605_, v___x_606_, v___x_607_, v___x_609_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_610_);
v___x_612_ = v___x_600_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = l_Lean_Syntax_getArg(v_a_598_, v___x_614_);
v___x_616_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46));
lean_inc(v___x_615_);
v___x_617_ = l_Lean_Syntax_isOfKind(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v_ref_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
lean_dec(v___x_615_);
v_ref_618_ = lean_ctor_get(v_a_593_, 5);
v___x_619_ = l_Lean_SourceInfo_fromRef(v_ref_618_, v___x_617_);
v___x_620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_621_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
v___x_622_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_619_);
v___x_623_ = l_Lean_Syntax_node1(v___x_619_, v___x_622_, v_a_598_);
v___x_624_ = l_Lean_Syntax_node2(v___x_619_, v___x_620_, v___x_621_, v___x_623_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_624_);
v___x_626_ = v___x_600_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = l_Lean_Syntax_getArg(v___x_615_, v___x_614_);
v___x_630_ = l_Lean_Syntax_matchesNull(v___x_629_, v___x_628_);
if (v___x_630_ == 0)
{
lean_object* v_ref_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
lean_dec(v___x_615_);
v_ref_631_ = lean_ctor_get(v_a_593_, 5);
v___x_632_ = l_Lean_SourceInfo_fromRef(v_ref_631_, v___x_630_);
v___x_633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_634_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
v___x_635_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_632_);
v___x_636_ = l_Lean_Syntax_node1(v___x_632_, v___x_635_, v_a_598_);
v___x_637_ = l_Lean_Syntax_node2(v___x_632_, v___x_633_, v___x_634_, v___x_636_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_637_);
v___x_639_ = v___x_600_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
lean_del_object(v___x_600_);
lean_dec(v_a_598_);
v___x_641_ = lean_unsigned_to_nat(3u);
v___x_642_ = l_Lean_Syntax_getArg(v___x_615_, v___x_641_);
v___x_643_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_642_, v_a_593_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_668_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_668_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_668_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_668_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_ref_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_666_; 
v_ref_648_ = lean_ctor_get(v_a_593_, 5);
v___x_649_ = l_Lean_Syntax_getArg(v___x_615_, v___x_628_);
lean_dec(v___x_615_);
v___x_650_ = l_Lean_Syntax_getArgs(v___x_649_);
lean_dec(v___x_649_);
v___x_651_ = 0;
v___x_652_ = l_Lean_SourceInfo_fromRef(v_ref_648_, v___x_651_);
v___x_653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4));
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10));
v___x_655_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
lean_inc_n(v___x_652_, 4);
v___x_656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_656_, 0, v___x_652_);
lean_ctor_set(v___x_656_, 1, v___x_654_);
lean_ctor_set(v___x_656_, 2, v___x_655_);
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5));
v___x_658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_652_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
v___x_660_ = l_Array_append___redArg(v___x_655_, v___x_650_);
lean_dec_ref(v___x_650_);
v___x_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_661_, 0, v___x_652_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
lean_ctor_set(v___x_661_, 2, v___x_660_);
v___x_662_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48));
v___x_663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_652_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Lean_Syntax_node5(v___x_652_, v___x_653_, v___x_656_, v___x_658_, v___x_661_, v___x_663_, v_a_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_664_);
v___x_666_ = v___x_646_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_dec(v___x_615_);
return v___x_643_;
}
}
}
}
}
}
else
{
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___boxed(lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1(){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_686_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0));
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2));
v___x_689_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___boxed), 7, 0);
v___x_690_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_686_, v___x_687_, v___x_688_, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___boxed(lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
return v_res_692_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_box(0);
v___x_694_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg(){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0);
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___boxed(lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(lean_object* v_00_u03b1_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___boxed(lean_object* v_00_u03b1_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(v_00_u03b1_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(lean_object* v_e_719_, lean_object* v___y_720_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_Expr_hasMVar(v_e_719_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_e_719_);
return v___x_723_;
}
else
{
lean_object* v___x_724_; lean_object* v_mctx_725_; lean_object* v___x_726_; lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_729_; lean_object* v_cache_730_; lean_object* v_zetaDeltaFVarIds_731_; lean_object* v_postponed_732_; lean_object* v_diag_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_742_; 
v___x_724_ = lean_st_ref_get(v___y_720_);
v_mctx_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_mctx_725_);
lean_dec(v___x_724_);
v___x_726_ = l_Lean_instantiateMVarsCore(v_mctx_725_, v_e_719_);
v_fst_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_fst_727_);
v_snd_728_ = lean_ctor_get(v___x_726_, 1);
lean_inc(v_snd_728_);
lean_dec_ref(v___x_726_);
v___x_729_ = lean_st_ref_take(v___y_720_);
v_cache_730_ = lean_ctor_get(v___x_729_, 1);
v_zetaDeltaFVarIds_731_ = lean_ctor_get(v___x_729_, 2);
v_postponed_732_ = lean_ctor_get(v___x_729_, 3);
v_diag_733_ = lean_ctor_get(v___x_729_, 4);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_743_);
v___x_735_ = v___x_729_;
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_diag_733_);
lean_inc(v_postponed_732_);
lean_inc(v_zetaDeltaFVarIds_731_);
lean_inc(v_cache_730_);
lean_dec(v___x_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_snd_728_);
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_snd_728_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_cache_730_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v_zetaDeltaFVarIds_731_);
lean_ctor_set(v_reuseFailAlloc_741_, 3, v_postponed_732_);
lean_ctor_set(v_reuseFailAlloc_741_, 4, v_diag_733_);
v___x_738_ = v_reuseFailAlloc_741_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_st_ref_set(v___y_720_, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_fst_727_);
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg___boxed(lean_object* v_e_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_744_, v___y_745_);
lean_dec(v___y_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(lean_object* v_e_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_748_, v___y_752_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___boxed(lean_object* v_e_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(v_e_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(lean_object* v_msgData_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; lean_object* v_env_773_; lean_object* v___x_774_; lean_object* v_mctx_775_; lean_object* v_lctx_776_; lean_object* v_options_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_772_ = lean_st_ref_get(v___y_770_);
v_env_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc_ref(v_env_773_);
lean_dec(v___x_772_);
v___x_774_ = lean_st_ref_get(v___y_768_);
v_mctx_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc_ref(v_mctx_775_);
lean_dec(v___x_774_);
v_lctx_776_ = lean_ctor_get(v___y_767_, 2);
v_options_777_ = lean_ctor_get(v___y_769_, 2);
lean_inc_ref(v_options_777_);
lean_inc_ref(v_lctx_776_);
v___x_778_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_778_, 0, v_env_773_);
lean_ctor_set(v___x_778_, 1, v_mctx_775_);
lean_ctor_set(v___x_778_, 2, v_lctx_776_);
lean_ctor_set(v___x_778_, 3, v_options_777_);
v___x_779_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v_msgData_766_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2___boxed(lean_object* v_msgData_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msgData_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_787_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_box(1);
v___x_789_ = l_Lean_MessageData_ofFormat(v___x_788_);
return v___x_789_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2));
v___x_794_ = l_Lean_MessageData_ofFormat(v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(lean_object* v_x_795_, lean_object* v_x_796_){
_start:
{
if (lean_obj_tag(v_x_796_) == 0)
{
return v_x_795_;
}
else
{
lean_object* v_head_797_; lean_object* v_tail_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_820_; 
v_head_797_ = lean_ctor_get(v_x_796_, 0);
v_tail_798_ = lean_ctor_get(v_x_796_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_x_796_);
if (v_isSharedCheck_820_ == 0)
{
v___x_800_ = v_x_796_;
v_isShared_801_ = v_isSharedCheck_820_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_tail_798_);
lean_inc(v_head_797_);
lean_dec(v_x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_820_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_before_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_818_; 
v_before_802_ = lean_ctor_get(v_head_797_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_head_797_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_head_797_, 1);
lean_dec(v_unused_819_);
v___x_804_ = v_head_797_;
v_isShared_805_ = v_isSharedCheck_818_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_before_802_);
lean_dec(v_head_797_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_818_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 7);
lean_ctor_set(v___x_804_, 1, v___x_806_);
lean_ctor_set(v___x_804_, 0, v_x_795_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_x_795_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_817_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 7);
lean_ctor_set(v___x_800_, 1, v___x_809_);
lean_ctor_set(v___x_800_, 0, v___x_808_);
v___x_811_ = v___x_800_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_816_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = l_Lean_MessageData_ofSyntax(v_before_802_);
v___x_813_ = l_Lean_indentD(v___x_812_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_811_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v_x_795_ = v___x_814_;
v_x_796_ = v_tail_798_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(lean_object* v_opts_821_, lean_object* v_opt_822_){
_start:
{
lean_object* v_name_823_; lean_object* v_defValue_824_; lean_object* v_map_825_; lean_object* v___x_826_; 
v_name_823_ = lean_ctor_get(v_opt_822_, 0);
v_defValue_824_ = lean_ctor_get(v_opt_822_, 1);
v_map_825_ = lean_ctor_get(v_opts_821_, 0);
v___x_826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_825_, v_name_823_);
if (lean_obj_tag(v___x_826_) == 0)
{
uint8_t v___x_827_; 
v___x_827_ = lean_unbox(v_defValue_824_);
return v___x_827_;
}
else
{
lean_object* v_val_828_; 
v_val_828_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_828_);
lean_dec_ref(v___x_826_);
if (lean_obj_tag(v_val_828_) == 1)
{
uint8_t v_v_829_; 
v_v_829_ = lean_ctor_get_uint8(v_val_828_, 0);
lean_dec_ref(v_val_828_);
return v_v_829_;
}
else
{
uint8_t v___x_830_; 
lean_dec(v_val_828_);
v___x_830_ = lean_unbox(v_defValue_824_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_831_, lean_object* v_opt_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_opts_831_, v_opt_832_);
lean_dec_ref(v_opt_832_);
lean_dec_ref(v_opts_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1));
v___x_839_ = l_Lean_MessageData_ofFormat(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(lean_object* v_msgData_840_, lean_object* v_macroStack_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_options_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_options_844_ = lean_ctor_get(v___y_842_, 2);
v___x_845_ = l_Lean_Elab_pp_macroStack;
v___x_846_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_options_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec(v_macroStack_841_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_msgData_840_);
return v___x_847_;
}
else
{
if (lean_obj_tag(v_macroStack_841_) == 0)
{
lean_object* v___x_848_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_msgData_840_);
return v___x_848_;
}
else
{
lean_object* v_head_849_; lean_object* v_after_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_865_; 
v_head_849_ = lean_ctor_get(v_macroStack_841_, 0);
lean_inc(v_head_849_);
v_after_850_ = lean_ctor_get(v_head_849_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_head_849_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v_head_849_, 0);
lean_dec(v_unused_866_);
v___x_852_ = v_head_849_;
v_isShared_853_ = v_isSharedCheck_865_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_after_850_);
lean_dec(v_head_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_865_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 7);
lean_ctor_set(v___x_852_, 1, v___x_854_);
lean_ctor_set(v___x_852_, 0, v_msgData_840_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_msgData_840_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_864_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_msgData_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_857_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_MessageData_ofSyntax(v_after_850_);
v___x_860_ = l_Lean_indentD(v___x_859_);
v_msgData_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_861_, 0, v___x_858_);
lean_ctor_set(v_msgData_861_, 1, v___x_860_);
v___x_862_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(v_msgData_861_, v_macroStack_841_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_867_, lean_object* v_macroStack_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_867_, v_macroStack_868_, v___y_869_);
lean_dec_ref(v___y_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(lean_object* v_msg_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_ref_880_; lean_object* v___x_881_; lean_object* v_a_882_; lean_object* v_macroStack_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_ref_880_ = lean_ctor_get(v___y_877_, 5);
v___x_881_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msg_872_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref(v___x_881_);
v_macroStack_883_ = lean_ctor_get(v___y_873_, 1);
lean_inc_n(v_macroStack_883_, 2);
v___x_884_ = l_Lean_Elab_getBetterRef(v_ref_880_, v_macroStack_883_);
v___x_885_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_a_882_, v_macroStack_883_, v___y_877_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_884_);
lean_ctor_set(v___x_890_, 1, v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 1);
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg___boxed(lean_object* v_msg_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_903_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(lean_object* v_x_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1));
lean_inc(v_x_943_);
v___x_952_ = l_Lean_Syntax_isOfKind(v_x_943_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec(v_x_943_);
v___x_953_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
return v___x_953_;
}
else
{
lean_object* v_fileName_954_; lean_object* v_fileMap_955_; lean_object* v_options_956_; lean_object* v_currRecDepth_957_; lean_object* v_maxRecDepth_958_; lean_object* v_ref_959_; lean_object* v_currNamespace_960_; lean_object* v_openDecls_961_; lean_object* v_initHeartbeats_962_; lean_object* v_maxHeartbeats_963_; lean_object* v_quotContext_964_; lean_object* v_currMacroScope_965_; uint8_t v_diag_966_; lean_object* v_cancelTk_x3f_967_; uint8_t v_suppressElabErrors_968_; lean_object* v_inheritedTraceOptions_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_ref_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_fileName_954_ = lean_ctor_get(v_a_948_, 0);
v_fileMap_955_ = lean_ctor_get(v_a_948_, 1);
v_options_956_ = lean_ctor_get(v_a_948_, 2);
v_currRecDepth_957_ = lean_ctor_get(v_a_948_, 3);
v_maxRecDepth_958_ = lean_ctor_get(v_a_948_, 4);
v_ref_959_ = lean_ctor_get(v_a_948_, 5);
v_currNamespace_960_ = lean_ctor_get(v_a_948_, 6);
v_openDecls_961_ = lean_ctor_get(v_a_948_, 7);
v_initHeartbeats_962_ = lean_ctor_get(v_a_948_, 8);
v_maxHeartbeats_963_ = lean_ctor_get(v_a_948_, 9);
v_quotContext_964_ = lean_ctor_get(v_a_948_, 10);
v_currMacroScope_965_ = lean_ctor_get(v_a_948_, 11);
v_diag_966_ = lean_ctor_get_uint8(v_a_948_, sizeof(void*)*14);
v_cancelTk_x3f_967_ = lean_ctor_get(v_a_948_, 12);
v_suppressElabErrors_968_ = lean_ctor_get_uint8(v_a_948_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_969_ = lean_ctor_get(v_a_948_, 13);
v___x_970_ = lean_unsigned_to_nat(3u);
v___x_971_ = l_Lean_Syntax_getArg(v_x_943_, v___x_970_);
v___x_972_ = lean_box(0);
v_ref_973_ = l_Lean_replaceRef(v___x_971_, v_ref_959_);
lean_inc_ref(v_inheritedTraceOptions_969_);
lean_inc(v_cancelTk_x3f_967_);
lean_inc(v_currMacroScope_965_);
lean_inc(v_quotContext_964_);
lean_inc(v_maxHeartbeats_963_);
lean_inc(v_initHeartbeats_962_);
lean_inc(v_openDecls_961_);
lean_inc(v_currNamespace_960_);
lean_inc(v_maxRecDepth_958_);
lean_inc(v_currRecDepth_957_);
lean_inc_ref(v_options_956_);
lean_inc_ref(v_fileMap_955_);
lean_inc_ref(v_fileName_954_);
v___x_974_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_974_, 0, v_fileName_954_);
lean_ctor_set(v___x_974_, 1, v_fileMap_955_);
lean_ctor_set(v___x_974_, 2, v_options_956_);
lean_ctor_set(v___x_974_, 3, v_currRecDepth_957_);
lean_ctor_set(v___x_974_, 4, v_maxRecDepth_958_);
lean_ctor_set(v___x_974_, 5, v_ref_973_);
lean_ctor_set(v___x_974_, 6, v_currNamespace_960_);
lean_ctor_set(v___x_974_, 7, v_openDecls_961_);
lean_ctor_set(v___x_974_, 8, v_initHeartbeats_962_);
lean_ctor_set(v___x_974_, 9, v_maxHeartbeats_963_);
lean_ctor_set(v___x_974_, 10, v_quotContext_964_);
lean_ctor_set(v___x_974_, 11, v_currMacroScope_965_);
lean_ctor_set(v___x_974_, 12, v_cancelTk_x3f_967_);
lean_ctor_set(v___x_974_, 13, v_inheritedTraceOptions_969_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*14, v_diag_966_);
lean_ctor_set_uint8(v___x_974_, sizeof(void*)*14 + 1, v_suppressElabErrors_968_);
v___x_975_ = l_Lean_Elab_Term_elabTerm(v___x_971_, v___x_972_, v___x_952_, v___x_952_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_n(v_a_976_, 2);
lean_dec_ref(v___x_975_);
lean_inc(v_a_949_);
lean_inc_ref(v___x_974_);
lean_inc(v_a_947_);
lean_inc_ref(v_a_946_);
v___x_977_ = lean_infer_type(v_a_976_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc_n(v_a_978_, 2);
lean_dec_ref(v___x_977_);
v___x_979_ = l_Lean_Elab_Term_tryPostponeIfMVar(v_a_978_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v___x_980_; lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v___x_979_);
v___x_980_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_a_978_, v_a_947_);
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1114_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1114_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_fst_990_; lean_object* v_fst_991_; lean_object* v_fst_992_; lean_object* v_fst_993_; lean_object* v_fst_994_; lean_object* v_fst_995_; lean_object* v_snd_996_; lean_object* v___y_1040_; lean_object* v___x_1049_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = l_Lean_Syntax_getArg(v_x_943_, v___x_985_);
v___x_987_ = lean_unsigned_to_nat(5u);
v___x_988_ = l_Lean_Syntax_getArg(v_x_943_, v___x_987_);
lean_dec(v_x_943_);
v___x_1049_ = l_Lean_Expr_consumeMData(v_a_981_);
if (lean_obj_tag(v___x_1049_) == 5)
{
lean_object* v_fn_1050_; lean_object* v_arg_1051_; lean_object* v___x_1052_; 
v_fn_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc_ref(v_fn_1050_);
v_arg_1051_ = lean_ctor_get(v___x_1049_, 1);
lean_inc_ref_n(v_arg_1051_, 2);
lean_dec_ref(v___x_1049_);
v___x_1052_ = l_Lean_Meta_getLevel(v_arg_1051_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_Lean_Level_dec(v_a_1053_);
lean_dec(v_a_1053_);
if (lean_obj_tag(v___x_1054_) == 1)
{
lean_object* v_val_1055_; lean_object* v___x_1056_; 
v_val_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_val_1055_);
lean_dec_ref(v___x_1054_);
lean_inc(v_a_981_);
v___x_1056_ = l_Lean_Meta_getLevel(v_a_981_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = l_Lean_Level_dec(v_a_1057_);
lean_dec(v_a_1057_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v_a_981_);
v_val_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1081_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1081_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9));
v___x_1064_ = lean_box(0);
lean_inc(v_val_1055_);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_val_1055_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_mkConst(v___x_1063_, v___x_1065_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1066_);
v___x_1068_ = v___x_1061_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = 0;
v___x_1070_ = lean_box(0);
v___x_1071_ = l_Lean_Meta_mkFreshExprMVar(v___x_1068_, v___x_1069_, v___x_1070_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc_n(v_a_1072_, 2);
lean_dec_ref(v___x_1071_);
v___x_1073_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11));
lean_inc(v_val_1059_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_val_1059_);
lean_ctor_set(v___x_1074_, 1, v___x_1064_);
lean_inc(v_val_1055_);
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_val_1055_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_mkConst(v___x_1073_, v___x_1075_);
lean_inc_ref(v_fn_1050_);
v___x_1077_ = l_Lean_mkAppB(v___x_1076_, v_fn_1050_, v_a_1072_);
v___x_1078_ = l_Lean_Meta_synthInstance(v___x_1077_, v___x_972_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
lean_dec_ref(v___x_974_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref(v___x_1078_);
v_fst_990_ = v_val_1055_;
v_fst_991_ = v_val_1059_;
v_fst_992_ = v_fn_1050_;
v_fst_993_ = v_arg_1051_;
v_fst_994_ = v_a_1072_;
v_fst_995_ = v_a_1079_;
v_snd_996_ = v_a_976_;
goto v___jp_989_;
}
else
{
lean_dec(v_a_1072_);
lean_dec(v_val_1059_);
lean_dec(v_val_1055_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_fn_1050_);
lean_dec(v___x_988_);
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_dec(v_a_976_);
return v___x_1078_;
}
}
else
{
lean_dec(v_val_1059_);
lean_dec(v_val_1055_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_fn_1050_);
lean_dec(v___x_988_);
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_dec(v_a_976_);
lean_dec_ref(v___x_974_);
return v___x_1071_;
}
}
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v___x_1058_);
lean_dec(v_val_1055_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_fn_1050_);
lean_dec(v___x_988_);
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_dec(v_a_976_);
v___x_1082_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
v___x_1083_ = l_Lean_MessageData_ofExpr(v_a_981_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_1084_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
lean_dec_ref(v___x_974_);
v___y_1040_ = v___x_1085_;
goto v___jp_1039_;
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec(v_val_1055_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_fn_1050_);
lean_dec(v___x_988_);
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_dec(v_a_981_);
lean_dec(v_a_976_);
lean_dec_ref(v___x_974_);
v_a_1086_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1056_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1056_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_dec(v___x_1054_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_fn_1050_);
lean_dec(v___x_988_);
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_dec(v_a_976_);
v___x_1094_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
v___x_1095_ = l_Lean_MessageData_ofExpr(v_a_981_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_1096_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
lean_dec_ref(v___x_974_);
v___y_1040_ = v___x_1097_;
goto v___jp_1039_;
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_fn_1050_);
lean_dec(v___x_988_);
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
lean_dec(v_a_981_);
lean_dec(v_a_976_);
lean_dec_ref(v___x_974_);
v_a_1098_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1052_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1052_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec_ref(v___x_1049_);
lean_dec(v___x_988_);
lean_dec(v___x_986_);
lean_del_object(v___x_983_);
v___x_1106_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15);
v___x_1107_ = l_Lean_MessageData_ofExpr(v_a_976_);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_Lean_MessageData_ofExpr(v_a_981_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_1112_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v___x_974_, v_a_949_);
lean_dec_ref(v___x_974_);
v___y_1040_ = v___x_1113_;
goto v___jp_1039_;
}
v___jp_989_:
{
uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_997_ = 0;
v___x_998_ = l_Lean_SourceInfo_fromRef(v_ref_959_, v___x_997_);
v___x_999_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3));
v___x_1000_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2));
lean_inc_n(v___x_998_, 2);
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_998_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44));
v___x_1003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_998_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node3(v___x_998_, v___x_999_, v___x_1001_, v___x_986_, v___x_1003_);
v___x_1005_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4));
v___x_1006_ = lean_box(0);
lean_inc(v_fst_990_);
v___x_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_fst_990_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_inc_ref(v___x_1007_);
v___x_1008_ = l_Lean_mkConst(v___x_1005_, v___x_1007_);
lean_inc_ref(v_fst_994_);
v___x_1009_ = l_Lean_Expr_app___override(v___x_1008_, v_fst_994_);
if (v_isShared_984_ == 0)
{
lean_ctor_set_tag(v___x_983_, 1);
lean_ctor_set(v___x_983_, 0, v___x_1009_);
v___x_1011_ = v___x_983_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Elab_Term_elabTerm(v___x_1004_, v___x_1011_, v___x_952_, v___x_952_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1037_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1037_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1037_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1017_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5));
v___x_1018_ = l_Lean_mkConst(v___x_1017_, v___x_1007_);
lean_inc_ref(v_fst_994_);
lean_inc_ref(v_fst_993_);
v___x_1019_ = l_Lean_mkAppB(v___x_1018_, v_fst_993_, v_fst_994_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 1);
lean_ctor_set(v___x_1015_, 0, v___x_1019_);
v___x_1021_ = v___x_1015_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Elab_Term_elabTerm(v___x_988_, v___x_1021_, v___x_952_, v___x_952_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1035_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1035_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1035_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7));
v___x_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_fst_991_);
lean_ctor_set(v___x_1028_, 1, v___x_1006_);
v___x_1029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1029_, 0, v_fst_990_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = l_Lean_mkConst(v___x_1027_, v___x_1029_);
v___x_1031_ = l_Lean_mkApp7(v___x_1030_, v_fst_992_, v_fst_994_, v_fst_995_, v_fst_993_, v_snd_996_, v_a_1013_, v_a_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1031_);
v___x_1033_ = v___x_1025_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_dec(v_a_1013_);
lean_dec_ref(v_snd_996_);
lean_dec_ref(v_fst_995_);
lean_dec_ref(v_fst_994_);
lean_dec_ref(v_fst_993_);
lean_dec_ref(v_fst_992_);
lean_dec(v_fst_991_);
lean_dec(v_fst_990_);
return v___x_1022_;
}
}
}
}
else
{
lean_dec_ref(v___x_1007_);
lean_dec_ref(v_snd_996_);
lean_dec_ref(v_fst_995_);
lean_dec_ref(v_fst_994_);
lean_dec_ref(v_fst_993_);
lean_dec_ref(v_fst_992_);
lean_dec(v_fst_991_);
lean_dec(v_fst_990_);
lean_dec(v___x_988_);
return v___x_1012_;
}
}
}
v___jp_1039_:
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_a_1041_ = lean_ctor_get(v___y_1040_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___y_1040_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___y_1040_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___y_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v_a_978_);
lean_dec(v_a_976_);
lean_dec_ref(v___x_974_);
lean_dec(v_x_943_);
v_a_1115_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_979_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_979_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
else
{
lean_dec(v_a_976_);
lean_dec_ref(v___x_974_);
lean_dec(v_x_943_);
return v___x_977_;
}
}
else
{
lean_dec_ref(v___x_974_);
lean_dec(v_x_943_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___boxed(lean_object* v_x_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(v_x_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(v_x_1132_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed(lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(v_x_1142_, v_x_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_x_1143_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(lean_object* v_00_u03b1_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___boxed(lean_object* v_00_u03b1_1162_, lean_object* v_msg_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(v_00_u03b1_1162_, v_msg_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(lean_object* v_msgData_1172_, lean_object* v_macroStack_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_1172_, v_macroStack_1173_, v___y_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___boxed(lean_object* v_msgData_1182_, lean_object* v_macroStack_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(v_msgData_1182_, v_macroStack_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1(){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1197_ = l_Lean_Elab_Term_termElabAttribute;
v___x_1198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1));
v___x_1199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1));
v___x_1200_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed), 9, 0);
v___x_1201_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1197_, v___x_1198_, v___x_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___boxed(lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
return v_res_1203_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
lean_object* runtime_initialize_Std_Do_Triple_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
lean_object* initialize_Std_Do_Triple_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_BuiltinNotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
