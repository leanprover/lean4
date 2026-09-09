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
lean_object* l_Lean_mkIdent(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* v_toCold_141_; lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_169_; 
v_toCold_141_ = lean_ctor_get(v___y_107_, 0);
v_a_142_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_169_ == 0)
{
v___x_144_ = v___x_140_;
v_isShared_145_ = v_isSharedCheck_169_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_140_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_169_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v_ref_146_; lean_object* v_currMacroScope_147_; lean_object* v_quotContext_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v_ref_146_ = lean_ctor_get(v___y_107_, 4);
v_currMacroScope_147_ = lean_ctor_get(v___y_107_, 9);
v_quotContext_148_ = lean_ctor_get(v_toCold_141_, 2);
v___x_149_ = l_Lean_Syntax_getArg(v___x_136_, v___x_121_);
lean_dec(v___x_136_);
v___x_150_ = l_Lean_SourceInfo_fromRef(v_ref_146_, v___x_117_);
v___x_151_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19));
lean_inc_n(v___x_150_, 7);
v___x_152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
lean_inc(v_currMacroScope_147_);
lean_inc(v_quotContext_148_);
v___x_154_ = l_Lean_addMacroScope(v_quotContext_148_, v___x_132_, v_currMacroScope_147_);
v___x_155_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40));
v___x_156_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_156_, 0, v___x_150_);
lean_ctor_set(v___x_156_, 1, v___x_153_);
lean_ctor_set(v___x_156_, 2, v___x_154_);
lean_ctor_set(v___x_156_, 3, v___x_155_);
v___x_157_ = l_Lean_Syntax_node1(v___x_150_, v___x_128_, v___x_156_);
v___x_158_ = l_Lean_Syntax_node2(v___x_150_, v___x_123_, v___x_152_, v___x_157_);
v___x_159_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41));
v___x_160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_150_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
v___x_162_ = l_Lean_Syntax_node1(v___x_150_, v___x_161_, v___x_149_);
v___x_163_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44));
v___x_164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_150_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = l_Lean_Syntax_node5(v___x_150_, v___x_118_, v___x_158_, v_a_142_, v___x_160_, v___x_162_, v___x_164_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_165_);
v___x_167_ = v___x_144_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
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
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = l_Lean_Syntax_getArg(v_x_106_, v___x_170_);
v___x_172_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46));
lean_inc(v___x_171_);
v___x_173_ = l_Lean_Syntax_isOfKind(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_dec(v___x_171_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v_x_106_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = l_Lean_Syntax_getArg(v___x_171_, v___x_170_);
v___x_177_ = l_Lean_Syntax_matchesNull(v___x_176_, v___x_175_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
lean_dec(v___x_171_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v_x_106_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v_b_180_; lean_object* v___x_181_; 
lean_dec(v_x_106_);
v___x_179_ = lean_unsigned_to_nat(3u);
v_b_180_ = l_Lean_Syntax_getArg(v___x_171_, v___x_179_);
v___x_181_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_b_180_, v___y_107_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_203_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_203_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_203_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_203_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_ref_186_; lean_object* v___x_187_; lean_object* v_xs_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v_ref_186_ = lean_ctor_get(v___y_107_, 4);
v___x_187_ = l_Lean_Syntax_getArg(v___x_171_, v___x_175_);
lean_dec(v___x_171_);
v_xs_188_ = l_Lean_Syntax_getArgs(v___x_187_);
lean_dec(v___x_187_);
v___x_189_ = l_Lean_SourceInfo_fromRef(v_ref_186_, v___x_114_);
lean_inc_n(v___x_189_, 5);
v___x_190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_115_);
v___x_191_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
v___x_192_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
v___x_193_ = l_Array_append___redArg(v___x_192_, v_xs_188_);
lean_dec_ref(v_xs_188_);
v___x_194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_194_, 0, v___x_189_);
lean_ctor_set(v___x_194_, 1, v___x_191_);
lean_ctor_set(v___x_194_, 2, v___x_193_);
v___x_195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_195_, 0, v___x_189_);
lean_ctor_set(v___x_195_, 1, v___x_191_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
v___x_196_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48));
v___x_197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_189_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = l_Lean_Syntax_node4(v___x_189_, v___x_172_, v___x_194_, v___x_195_, v___x_197_, v_a_182_);
v___x_199_ = l_Lean_Syntax_node2(v___x_189_, v___x_116_, v___x_190_, v___x_198_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_199_);
v___x_201_ = v___x_184_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_dec(v___x_171_);
return v___x_181_;
}
}
}
}
}
else
{
lean_object* v___x_204_; lean_object* v_t_205_; lean_object* v___x_206_; 
v___x_204_ = lean_unsigned_to_nat(3u);
v_t_205_ = l_Lean_Syntax_getArg(v_x_106_, v___x_204_);
v___x_206_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_t_205_, v___y_107_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; lean_object* v_e_209_; lean_object* v___x_210_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = lean_unsigned_to_nat(5u);
v_e_209_ = l_Lean_Syntax_getArg(v_x_106_, v___x_208_);
v___x_210_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_e_209_, v___y_107_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_229_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_229_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_229_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_229_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_ref_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v_ref_215_ = lean_ctor_get(v___y_107_, 4);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = l_Lean_Syntax_getArg(v_x_106_, v___x_216_);
lean_dec(v_x_106_);
v___x_218_ = l_Lean_SourceInfo_fromRef(v_ref_215_, v___x_112_);
v___x_219_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49));
lean_inc_n(v___x_218_, 3);
v___x_220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50));
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_218_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51));
v___x_224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_218_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = l_Lean_Syntax_node6(v___x_218_, v___x_113_, v___x_220_, v___x_217_, v___x_222_, v_a_207_, v___x_224_, v_a_211_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_225_);
v___x_227_ = v___x_213_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
else
{
lean_dec(v_a_207_);
lean_dec(v_x_106_);
return v___x_210_;
}
}
else
{
lean_dec(v_x_106_);
return v___x_206_;
}
}
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l_Lean_Syntax_getArg(v_x_106_, v___x_230_);
v___x_232_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16));
lean_inc(v___x_231_);
v___x_233_ = l_Lean_Syntax_isOfKind(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_dec(v___x_231_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v_x_106_);
return v___x_234_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = l_Lean_Syntax_getArg(v___x_231_, v___x_235_);
lean_dec(v___x_231_);
v___x_237_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18));
lean_inc(v___x_236_);
v___x_238_ = l_Lean_Syntax_isOfKind(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v___x_236_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v_x_106_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = l_Lean_Syntax_getArg(v___x_236_, v___x_230_);
lean_dec(v___x_236_);
v___x_241_ = lean_box(0);
v___x_242_ = l_Lean_Syntax_matchesIdent(v___x_240_, v___x_241_);
lean_dec(v___x_240_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v_x_106_);
return v___x_243_;
}
else
{
lean_object* v_P_244_; lean_object* v___x_245_; 
v_P_244_ = l_Lean_Syntax_getArg(v_x_106_, v___x_235_);
lean_dec(v_x_106_);
v___x_245_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_244_, v___y_107_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_toCold_246_; lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_269_; 
v_toCold_246_ = lean_ctor_get(v___y_107_, 0);
v_a_247_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_269_ == 0)
{
v___x_249_ = v___x_245_;
v_isShared_250_ = v_isSharedCheck_269_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_245_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_269_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_ref_251_; lean_object* v_currMacroScope_252_; lean_object* v_quotContext_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v_ref_251_ = lean_ctor_get(v___y_107_, 4);
v_currMacroScope_252_ = lean_ctor_get(v___y_107_, 9);
v_quotContext_253_ = lean_ctor_get(v_toCold_246_, 2);
v___x_254_ = l_Lean_SourceInfo_fromRef(v_ref_251_, v___x_110_);
v___x_255_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19));
lean_inc_n(v___x_254_, 5);
v___x_256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
lean_inc(v_currMacroScope_252_);
lean_inc(v_quotContext_253_);
v___x_258_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_241_, v_currMacroScope_252_);
v___x_259_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40));
v___x_260_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_260_, 0, v___x_254_);
lean_ctor_set(v___x_260_, 1, v___x_257_);
lean_ctor_set(v___x_260_, 2, v___x_258_);
lean_ctor_set(v___x_260_, 3, v___x_259_);
v___x_261_ = l_Lean_Syntax_node1(v___x_254_, v___x_237_, v___x_260_);
v___x_262_ = l_Lean_Syntax_node2(v___x_254_, v___x_232_, v___x_256_, v___x_261_);
v___x_263_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44));
v___x_264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_254_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = l_Lean_Syntax_node3(v___x_254_, v___x_111_, v___x_262_, v_a_247_, v___x_264_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_265_);
v___x_267_ = v___x_249_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
else
{
return v___x_245_;
}
}
}
}
}
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = l_Lean_Syntax_getArg(v_x_106_, v___x_270_);
lean_dec(v_x_106_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___boxed(lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_273_, v___y_274_);
lean_dec_ref(v___y_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(lean_object* v_child_277_, lean_object* v_childIdx_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_subExpr_287_; lean_object* v_optionsPerPos_288_; lean_object* v_currNamespace_289_; lean_object* v_openDecls_290_; uint8_t v_inPattern_291_; lean_object* v_depth_292_; lean_object* v_lctxInitIndices_293_; lean_object* v_pos_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_subExpr_287_ = lean_ctor_get(v___y_280_, 3);
v_optionsPerPos_288_ = lean_ctor_get(v___y_280_, 0);
v_currNamespace_289_ = lean_ctor_get(v___y_280_, 1);
v_openDecls_290_ = lean_ctor_get(v___y_280_, 2);
v_inPattern_291_ = lean_ctor_get_uint8(v___y_280_, sizeof(void*)*6);
v_depth_292_ = lean_ctor_get(v___y_280_, 4);
v_lctxInitIndices_293_ = lean_ctor_get(v___y_280_, 5);
v_pos_294_ = lean_ctor_get(v_subExpr_287_, 1);
v___x_295_ = l_Lean_SubExpr_Pos_push(v_pos_294_, v_childIdx_278_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_child_277_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
lean_inc(v_lctxInitIndices_293_);
lean_inc(v_depth_292_);
lean_inc(v_openDecls_290_);
lean_inc(v_currNamespace_289_);
lean_inc(v_optionsPerPos_288_);
v___x_297_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_297_, 0, v_optionsPerPos_288_);
lean_ctor_set(v___x_297_, 1, v_currNamespace_289_);
lean_ctor_set(v___x_297_, 2, v_openDecls_290_);
lean_ctor_set(v___x_297_, 3, v___x_296_);
lean_ctor_set(v___x_297_, 4, v_depth_292_);
lean_ctor_set(v___x_297_, 5, v_lctxInitIndices_293_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*6, v_inPattern_291_);
lean_inc(v___y_285_);
lean_inc_ref(v___y_284_);
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
lean_inc(v___y_281_);
v___x_298_ = lean_apply_7(v_x_279_, v___x_297_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, lean_box(0));
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg___boxed(lean_object* v_child_299_, lean_object* v_childIdx_300_, lean_object* v_x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_299_, v_childIdx_300_, v_x_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(lean_object* v___y_310_){
_start:
{
lean_object* v_subExpr_312_; lean_object* v_expr_313_; lean_object* v___x_314_; 
v_subExpr_312_ = lean_ctor_get(v___y_310_, 3);
v_expr_313_ = lean_ctor_get(v_subExpr_312_, 0);
lean_inc_ref(v_expr_313_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v_expr_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg___boxed(lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_315_);
lean_dec_ref(v___y_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(lean_object* v_x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_a_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_326_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_319_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc(v_a_327_);
lean_dec_ref(v___x_326_);
v___x_328_ = l_Lean_Expr_appArg_x21(v_a_327_);
lean_dec(v_a_327_);
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v___x_328_, v___x_329_, v_x_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg___boxed(lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5));
v___x_355_ = l_Lean_mkIdent(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0));
v___x_373_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_372_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_445_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_445_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_445_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_445_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12));
lean_inc(v_a_374_);
v___x_379_ = l_Lean_Syntax_isOfKind(v_a_374_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v_ref_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v_ref_380_ = lean_ctor_get(v_a_369_, 4);
v___x_381_ = l_Lean_SourceInfo_fromRef(v_ref_380_, v___x_379_);
v___x_382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_383_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
v___x_384_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_381_);
v___x_385_ = l_Lean_Syntax_node1(v___x_381_, v___x_384_, v_a_374_);
v___x_386_ = l_Lean_Syntax_node2(v___x_381_, v___x_382_, v___x_383_, v___x_385_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_386_);
v___x_388_ = v___x_376_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = l_Lean_Syntax_getArg(v_a_374_, v___x_390_);
v___x_392_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46));
lean_inc(v___x_391_);
v___x_393_ = l_Lean_Syntax_isOfKind(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v_ref_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
lean_dec(v___x_391_);
v_ref_394_ = lean_ctor_get(v_a_369_, 4);
v___x_395_ = l_Lean_SourceInfo_fromRef(v_ref_394_, v___x_393_);
v___x_396_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_397_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
v___x_398_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_395_);
v___x_399_ = l_Lean_Syntax_node1(v___x_395_, v___x_398_, v_a_374_);
v___x_400_ = l_Lean_Syntax_node2(v___x_395_, v___x_396_, v___x_397_, v___x_399_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_400_);
v___x_402_ = v___x_376_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l_Lean_Syntax_getArg(v___x_391_, v___x_390_);
v___x_406_ = l_Lean_Syntax_matchesNull(v___x_405_, v___x_404_);
if (v___x_406_ == 0)
{
lean_object* v_ref_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
lean_dec(v___x_391_);
v_ref_407_ = lean_ctor_get(v_a_369_, 4);
v___x_408_ = l_Lean_SourceInfo_fromRef(v_ref_407_, v___x_406_);
v___x_409_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_410_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
v___x_411_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_408_);
v___x_412_ = l_Lean_Syntax_node1(v___x_408_, v___x_411_, v_a_374_);
v___x_413_ = l_Lean_Syntax_node2(v___x_408_, v___x_409_, v___x_410_, v___x_412_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_413_);
v___x_415_ = v___x_376_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_del_object(v___x_376_);
lean_dec(v_a_374_);
v___x_417_ = lean_unsigned_to_nat(3u);
v___x_418_ = l_Lean_Syntax_getArg(v___x_391_, v___x_417_);
v___x_419_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_418_, v_a_369_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_444_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_444_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_444_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_444_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_ref_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v_ref_424_ = lean_ctor_get(v_a_369_, 4);
v___x_425_ = l_Lean_Syntax_getArg(v___x_391_, v___x_404_);
lean_dec(v___x_391_);
v___x_426_ = l_Lean_Syntax_getArgs(v___x_425_);
lean_dec(v___x_425_);
v___x_427_ = 0;
v___x_428_ = l_Lean_SourceInfo_fromRef(v_ref_424_, v___x_427_);
v___x_429_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8));
v___x_430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10));
v___x_431_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
lean_inc_n(v___x_428_, 4);
v___x_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_432_, 0, v___x_428_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_431_);
v___x_433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11));
v___x_434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_428_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
v___x_436_ = l_Array_append___redArg(v___x_431_, v___x_426_);
lean_dec_ref(v___x_426_);
v___x_437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_437_, 0, v___x_428_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
lean_ctor_set(v___x_437_, 2, v___x_436_);
v___x_438_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48));
v___x_439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_428_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_Syntax_node5(v___x_428_, v___x_429_, v___x_432_, v___x_434_, v___x_437_, v___x_439_, v_a_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_440_);
v___x_442_ = v___x_422_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_dec(v___x_391_);
return v___x_419_;
}
}
}
}
}
}
else
{
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___boxed(lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_454_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___boxed(lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(lean_object* v_00_u03b1_470_, lean_object* v_child_471_, lean_object* v_childIdx_472_, lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_471_, v_childIdx_472_, v_x_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___boxed(lean_object* v_00_u03b1_482_, lean_object* v_child_483_, lean_object* v_childIdx_484_, lean_object* v_x_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(v_00_u03b1_482_, v_child_483_, v_childIdx_484_, v_x_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(lean_object* v_00_u03b1_494_, lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___boxed(lean_object* v_00_u03b1_504_, lean_object* v_x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(v_00_u03b1_504_, v_x_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(lean_object* v_x_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_514_, v___y_519_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___boxed(lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(v_x_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1(){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_571_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0));
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15));
v___x_574_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___boxed), 7, 0);
v___x_575_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_571_, v___x_572_, v___x_573_, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___boxed(lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
return v_res_577_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1));
v___x_585_ = l_Lean_mkIdent(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0));
v___x_600_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_599_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_672_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_672_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_672_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_672_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12));
lean_inc(v_a_601_);
v___x_606_ = l_Lean_Syntax_isOfKind(v_a_601_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v_ref_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v_ref_607_ = lean_ctor_get(v_a_596_, 4);
v___x_608_ = l_Lean_SourceInfo_fromRef(v_ref_607_, v___x_606_);
v___x_609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_610_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
v___x_611_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_608_);
v___x_612_ = l_Lean_Syntax_node1(v___x_608_, v___x_611_, v_a_601_);
v___x_613_ = l_Lean_Syntax_node2(v___x_608_, v___x_609_, v___x_610_, v___x_612_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_613_);
v___x_615_ = v___x_603_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = l_Lean_Syntax_getArg(v_a_601_, v___x_617_);
v___x_619_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46));
lean_inc(v___x_618_);
v___x_620_ = l_Lean_Syntax_isOfKind(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v_ref_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_629_; 
lean_dec(v___x_618_);
v_ref_621_ = lean_ctor_get(v_a_596_, 4);
v___x_622_ = l_Lean_SourceInfo_fromRef(v_ref_621_, v___x_620_);
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_624_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
v___x_625_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_622_);
v___x_626_ = l_Lean_Syntax_node1(v___x_622_, v___x_625_, v_a_601_);
v___x_627_ = l_Lean_Syntax_node2(v___x_622_, v___x_623_, v___x_624_, v___x_626_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_627_);
v___x_629_ = v___x_603_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = l_Lean_Syntax_getArg(v___x_618_, v___x_617_);
v___x_633_ = l_Lean_Syntax_matchesNull(v___x_632_, v___x_631_);
if (v___x_633_ == 0)
{
lean_object* v_ref_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
lean_dec(v___x_618_);
v_ref_634_ = lean_ctor_get(v_a_596_, 4);
v___x_635_ = l_Lean_SourceInfo_fromRef(v_ref_634_, v___x_633_);
v___x_636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2));
v___x_637_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
v___x_638_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
lean_inc(v___x_635_);
v___x_639_ = l_Lean_Syntax_node1(v___x_635_, v___x_638_, v_a_601_);
v___x_640_ = l_Lean_Syntax_node2(v___x_635_, v___x_636_, v___x_637_, v___x_639_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_640_);
v___x_642_ = v___x_603_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_del_object(v___x_603_);
lean_dec(v_a_601_);
v___x_644_ = lean_unsigned_to_nat(3u);
v___x_645_ = l_Lean_Syntax_getArg(v___x_618_, v___x_644_);
v___x_646_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_645_, v_a_596_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_671_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_671_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_671_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_671_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v_ref_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v_ref_651_ = lean_ctor_get(v_a_596_, 4);
v___x_652_ = l_Lean_Syntax_getArg(v___x_618_, v___x_631_);
lean_dec(v___x_618_);
v___x_653_ = l_Lean_Syntax_getArgs(v___x_652_);
lean_dec(v___x_652_);
v___x_654_ = 0;
v___x_655_ = l_Lean_SourceInfo_fromRef(v_ref_651_, v___x_654_);
v___x_656_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4));
v___x_657_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10));
v___x_658_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
lean_inc_n(v___x_655_, 4);
v___x_659_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_659_, 0, v___x_655_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
lean_ctor_set(v___x_659_, 2, v___x_658_);
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5));
v___x_661_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_655_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43));
v___x_663_ = l_Array_append___redArg(v___x_658_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_664_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_664_, 0, v___x_655_);
lean_ctor_set(v___x_664_, 1, v___x_662_);
lean_ctor_set(v___x_664_, 2, v___x_663_);
v___x_665_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48));
v___x_666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_655_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_Syntax_node5(v___x_655_, v___x_656_, v___x_659_, v___x_661_, v___x_664_, v___x_666_, v_a_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_667_);
v___x_669_ = v___x_649_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_dec(v___x_618_);
return v___x_646_;
}
}
}
}
}
}
else
{
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___boxed(lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1(){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0));
v___x_691_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2));
v___x_692_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___boxed), 7, 0);
v___x_693_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_689_, v___x_690_, v___x_691_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___boxed(lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
return v_res_695_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_box(0);
v___x_697_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_696_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg(){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0);
v___x_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___boxed(lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(lean_object* v_00_u03b1_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___boxed(lean_object* v_00_u03b1_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(v_00_u03b1_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(lean_object* v_e_722_, lean_object* v___y_723_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = l_Lean_Expr_hasMVar(v_e_722_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_e_722_);
return v___x_726_;
}
else
{
lean_object* v___x_727_; lean_object* v_mctx_728_; lean_object* v___x_729_; lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___x_732_; lean_object* v_cache_733_; lean_object* v_zetaDeltaFVarIds_734_; lean_object* v_postponed_735_; lean_object* v_diag_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_745_; 
v___x_727_ = lean_st_ref_get(v___y_723_);
v_mctx_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc_ref(v_mctx_728_);
lean_dec(v___x_727_);
v___x_729_ = l_Lean_instantiateMVarsCore(v_mctx_728_, v_e_722_);
v_fst_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_fst_730_);
v_snd_731_ = lean_ctor_get(v___x_729_, 1);
lean_inc(v_snd_731_);
lean_dec_ref(v___x_729_);
v___x_732_ = lean_st_ref_take(v___y_723_);
v_cache_733_ = lean_ctor_get(v___x_732_, 1);
v_zetaDeltaFVarIds_734_ = lean_ctor_get(v___x_732_, 2);
v_postponed_735_ = lean_ctor_get(v___x_732_, 3);
v_diag_736_ = lean_ctor_get(v___x_732_, 4);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v___x_732_, 0);
lean_dec(v_unused_746_);
v___x_738_ = v___x_732_;
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_diag_736_);
lean_inc(v_postponed_735_);
lean_inc(v_zetaDeltaFVarIds_734_);
lean_inc(v_cache_733_);
lean_dec(v___x_732_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_745_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v_snd_731_);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_snd_731_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_cache_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_zetaDeltaFVarIds_734_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_postponed_735_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v_diag_736_);
v___x_741_ = v_reuseFailAlloc_744_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_st_ref_put(v___y_723_, v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_fst_730_);
return v___x_743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg___boxed(lean_object* v_e_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_747_, v___y_748_);
lean_dec(v___y_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(lean_object* v_e_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_751_, v___y_755_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___boxed(lean_object* v_e_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(v_e_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(lean_object* v_msgData_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_env_776_; lean_object* v___x_777_; lean_object* v_mctx_778_; lean_object* v_lctx_779_; lean_object* v_options_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_775_ = lean_st_ref_get(v___y_773_);
v_env_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc_ref(v_env_776_);
lean_dec(v___x_775_);
v___x_777_ = lean_st_ref_get(v___y_771_);
v_mctx_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc_ref(v_mctx_778_);
lean_dec(v___x_777_);
v_lctx_779_ = lean_ctor_get(v___y_770_, 2);
v_options_780_ = lean_ctor_get(v___y_772_, 1);
lean_inc_ref(v_options_780_);
lean_inc_ref(v_lctx_779_);
v___x_781_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_781_, 0, v_env_776_);
lean_ctor_set(v___x_781_, 1, v_mctx_778_);
lean_ctor_set(v___x_781_, 2, v_lctx_779_);
lean_ctor_set(v___x_781_, 3, v_options_780_);
v___x_782_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_msgData_769_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2___boxed(lean_object* v_msgData_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msgData_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_790_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_box(1);
v___x_792_ = l_Lean_MessageData_ofFormat(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2));
v___x_797_ = l_Lean_MessageData_ofFormat(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
return v_x_798_;
}
else
{
lean_object* v_head_800_; lean_object* v_tail_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_823_; 
v_head_800_ = lean_ctor_get(v_x_799_, 0);
v_tail_801_ = lean_ctor_get(v_x_799_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_799_);
if (v_isSharedCheck_823_ == 0)
{
v___x_803_ = v_x_799_;
v_isShared_804_ = v_isSharedCheck_823_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_tail_801_);
lean_inc(v_head_800_);
lean_dec(v_x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_823_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_before_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_821_; 
v_before_805_ = lean_ctor_get(v_head_800_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_head_800_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_head_800_, 1);
lean_dec(v_unused_822_);
v___x_807_ = v_head_800_;
v_isShared_808_ = v_isSharedCheck_821_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_before_805_);
lean_dec(v_head_800_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_821_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_808_ == 0)
{
lean_ctor_set_tag(v___x_807_, 7);
lean_ctor_set(v___x_807_, 1, v___x_809_);
lean_ctor_set(v___x_807_, 0, v_x_798_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_x_798_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_820_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 7);
lean_ctor_set(v___x_803_, 1, v___x_812_);
lean_ctor_set(v___x_803_, 0, v___x_811_);
v___x_814_ = v___x_803_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_812_);
v___x_814_ = v_reuseFailAlloc_819_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = l_Lean_MessageData_ofSyntax(v_before_805_);
v___x_816_ = l_Lean_indentD(v___x_815_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_814_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v_x_798_ = v___x_817_;
v_x_799_ = v_tail_801_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(lean_object* v_opts_824_, lean_object* v_opt_825_){
_start:
{
lean_object* v_name_826_; lean_object* v_defValue_827_; lean_object* v_map_828_; lean_object* v___x_829_; 
v_name_826_ = lean_ctor_get(v_opt_825_, 0);
v_defValue_827_ = lean_ctor_get(v_opt_825_, 1);
v_map_828_ = lean_ctor_get(v_opts_824_, 0);
v___x_829_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_828_, v_name_826_);
if (lean_obj_tag(v___x_829_) == 0)
{
uint8_t v___x_830_; 
v___x_830_ = lean_unbox(v_defValue_827_);
return v___x_830_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_829_, 1);
if (lean_obj_tag(v_val_831_) == 1)
{
uint8_t v_v_832_; 
v_v_832_ = lean_ctor_get_uint8(v_val_831_, 0);
lean_dec_ref_known(v_val_831_, 0);
return v_v_832_;
}
else
{
uint8_t v___x_833_; 
lean_dec(v_val_831_);
v___x_833_ = lean_unbox(v_defValue_827_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4___boxed(lean_object* v_opts_834_, lean_object* v_opt_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_opts_834_, v_opt_835_);
lean_dec_ref(v_opt_835_);
lean_dec_ref(v_opts_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1));
v___x_842_ = l_Lean_MessageData_ofFormat(v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(lean_object* v_msgData_843_, lean_object* v_macroStack_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_options_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_options_847_ = lean_ctor_get(v___y_845_, 1);
v___x_848_ = l_Lean_Elab_pp_macroStack;
v___x_849_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_options_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v_macroStack_844_);
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v_msgData_843_);
return v___x_850_;
}
else
{
if (lean_obj_tag(v_macroStack_844_) == 0)
{
lean_object* v___x_851_; 
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_msgData_843_);
return v___x_851_;
}
else
{
lean_object* v_head_852_; lean_object* v_after_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_868_; 
v_head_852_ = lean_ctor_get(v_macroStack_844_, 0);
lean_inc(v_head_852_);
v_after_853_ = lean_ctor_get(v_head_852_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_head_852_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v_head_852_, 0);
lean_dec(v_unused_869_);
v___x_855_ = v_head_852_;
v_isShared_856_ = v_isSharedCheck_868_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_after_853_);
lean_dec(v_head_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_868_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
if (v_isShared_856_ == 0)
{
lean_ctor_set_tag(v___x_855_, 7);
lean_ctor_set(v___x_855_, 1, v___x_857_);
lean_ctor_set(v___x_855_, 0, v_msgData_843_);
v___x_859_ = v___x_855_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_msgData_843_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_867_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_msgData_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_860_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2);
v___x_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = l_Lean_MessageData_ofSyntax(v_after_853_);
v___x_863_ = l_Lean_indentD(v___x_862_);
v_msgData_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_864_, 0, v___x_861_);
lean_ctor_set(v_msgData_864_, 1, v___x_863_);
v___x_865_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(v_msgData_864_, v_macroStack_844_);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_870_, lean_object* v_macroStack_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_870_, v_macroStack_871_, v___y_872_);
lean_dec_ref(v___y_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(lean_object* v_msg_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_ref_883_; lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v_macroStack_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_897_; 
v_ref_883_ = lean_ctor_get(v___y_880_, 4);
v___x_884_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msg_875_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v_macroStack_886_ = lean_ctor_get(v___y_876_, 1);
v___x_887_ = l_Lean_Elab_getBetterRef(v_ref_883_, v_macroStack_886_);
lean_inc(v_macroStack_886_);
v___x_888_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_a_885_, v_macroStack_886_, v___y_880_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_897_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_887_);
lean_ctor_set(v___x_893_, 1, v_a_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 1);
lean_ctor_set(v___x_891_, 0, v___x_893_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg___boxed(lean_object* v_msg_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_906_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(lean_object* v_x_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1));
lean_inc(v_x_946_);
v___x_955_ = l_Lean_Syntax_isOfKind(v_x_946_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec(v_x_946_);
v___x_956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
return v___x_956_;
}
else
{
lean_object* v_toCold_957_; lean_object* v_options_958_; lean_object* v_currRecDepth_959_; lean_object* v_maxRecDepth_960_; lean_object* v_ref_961_; lean_object* v_currNamespace_962_; lean_object* v_openDecls_963_; lean_object* v_initHeartbeats_964_; lean_object* v_maxHeartbeats_965_; lean_object* v_currMacroScope_966_; uint8_t v_diag_967_; uint8_t v_suppressElabErrors_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_ref_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_toCold_957_ = lean_ctor_get(v_a_951_, 0);
v_options_958_ = lean_ctor_get(v_a_951_, 1);
v_currRecDepth_959_ = lean_ctor_get(v_a_951_, 2);
v_maxRecDepth_960_ = lean_ctor_get(v_a_951_, 3);
v_ref_961_ = lean_ctor_get(v_a_951_, 4);
v_currNamespace_962_ = lean_ctor_get(v_a_951_, 5);
v_openDecls_963_ = lean_ctor_get(v_a_951_, 6);
v_initHeartbeats_964_ = lean_ctor_get(v_a_951_, 7);
v_maxHeartbeats_965_ = lean_ctor_get(v_a_951_, 8);
v_currMacroScope_966_ = lean_ctor_get(v_a_951_, 9);
v_diag_967_ = lean_ctor_get_uint8(v_a_951_, sizeof(void*)*10);
v_suppressElabErrors_968_ = lean_ctor_get_uint8(v_a_951_, sizeof(void*)*10 + 1);
v___x_969_ = lean_unsigned_to_nat(3u);
v___x_970_ = l_Lean_Syntax_getArg(v_x_946_, v___x_969_);
v___x_971_ = lean_box(0);
v_ref_972_ = l_Lean_replaceRef(v___x_970_, v_ref_961_);
lean_inc(v_currMacroScope_966_);
lean_inc(v_maxHeartbeats_965_);
lean_inc(v_initHeartbeats_964_);
lean_inc(v_openDecls_963_);
lean_inc(v_currNamespace_962_);
lean_inc(v_maxRecDepth_960_);
lean_inc(v_currRecDepth_959_);
lean_inc_ref(v_options_958_);
lean_inc_ref(v_toCold_957_);
v___x_973_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_973_, 0, v_toCold_957_);
lean_ctor_set(v___x_973_, 1, v_options_958_);
lean_ctor_set(v___x_973_, 2, v_currRecDepth_959_);
lean_ctor_set(v___x_973_, 3, v_maxRecDepth_960_);
lean_ctor_set(v___x_973_, 4, v_ref_972_);
lean_ctor_set(v___x_973_, 5, v_currNamespace_962_);
lean_ctor_set(v___x_973_, 6, v_openDecls_963_);
lean_ctor_set(v___x_973_, 7, v_initHeartbeats_964_);
lean_ctor_set(v___x_973_, 8, v_maxHeartbeats_965_);
lean_ctor_set(v___x_973_, 9, v_currMacroScope_966_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*10, v_diag_967_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*10 + 1, v_suppressElabErrors_968_);
v___x_974_ = l_Lean_Elab_Term_elabTerm(v___x_970_, v___x_971_, v___x_955_, v___x_955_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_976_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc_n(v_a_975_, 2);
lean_dec_ref_known(v___x_974_, 1);
lean_inc(v_a_952_);
lean_inc_ref(v___x_973_);
lean_inc(v_a_950_);
lean_inc_ref(v_a_949_);
v___x_976_ = lean_infer_type(v_a_975_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_n(v_a_977_, 2);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = l_Lean_Elab_Term_tryPostponeIfMVar(v_a_977_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v___x_979_; lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref_known(v___x_978_, 1);
v___x_979_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_a_977_, v_a_950_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_1113_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1113_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v_fst_989_; lean_object* v_fst_990_; lean_object* v_fst_991_; lean_object* v_fst_992_; lean_object* v_fst_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v___y_1039_; lean_object* v___x_1048_; 
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = l_Lean_Syntax_getArg(v_x_946_, v___x_984_);
v___x_986_ = lean_unsigned_to_nat(5u);
v___x_987_ = l_Lean_Syntax_getArg(v_x_946_, v___x_986_);
lean_dec(v_x_946_);
v___x_1048_ = l_Lean_Expr_consumeMData(v_a_980_);
if (lean_obj_tag(v___x_1048_) == 5)
{
lean_object* v_fn_1049_; lean_object* v_arg_1050_; lean_object* v___x_1051_; 
v_fn_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc_ref(v_fn_1049_);
v_arg_1050_ = lean_ctor_get(v___x_1048_, 1);
lean_inc_ref_n(v_arg_1050_, 2);
lean_dec_ref_known(v___x_1048_, 2);
v___x_1051_ = l_Lean_Meta_getLevel(v_arg_1050_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1053_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v___x_1053_ = l_Lean_Level_dec(v_a_1052_);
lean_dec(v_a_1052_);
if (lean_obj_tag(v___x_1053_) == 1)
{
lean_object* v_val_1054_; lean_object* v___x_1055_; 
v_val_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v___x_1053_, 1);
lean_inc(v_a_980_);
v___x_1055_ = l_Lean_Meta_getLevel(v_a_980_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1055_, 1);
v___x_1057_ = l_Lean_Level_dec(v_a_1056_);
lean_dec(v_a_1056_);
if (lean_obj_tag(v___x_1057_) == 1)
{
lean_object* v_val_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_a_980_);
v_val_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1080_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_val_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1080_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9));
v___x_1063_ = lean_box(0);
lean_inc(v_val_1054_);
v___x_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_val_1054_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_mkConst(v___x_1062_, v___x_1064_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1065_);
v___x_1067_ = v___x_1060_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = 0;
v___x_1069_ = lean_box(0);
v___x_1070_ = l_Lean_Meta_mkFreshExprMVar(v___x_1067_, v___x_1068_, v___x_1069_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc_n(v_a_1071_, 2);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11));
lean_inc(v_val_1058_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_val_1058_);
lean_ctor_set(v___x_1073_, 1, v___x_1063_);
lean_inc(v_val_1054_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_val_1054_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_mkConst(v___x_1072_, v___x_1074_);
lean_inc_ref(v_fn_1049_);
v___x_1076_ = l_Lean_mkAppB(v___x_1075_, v_fn_1049_, v_a_1071_);
v___x_1077_ = l_Lean_Meta_synthInstance(v___x_1076_, v___x_971_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
lean_dec_ref_known(v___x_973_, 10);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v_fst_989_ = v_val_1054_;
v_fst_990_ = v_val_1058_;
v_fst_991_ = v_fn_1049_;
v_fst_992_ = v_arg_1050_;
v_fst_993_ = v_a_1071_;
v_fst_994_ = v_a_1078_;
v_snd_995_ = v_a_975_;
goto v___jp_988_;
}
else
{
lean_dec(v_a_1071_);
lean_dec(v_val_1058_);
lean_dec(v_val_1054_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_fn_1049_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
lean_del_object(v___x_982_);
lean_dec(v_a_975_);
return v___x_1077_;
}
}
else
{
lean_dec(v_val_1058_);
lean_dec(v_val_1054_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_fn_1049_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
lean_del_object(v___x_982_);
lean_dec(v_a_975_);
lean_dec_ref_known(v___x_973_, 10);
return v___x_1070_;
}
}
}
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v___x_1057_);
lean_dec(v_val_1054_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_fn_1049_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
lean_del_object(v___x_982_);
lean_dec(v_a_975_);
v___x_1081_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
v___x_1082_ = l_Lean_MessageData_ofExpr(v_a_980_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_1083_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
lean_dec_ref_known(v___x_973_, 10);
v___y_1039_ = v___x_1084_;
goto v___jp_1038_;
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_val_1054_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_fn_1049_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
lean_del_object(v___x_982_);
lean_dec(v_a_980_);
lean_dec(v_a_975_);
lean_dec_ref_known(v___x_973_, 10);
v_a_1085_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1055_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1055_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v___x_1053_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_fn_1049_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
lean_del_object(v___x_982_);
lean_dec(v_a_975_);
v___x_1093_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
v___x_1094_ = l_Lean_MessageData_ofExpr(v_a_980_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_1095_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
lean_dec_ref_known(v___x_973_, 10);
v___y_1039_ = v___x_1096_;
goto v___jp_1038_;
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_fn_1049_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
lean_del_object(v___x_982_);
lean_dec(v_a_980_);
lean_dec(v_a_975_);
lean_dec_ref_known(v___x_973_, 10);
v_a_1097_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1051_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1051_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref(v___x_1048_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
lean_del_object(v___x_982_);
v___x_1105_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15);
v___x_1106_ = l_Lean_MessageData_ofExpr(v_a_975_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17, &l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_MessageData_ofExpr(v_a_980_);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_1111_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v___x_973_, v_a_952_);
lean_dec_ref_known(v___x_973_, 10);
v___y_1039_ = v___x_1112_;
goto v___jp_1038_;
}
v___jp_988_:
{
uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_996_ = 0;
v___x_997_ = l_Lean_SourceInfo_fromRef(v_ref_961_, v___x_996_);
v___x_998_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3));
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2));
lean_inc_n(v___x_997_, 2);
v___x_1000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_997_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_997_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_Syntax_node3(v___x_997_, v___x_998_, v___x_1000_, v___x_985_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4));
v___x_1005_ = lean_box(0);
lean_inc(v_fst_989_);
v___x_1006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_fst_989_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
lean_inc_ref(v___x_1006_);
v___x_1007_ = l_Lean_mkConst(v___x_1004_, v___x_1006_);
lean_inc_ref(v_fst_993_);
v___x_1008_ = l_Lean_Expr_app___override(v___x_1007_, v_fst_993_);
if (v_isShared_983_ == 0)
{
lean_ctor_set_tag(v___x_982_, 1);
lean_ctor_set(v___x_982_, 0, v___x_1008_);
v___x_1010_ = v___x_982_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Elab_Term_elabTerm(v___x_1003_, v___x_1010_, v___x_955_, v___x_955_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1036_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1036_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1036_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5));
v___x_1017_ = l_Lean_mkConst(v___x_1016_, v___x_1006_);
lean_inc_ref(v_fst_993_);
lean_inc_ref(v_fst_992_);
v___x_1018_ = l_Lean_mkAppB(v___x_1017_, v_fst_992_, v_fst_993_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 1);
lean_ctor_set(v___x_1014_, 0, v___x_1018_);
v___x_1020_ = v___x_1014_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_Elab_Term_elabTerm(v___x_987_, v___x_1020_, v___x_955_, v___x_955_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1034_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1034_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1034_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7));
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_fst_990_);
lean_ctor_set(v___x_1027_, 1, v___x_1005_);
v___x_1028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_fst_989_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_mkConst(v___x_1026_, v___x_1028_);
v___x_1030_ = l_Lean_mkApp7(v___x_1029_, v_fst_991_, v_fst_993_, v_fst_994_, v_fst_992_, v_snd_995_, v_a_1012_, v_a_1022_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1030_);
v___x_1032_ = v___x_1024_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
else
{
lean_dec(v_a_1012_);
lean_dec_ref(v_snd_995_);
lean_dec_ref(v_fst_994_);
lean_dec_ref(v_fst_993_);
lean_dec_ref(v_fst_992_);
lean_dec_ref(v_fst_991_);
lean_dec(v_fst_990_);
lean_dec(v_fst_989_);
return v___x_1021_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1006_, 2);
lean_dec_ref(v_snd_995_);
lean_dec_ref(v_fst_994_);
lean_dec_ref(v_fst_993_);
lean_dec_ref(v_fst_992_);
lean_dec_ref(v_fst_991_);
lean_dec(v_fst_990_);
lean_dec(v_fst_989_);
lean_dec(v___x_987_);
return v___x_1011_;
}
}
}
v___jp_1038_:
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
v_a_1040_ = lean_ctor_get(v___y_1039_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___y_1039_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___y_1039_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___y_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v_a_977_);
lean_dec(v_a_975_);
lean_dec_ref_known(v___x_973_, 10);
lean_dec(v_x_946_);
v_a_1114_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_978_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_978_);
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
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
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
lean_dec(v_a_975_);
lean_dec_ref_known(v___x_973_, 10);
lean_dec(v_x_946_);
return v___x_976_;
}
}
else
{
lean_dec_ref_known(v___x_973_, 10);
lean_dec(v_x_946_);
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___boxed(lean_object* v_x_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(v_x_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(v_x_1131_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed(lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(v_x_1141_, v_x_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_x_1142_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(lean_object* v_00_u03b1_1151_, lean_object* v_msg_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_msg_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(v_00_u03b1_1161_, v_msg_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(lean_object* v_msgData_1171_, lean_object* v_macroStack_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_1171_, v_macroStack_1172_, v___y_1177_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___boxed(lean_object* v_msgData_1181_, lean_object* v_macroStack_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(v_msgData_1181_, v_macroStack_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1(){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1196_ = l_Lean_Elab_Term_termElabAttribute;
v___x_1197_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1));
v___x_1198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1));
v___x_1199_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed), 9, 0);
v___x_1200_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1196_, v___x_1197_, v___x_1198_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___boxed(lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
return v_res_1202_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinNotation(uint8_t builtin);
lean_object* runtime_initialize_Std_Do_Triple_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
