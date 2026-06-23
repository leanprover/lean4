// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Forward
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.Do.Control import Lean.Elab.Do.InferControlInfo import Lean.Elab.Binders
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f(lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabFunBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoForward___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 133, .m_data = "`do←` may only appear as the last argument of a function application inside an enclosing `do` block, optionally inside a `fun` binder"};
static const lean_object* l_Lean_Elab_Do_elabDoForward___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoForward___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoForward___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoForward___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForward"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(207, 164, 175, 48, 233, 61, 15, 76)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabDoForward"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(86, 191, 102, 116, 164, 35, 128, 94)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 32, .m_data = "` is not a valid `do←` wrapper: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 148, .m_data = ". The wrapper must have type `(… → m α) → m α` for some `α` that is universally quantified in the wrapper's signature and does not appear elsewhere."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 48, .m_data = "`α` appears in the forwarded body's input type `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 62, .m_data = "the forwarded body's `α` differs from the wrapper's return `α`"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 53, .m_data = "`α` appears in an applied explicit argument of type `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 43, .m_data = "its return type pins `α` to a concrete type"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "its return type `"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 26, .m_data = "` is not of the form `m α`"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "forwarded"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(125, 152, 115, 51, 73, 98, 174, 67)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the lifted body's type does not match the wrapper's body slot type"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_box(1);
v___x_16_ = l_Lean_MessageData_ofFormat(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2));
v___x_21_ = l_Lean_MessageData_ofFormat(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
return v_x_22_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_47_; 
v_head_24_ = lean_ctor_get(v_x_23_, 0);
v_tail_25_ = lean_ctor_get(v_x_23_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_47_ == 0)
{
v___x_27_ = v_x_23_;
v_isShared_28_ = v_isSharedCheck_47_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_tail_25_);
lean_inc(v_head_24_);
lean_dec(v_x_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_47_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_before_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_45_; 
v_before_29_ = lean_ctor_get(v_head_24_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_head_24_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v_head_24_, 1);
lean_dec(v_unused_46_);
v___x_31_ = v_head_24_;
v_isShared_32_ = v_isSharedCheck_45_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_before_29_);
lean_dec(v_head_24_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_45_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 7);
lean_ctor_set(v___x_31_, 1, v___x_33_);
lean_ctor_set(v___x_31_, 0, v_x_22_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_x_22_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_44_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 7);
lean_ctor_set(v___x_27_, 1, v___x_36_);
lean_ctor_set(v___x_27_, 0, v___x_35_);
v___x_38_ = v___x_27_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_36_);
v___x_38_ = v_reuseFailAlloc_43_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = l_Lean_MessageData_ofSyntax(v_before_29_);
v___x_40_ = l_Lean_indentD(v___x_39_);
v___x_41_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_38_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v_x_22_ = v___x_41_;
v_x_23_ = v_tail_25_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1));
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(lean_object* v_msgData_53_, lean_object* v_macroStack_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_options_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v_options_57_ = lean_ctor_get(v___y_55_, 2);
v___x_58_ = l_Lean_Elab_pp_macroStack;
v___x_59_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(v_options_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec(v_macroStack_54_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_msgData_53_);
return v___x_60_;
}
else
{
if (lean_obj_tag(v_macroStack_54_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_msgData_53_);
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_after_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_head_62_ = lean_ctor_get(v_macroStack_54_, 0);
lean_inc(v_head_62_);
v_after_63_ = lean_ctor_get(v_head_62_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_head_62_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v_head_62_, 0);
lean_dec(v_unused_79_);
v___x_65_ = v_head_62_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_after_63_);
lean_dec(v_head_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 7);
lean_ctor_set(v___x_65_, 1, v___x_67_);
lean_ctor_set(v___x_65_, 0, v_msgData_53_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_msgData_53_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_77_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_msgData_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2);
v___x_71_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = l_Lean_MessageData_ofSyntax(v_after_63_);
v___x_73_ = l_Lean_indentD(v___x_72_);
v_msgData_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_74_, 0, v___x_71_);
lean_ctor_set(v_msgData_74_, 1, v___x_73_);
v___x_75_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(v_msgData_74_, v_macroStack_54_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_80_, lean_object* v_macroStack_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_80_, v_macroStack_81_, v___y_82_);
lean_dec_ref(v___y_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_env_92_; lean_object* v___x_93_; lean_object* v_mctx_94_; lean_object* v_lctx_95_; lean_object* v_options_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = lean_st_ref_get(v___y_87_);
v_mctx_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_mctx_94_);
lean_dec(v___x_93_);
v_lctx_95_ = lean_ctor_get(v___y_86_, 2);
v_options_96_ = lean_ctor_get(v___y_88_, 2);
lean_inc_ref(v_options_96_);
lean_inc_ref(v_lctx_95_);
v___x_97_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_97_, 0, v_env_92_);
lean_ctor_set(v___x_97_, 1, v_mctx_94_);
lean_ctor_set(v___x_97_, 2, v_lctx_95_);
lean_ctor_set(v___x_97_, 3, v_options_96_);
v___x_98_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v_msgData_85_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0___boxed(lean_object* v_msgData_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msgData_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v_a_117_; lean_object* v_macroStack_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_115_ = lean_ctor_get(v___y_112_, 5);
v___x_116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_107_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v___x_116_);
v_macroStack_118_ = lean_ctor_get(v___y_108_, 1);
v___x_119_ = l_Lean_Elab_getBetterRef(v_ref_115_, v_macroStack_118_);
lean_inc(v_macroStack_118_);
v___x_120_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_a_117_, v_macroStack_118_, v___y_112_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg___boxed(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_138_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Elab_Do_elabDoForward___redArg___closed__0));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg(lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_obj_once(&l_Lean_Elab_Do_elabDoForward___redArg___closed__1, &l_Lean_Elab_Do_elabDoForward___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1);
v___x_150_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_149_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg___boxed(lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward(lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___boxed(lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Elab_Do_elabDoForward(v_x_169_, v_x_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_x_170_);
lean_dec(v_x_169_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(lean_object* v_00_u03b1_179_, lean_object* v_msg_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___boxed(lean_object* v_00_u03b1_189_, lean_object* v_msg_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(v_00_u03b1_189_, v_msg_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(lean_object* v_msgData_199_, lean_object* v_macroStack_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_199_, v_macroStack_200_, v___y_205_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___boxed(lean_object* v_msgData_209_, lean_object* v_macroStack_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(v_msgData_209_, v_macroStack_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1(){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_237_ = l_Lean_Elab_Term_termElabAttribute;
v___x_238_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4));
v___x_239_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8));
v___x_240_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoForward___boxed), 9, 0);
v___x_241_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_237_, v___x_238_, v___x_239_, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___boxed(lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
return v_res_243_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4));
v___x_252_ = l_Lean_stringToMessageData(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(lean_object* v_headApp_253_, lean_object* v_reason_254_){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_255_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_256_ = l_Lean_MessageData_ofSyntax(v_headApp_253_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_reason_254_);
v___x_261_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(lean_object* v_e_263_, lean_object* v___y_264_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = l_Lean_Expr_hasMVar(v_e_263_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_e_263_);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v_mctx_269_; lean_object* v___x_270_; lean_object* v_fst_271_; lean_object* v_snd_272_; lean_object* v___x_273_; lean_object* v_cache_274_; lean_object* v_zetaDeltaFVarIds_275_; lean_object* v_postponed_276_; lean_object* v_diag_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_286_; 
v___x_268_ = lean_st_ref_get(v___y_264_);
v_mctx_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_ref(v_mctx_269_);
lean_dec(v___x_268_);
v___x_270_ = l_Lean_instantiateMVarsCore(v_mctx_269_, v_e_263_);
v_fst_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_fst_271_);
v_snd_272_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_snd_272_);
lean_dec_ref(v___x_270_);
v___x_273_ = lean_st_ref_take(v___y_264_);
v_cache_274_ = lean_ctor_get(v___x_273_, 1);
v_zetaDeltaFVarIds_275_ = lean_ctor_get(v___x_273_, 2);
v_postponed_276_ = lean_ctor_get(v___x_273_, 3);
v_diag_277_ = lean_ctor_get(v___x_273_, 4);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v___x_273_, 0);
lean_dec(v_unused_287_);
v___x_279_ = v___x_273_;
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_diag_277_);
lean_inc(v_postponed_276_);
lean_inc(v_zetaDeltaFVarIds_275_);
lean_inc(v_cache_274_);
lean_dec(v___x_273_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v_snd_272_);
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_snd_272_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_cache_274_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_zetaDeltaFVarIds_275_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_postponed_276_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_diag_277_);
v___x_282_ = v_reuseFailAlloc_285_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_st_ref_set(v___y_264_, v___x_282_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_fst_271_);
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg___boxed(lean_object* v_e_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_288_, v___y_289_);
lean_dec(v___y_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(lean_object* v_e_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_292_, v___y_294_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___boxed(lean_object* v_e_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(v_e_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(lean_object* v_k_306_, lean_object* v_b_307_, lean_object* v_c_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; 
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
v___x_314_ = lean_apply_7(v_k_306_, v_b_307_, v_c_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, lean_box(0));
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed(lean_object* v_k_315_, lean_object* v_b_316_, lean_object* v_c_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(v_k_315_, v_b_316_, v_c_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(lean_object* v_type_324_, lean_object* v_k_325_, uint8_t v_cleanupAnnotations_326_, uint8_t v_whnfType_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___f_333_; lean_object* v___x_334_; 
v___f_333_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_333_, 0, v_k_325_);
v___x_334_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_324_, v___f_333_, v_cleanupAnnotations_326_, v_whnfType_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_343_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_334_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_334_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___boxed(lean_object* v_type_351_, lean_object* v_k_352_, lean_object* v_cleanupAnnotations_353_, lean_object* v_whnfType_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_360_; uint8_t v_whnfType_boxed_361_; lean_object* v_res_362_; 
v_cleanupAnnotations_boxed_360_ = lean_unbox(v_cleanupAnnotations_353_);
v_whnfType_boxed_361_ = lean_unbox(v_whnfType_354_);
v_res_362_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_351_, v_k_352_, v_cleanupAnnotations_boxed_360_, v_whnfType_boxed_361_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(lean_object* v_00_u03b1_363_, lean_object* v_type_364_, lean_object* v_k_365_, uint8_t v_cleanupAnnotations_366_, uint8_t v_whnfType_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_364_, v_k_365_, v_cleanupAnnotations_366_, v_whnfType_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___boxed(lean_object* v_00_u03b1_374_, lean_object* v_type_375_, lean_object* v_k_376_, lean_object* v_cleanupAnnotations_377_, lean_object* v_whnfType_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_384_; uint8_t v_whnfType_boxed_385_; lean_object* v_res_386_; 
v_cleanupAnnotations_boxed_384_ = lean_unbox(v_cleanupAnnotations_377_);
v_whnfType_boxed_385_ = lean_unbox(v_whnfType_378_);
v_res_386_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(v_00_u03b1_374_, v_type_375_, v_k_376_, v_cleanupAnnotations_boxed_384_, v_whnfType_boxed_385_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_ref_393_; lean_object* v___x_394_; lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_ref_393_ = lean_ctor_get(v___y_390_, 5);
v___x_394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_inc(v_ref_393_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_ref_393_);
lean_ctor_set(v___x_399_, 1, v_a_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 1);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg___boxed(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(lean_object* v_headApp_411_, lean_object* v_00_u03b1_412_, lean_object* v_reason_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_411_, v_reason_413_);
v___x_420_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_419_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed(lean_object* v_headApp_421_, lean_object* v_00_u03b1_422_, lean_object* v_reason_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_421_, v_00_u03b1_422_, v_reason_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_429_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(lean_object* v_arg_430_, lean_object* v_x_431_){
_start:
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = l_Lean_Expr_mvarId_x21(v_arg_430_);
v___x_433_ = l_Lean_instBEqMVarId_beq(v_x_431_, v___x_432_);
lean_dec(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed(lean_object* v_arg_434_, lean_object* v_x_435_){
_start:
{
uint8_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(v_arg_434_, v_x_435_);
lean_dec(v_x_435_);
lean_dec_ref(v_arg_434_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0));
v___x_440_ = l_Lean_stringToMessageData(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(lean_object* v_arg_441_, lean_object* v_headApp_442_, lean_object* v_as_443_, size_t v_sz_444_, size_t v_i_445_, lean_object* v_b_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_a_453_; uint8_t v___x_457_; 
v___x_457_ = lean_usize_dec_lt(v_i_445_, v_sz_444_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec(v_headApp_442_);
lean_dec_ref(v_arg_441_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_b_446_);
return v___x_458_;
}
else
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_array_uget_borrowed(v_as_443_, v_i_445_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
lean_inc(v___y_448_);
lean_inc_ref(v___y_447_);
lean_inc(v_a_459_);
v___x_460_ = lean_infer_type(v_a_459_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc_n(v_a_461_, 2);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_461_, v___y_448_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
lean_inc_ref(v_arg_441_);
v___f_464_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_464_, 0, v_arg_441_);
v___x_465_ = lean_box(0);
v___x_466_ = lean_box(0);
v___x_467_ = l_Lean_FindMVar_main(v___f_464_, v_a_463_, v___x_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_dec(v_a_461_);
v_a_453_ = v___x_465_;
goto v___jp_452_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec_ref_known(v___x_467_, 1);
v___x_468_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_469_ = l_Lean_MessageData_ofExpr(v_a_461_);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_468_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
lean_inc(v_headApp_442_);
v___x_473_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_442_, v___x_472_);
v___x_474_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_473_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_dec_ref_known(v___x_474_, 1);
v_a_453_ = v___x_465_;
goto v___jp_452_;
}
else
{
lean_dec(v_headApp_442_);
lean_dec_ref(v_arg_441_);
return v___x_474_;
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_a_461_);
lean_dec(v_headApp_442_);
lean_dec_ref(v_arg_441_);
v_a_475_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_462_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_462_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_headApp_442_);
lean_dec_ref(v_arg_441_);
v_a_483_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_460_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_460_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
v___jp_452_:
{
size_t v___x_454_; size_t v___x_455_; 
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_445_, v___x_454_);
v_i_445_ = v___x_455_;
v_b_446_ = v_a_453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___boxed(lean_object* v_arg_491_, lean_object* v_headApp_492_, lean_object* v_as_493_, lean_object* v_sz_494_, lean_object* v_i_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
size_t v_sz_boxed_502_; size_t v_i_boxed_503_; lean_object* v_res_504_; 
v_sz_boxed_502_ = lean_unbox_usize(v_sz_494_);
lean_dec(v_sz_494_);
v_i_boxed_503_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_491_, v_headApp_492_, v_as_493_, v_sz_boxed_502_, v_i_boxed_503_, v_b_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec_ref(v_as_493_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(lean_object* v_arg_505_, lean_object* v_headApp_506_, lean_object* v_as_507_, size_t v_sz_508_, size_t v_i_509_, lean_object* v_b_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_a_517_; uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_lt(v_i_509_, v_sz_508_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec(v_headApp_506_);
lean_dec_ref(v_arg_505_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v_b_510_);
return v___x_522_;
}
else
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_array_uget_borrowed(v_as_507_, v_i_509_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v_a_523_);
v___x_524_ = lean_infer_type(v_a_523_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc_n(v_a_525_, 2);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_525_, v___y_512_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___f_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
lean_inc_ref(v_arg_505_);
v___f_528_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_528_, 0, v_arg_505_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_box(0);
v___x_531_ = l_Lean_FindMVar_main(v___f_528_, v_a_527_, v___x_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_dec(v_a_525_);
v_a_517_ = v___x_529_;
goto v___jp_516_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec_ref_known(v___x_531_, 1);
v___x_532_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_533_ = l_Lean_MessageData_ofExpr(v_a_525_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
lean_inc(v_headApp_506_);
v___x_537_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_506_, v___x_536_);
v___x_538_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_537_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_dec_ref_known(v___x_538_, 1);
v_a_517_ = v___x_529_;
goto v___jp_516_;
}
else
{
lean_dec(v_headApp_506_);
lean_dec_ref(v_arg_505_);
return v___x_538_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_525_);
lean_dec(v_headApp_506_);
lean_dec_ref(v_arg_505_);
v_a_539_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_526_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_526_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_dec(v_headApp_506_);
lean_dec_ref(v_arg_505_);
v_a_547_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_524_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_524_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
v___jp_516_:
{
size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_518_ = ((size_t)1ULL);
v___x_519_ = lean_usize_add(v_i_509_, v___x_518_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_505_, v_headApp_506_, v_as_507_, v_sz_508_, v___x_519_, v_a_517_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3___boxed(lean_object* v_arg_555_, lean_object* v_headApp_556_, lean_object* v_as_557_, lean_object* v_sz_558_, lean_object* v_i_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
size_t v_sz_boxed_566_; size_t v_i_boxed_567_; lean_object* v_res_568_; 
v_sz_boxed_566_ = lean_unbox_usize(v_sz_558_);
lean_dec(v_sz_558_);
v_i_boxed_567_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_res_568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_555_, v_headApp_556_, v_as_557_, v_sz_boxed_566_, v_i_boxed_567_, v_b_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v_as_557_);
return v_res_568_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(lean_object* v_a_572_, lean_object* v_arg_573_, lean_object* v_headApp_574_, lean_object* v_reject_575_, lean_object* v_args_576_, lean_object* v_body_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___x_600_; lean_object* v_a_601_; lean_object* v___x_602_; 
v___x_600_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_body_577_, v___y_579_);
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref(v___x_600_);
v___x_602_ = l_Lean_Meta_whnfD(v_a_601_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = l_Lean_Meta_isExprDefEq(v_a_572_, v_a_603_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; uint8_t v___x_606_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_606_ = lean_unbox(v_a_605_);
lean_dec(v_a_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
lean_inc(v___y_579_);
lean_inc_ref(v___y_578_);
v___x_608_ = lean_apply_7(v_reject_575_, lean_box(0), v___x_607_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, lean_box(0));
if (lean_obj_tag(v___x_608_) == 0)
{
lean_dec_ref_known(v___x_608_, 1);
v___y_584_ = v___y_578_;
v___y_585_ = v___y_579_;
v___y_586_ = v___y_580_;
v___y_587_ = v___y_581_;
goto v___jp_583_;
}
else
{
lean_dec(v_headApp_574_);
lean_dec_ref(v_arg_573_);
return v___x_608_;
}
}
else
{
lean_dec_ref(v_reject_575_);
v___y_584_ = v___y_578_;
v___y_585_ = v___y_579_;
v___y_586_ = v___y_580_;
v___y_587_ = v___y_581_;
goto v___jp_583_;
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_reject_575_);
lean_dec(v_headApp_574_);
lean_dec_ref(v_arg_573_);
v_a_609_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_604_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_604_);
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
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v_reject_575_);
lean_dec(v_headApp_574_);
lean_dec_ref(v_arg_573_);
lean_dec_ref(v_a_572_);
v_a_617_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_602_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_602_);
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
v___jp_583_:
{
lean_object* v___x_588_; size_t v_sz_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_588_ = lean_box(0);
v_sz_589_ = lean_array_size(v_args_576_);
v___x_590_ = ((size_t)0ULL);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_573_, v_headApp_574_, v_args_576_, v_sz_589_, v___x_590_, v___x_588_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_591_, 0);
lean_dec(v_unused_599_);
v___x_593_ = v___x_591_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_dec(v___x_591_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_588_);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_588_);
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
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed(lean_object* v_a_625_, lean_object* v_arg_626_, lean_object* v_headApp_627_, lean_object* v_reject_628_, lean_object* v_args_629_, lean_object* v_body_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(v_a_625_, v_arg_626_, v_headApp_627_, v_reject_628_, v_args_629_, v_body_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v_args_629_);
return v_res_636_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0));
v___x_639_ = l_Lean_stringToMessageData(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(lean_object* v_forwarded_640_, lean_object* v_arg_641_, lean_object* v_headApp_642_, lean_object* v_as_643_, size_t v_sz_644_, size_t v_i_645_, lean_object* v_b_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_a_653_; uint8_t v___x_657_; 
v___x_657_ = lean_usize_dec_lt(v_i_645_, v_sz_644_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v_headApp_642_);
lean_dec_ref(v_arg_641_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v_b_646_);
return v___x_658_;
}
else
{
lean_object* v_a_659_; lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_721_; 
v_a_659_ = lean_array_uget(v_as_643_, v_i_645_);
v_fst_660_ = lean_ctor_get(v_a_659_, 0);
v_snd_661_ = lean_ctor_get(v_a_659_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_721_ == 0)
{
v___x_663_ = v_a_659_;
v_isShared_664_ = v_isSharedCheck_721_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snd_661_);
lean_inc(v_fst_660_);
lean_dec(v_a_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_721_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = l_Lean_Expr_fvarId_x21(v_fst_660_);
lean_dec(v_fst_660_);
v___x_666_ = l_Lean_FVarId_getDecl___redArg(v___x_665_, v___y_647_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = lean_box(0);
v___x_669_ = l_Lean_LocalDecl_binderInfo(v_a_667_);
lean_dec(v_a_667_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_661_, v___y_648_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_expr_eqv(v_a_671_, v_forwarded_640_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_inc(v___y_650_);
lean_inc_ref(v___y_649_);
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
v___x_673_ = lean_infer_type(v_a_671_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_n(v_a_674_, 2);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_674_, v___y_648_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
lean_inc_ref(v_arg_641_);
v___f_677_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_677_, 0, v_arg_641_);
v___x_678_ = lean_box(0);
v___x_679_ = l_Lean_FindMVar_main(v___f_677_, v_a_676_, v___x_678_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_dec(v_a_674_);
lean_del_object(v___x_663_);
v_a_653_ = v___x_668_;
goto v___jp_652_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
lean_dec_ref_known(v___x_679_, 1);
v___x_680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_681_ = l_Lean_MessageData_ofExpr(v_a_674_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 7);
lean_ctor_set(v___x_663_, 1, v___x_681_);
lean_ctor_set(v___x_663_, 0, v___x_680_);
v___x_683_ = v___x_663_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_681_);
v___x_683_ = v_reuseFailAlloc_688_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_684_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_683_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
lean_inc(v_headApp_642_);
v___x_686_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_642_, v___x_685_);
v___x_687_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_686_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_dec_ref_known(v___x_687_, 1);
v_a_653_ = v___x_668_;
goto v___jp_652_;
}
else
{
lean_dec(v_headApp_642_);
lean_dec_ref(v_arg_641_);
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_a_674_);
lean_del_object(v___x_663_);
lean_dec(v_headApp_642_);
lean_dec_ref(v_arg_641_);
v_a_689_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_675_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_675_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_del_object(v___x_663_);
lean_dec(v_headApp_642_);
lean_dec_ref(v_arg_641_);
v_a_697_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_673_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_673_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_dec(v_a_671_);
lean_del_object(v___x_663_);
v_a_653_ = v___x_668_;
goto v___jp_652_;
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_del_object(v___x_663_);
lean_dec(v_headApp_642_);
lean_dec_ref(v_arg_641_);
v_a_705_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_670_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_670_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
v_a_653_ = v___x_668_;
goto v___jp_652_;
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_del_object(v___x_663_);
lean_dec(v_snd_661_);
lean_dec(v_headApp_642_);
lean_dec_ref(v_arg_641_);
v_a_713_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_666_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_666_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
v___jp_652_:
{
size_t v___x_654_; size_t v___x_655_; 
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_add(v_i_645_, v___x_654_);
v_i_645_ = v___x_655_;
v_b_646_ = v_a_653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___boxed(lean_object* v_forwarded_722_, lean_object* v_arg_723_, lean_object* v_headApp_724_, lean_object* v_as_725_, lean_object* v_sz_726_, lean_object* v_i_727_, lean_object* v_b_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_sz_boxed_734_ = lean_unbox_usize(v_sz_726_);
lean_dec(v_sz_726_);
v_i_boxed_735_ = lean_unbox_usize(v_i_727_);
lean_dec(v_i_727_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_722_, v_arg_723_, v_headApp_724_, v_as_725_, v_sz_boxed_734_, v_i_boxed_735_, v_b_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec_ref(v_as_725_);
lean_dec_ref(v_forwarded_722_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(lean_object* v_forwarded_737_, lean_object* v_arg_738_, lean_object* v_headApp_739_, lean_object* v_as_740_, size_t v_sz_741_, size_t v_i_742_, lean_object* v_b_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_a_750_; uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_lt(v_i_742_, v_sz_741_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec(v_headApp_739_);
lean_dec_ref(v_arg_738_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v_b_743_);
return v___x_755_;
}
else
{
lean_object* v_a_756_; lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_818_; 
v_a_756_ = lean_array_uget(v_as_740_, v_i_742_);
v_fst_757_ = lean_ctor_get(v_a_756_, 0);
v_snd_758_ = lean_ctor_get(v_a_756_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_a_756_);
if (v_isSharedCheck_818_ == 0)
{
v___x_760_ = v_a_756_;
v_isShared_761_ = v_isSharedCheck_818_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_snd_758_);
lean_inc(v_fst_757_);
lean_dec(v_a_756_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_818_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = l_Lean_Expr_fvarId_x21(v_fst_757_);
lean_dec(v_fst_757_);
v___x_763_ = l_Lean_FVarId_getDecl___redArg(v___x_762_, v___y_744_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = lean_box(0);
v___x_766_ = l_Lean_LocalDecl_binderInfo(v_a_764_);
lean_dec(v_a_764_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_758_, v___y_745_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; uint8_t v___x_769_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = lean_expr_eqv(v_a_768_, v_forwarded_737_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_inc(v___y_747_);
lean_inc_ref(v___y_746_);
lean_inc(v___y_745_);
lean_inc_ref(v___y_744_);
v___x_770_ = lean_infer_type(v_a_768_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_n(v_a_771_, 2);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_771_, v___y_745_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
lean_inc_ref(v_arg_738_);
v___f_774_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_774_, 0, v_arg_738_);
v___x_775_ = lean_box(0);
v___x_776_ = l_Lean_FindMVar_main(v___f_774_, v_a_773_, v___x_775_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_dec(v_a_771_);
lean_del_object(v___x_760_);
v_a_750_ = v___x_765_;
goto v___jp_749_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
lean_dec_ref_known(v___x_776_, 1);
v___x_777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_778_ = l_Lean_MessageData_ofExpr(v_a_771_);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 7);
lean_ctor_set(v___x_760_, 1, v___x_778_);
lean_ctor_set(v___x_760_, 0, v___x_777_);
v___x_780_ = v___x_760_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___x_778_);
v___x_780_ = v_reuseFailAlloc_785_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_781_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
lean_inc(v_headApp_739_);
v___x_783_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_739_, v___x_782_);
v___x_784_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_783_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_dec_ref_known(v___x_784_, 1);
v_a_750_ = v___x_765_;
goto v___jp_749_;
}
else
{
lean_dec(v_headApp_739_);
lean_dec_ref(v_arg_738_);
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_a_771_);
lean_del_object(v___x_760_);
lean_dec(v_headApp_739_);
lean_dec_ref(v_arg_738_);
v_a_786_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_772_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_772_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_del_object(v___x_760_);
lean_dec(v_headApp_739_);
lean_dec_ref(v_arg_738_);
v_a_794_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_770_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_770_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_dec(v_a_768_);
lean_del_object(v___x_760_);
v_a_750_ = v___x_765_;
goto v___jp_749_;
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_del_object(v___x_760_);
lean_dec(v_headApp_739_);
lean_dec_ref(v_arg_738_);
v_a_802_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_767_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_767_);
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
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
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
lean_del_object(v___x_760_);
lean_dec(v_snd_758_);
v_a_750_ = v___x_765_;
goto v___jp_749_;
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_del_object(v___x_760_);
lean_dec(v_snd_758_);
lean_dec(v_headApp_739_);
lean_dec_ref(v_arg_738_);
v_a_810_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_763_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_763_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
v___jp_749_:
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)1ULL);
v___x_752_ = lean_usize_add(v_i_742_, v___x_751_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_737_, v_arg_738_, v_headApp_739_, v_as_740_, v_sz_741_, v___x_752_, v_a_750_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___boxed(lean_object* v_forwarded_819_, lean_object* v_arg_820_, lean_object* v_headApp_821_, lean_object* v_as_822_, lean_object* v_sz_823_, lean_object* v_i_824_, lean_object* v_b_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
size_t v_sz_boxed_831_; size_t v_i_boxed_832_; lean_object* v_res_833_; 
v_sz_boxed_831_ = lean_unbox_usize(v_sz_823_);
lean_dec(v_sz_823_);
v_i_boxed_832_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_res_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_819_, v_arg_820_, v_headApp_821_, v_as_822_, v_sz_boxed_831_, v_i_boxed_832_, v_b_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec_ref(v_as_822_);
lean_dec_ref(v_forwarded_819_);
return v_res_833_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0(void){
_start:
{
lean_object* v___x_834_; lean_object* v_dummy_835_; 
v___x_834_ = lean_box(0);
v_dummy_835_ = l_Lean_Expr_sort___override(v___x_834_);
return v_dummy_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(lean_object* v_probeExpr_836_, lean_object* v_forwarded_837_, lean_object* v_arg_838_, lean_object* v_headApp_839_, lean_object* v_fvars_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_dummy_847_; lean_object* v_nargs_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; size_t v_sz_855_; size_t v___x_856_; lean_object* v___x_857_; 
v_dummy_847_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0);
v_nargs_848_ = l_Lean_Expr_getAppNumArgs(v_probeExpr_836_);
lean_inc(v_nargs_848_);
v___x_849_ = lean_mk_array(v_nargs_848_, v_dummy_847_);
v___x_850_ = lean_unsigned_to_nat(1u);
v___x_851_ = lean_nat_sub(v_nargs_848_, v___x_850_);
lean_dec(v_nargs_848_);
v___x_852_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_probeExpr_836_, v___x_849_, v___x_851_);
v___x_853_ = l_Array_zip___redArg(v_fvars_840_, v___x_852_);
lean_dec_ref(v___x_852_);
v___x_854_ = lean_box(0);
v_sz_855_ = lean_array_size(v___x_853_);
v___x_856_ = ((size_t)0ULL);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_837_, v_arg_838_, v_headApp_839_, v___x_853_, v_sz_855_, v___x_856_, v___x_854_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec_ref(v___x_853_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v___x_857_, 0);
lean_dec(v_unused_865_);
v___x_859_ = v___x_857_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_dec(v___x_857_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_854_);
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_854_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed(lean_object* v_probeExpr_866_, lean_object* v_forwarded_867_, lean_object* v_arg_868_, lean_object* v_headApp_869_, lean_object* v_fvars_870_, lean_object* v_x_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(v_probeExpr_866_, v_forwarded_867_, v_arg_868_, v_headApp_869_, v_fvars_870_, v_x_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec_ref(v_x_871_);
lean_dec_ref(v_fvars_870_);
lean_dec_ref(v_forwarded_867_);
return v_res_877_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(lean_object* v_headApp_887_, lean_object* v_forwarded_888_, lean_object* v_probeExpr_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_895_; 
lean_inc(v_a_893_);
lean_inc_ref(v_a_892_);
lean_inc(v_a_891_);
lean_inc_ref(v_a_890_);
lean_inc_ref(v_probeExpr_889_);
v___x_895_ = lean_infer_type(v_probeExpr_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_896_, v_a_891_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_897_);
v___x_899_ = l_Lean_Meta_whnfD(v_a_898_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v_reject_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
lean_inc(v_headApp_887_);
v_reject_901_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed), 8, 1);
lean_closure_set(v_reject_901_, 0, v_headApp_887_);
if (lean_obj_tag(v_a_900_) == 5)
{
lean_object* v_arg_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; uint8_t v___x_934_; 
v_arg_902_ = lean_ctor_get(v_a_900_, 1);
lean_inc_ref_n(v_arg_902_, 3);
lean_inc_n(v_headApp_887_, 2);
v___f_903_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed), 11, 4);
lean_closure_set(v___f_903_, 0, v_a_900_);
lean_closure_set(v___f_903_, 1, v_arg_902_);
lean_closure_set(v___f_903_, 2, v_headApp_887_);
lean_closure_set(v___f_903_, 3, v_reject_901_);
lean_inc_ref(v_forwarded_888_);
lean_inc_ref(v_probeExpr_889_);
v___f_904_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed), 11, 4);
lean_closure_set(v___f_904_, 0, v_probeExpr_889_);
lean_closure_set(v___f_904_, 1, v_forwarded_888_);
lean_closure_set(v___f_904_, 2, v_arg_902_);
lean_closure_set(v___f_904_, 3, v_headApp_887_);
v___x_934_ = l_Lean_Expr_isMVar(v_arg_902_);
lean_dec_ref(v_arg_902_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref(v___f_904_);
lean_dec_ref(v___f_903_);
lean_dec_ref(v_probeExpr_889_);
lean_dec_ref(v_forwarded_888_);
v___x_935_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1);
v___x_936_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_887_, lean_box(0), v___x_935_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
return v___x_936_;
}
else
{
lean_dec(v_headApp_887_);
v___y_906_ = v_a_890_;
v___y_907_ = v_a_891_;
v___y_908_ = v_a_892_;
v___y_909_ = v_a_893_;
goto v___jp_905_;
}
v___jp_905_:
{
lean_object* v___x_910_; 
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
v___x_910_ = lean_infer_type(v_forwarded_888_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; uint8_t v___x_912_; lean_object* v___x_913_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = 0;
v___x_913_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_911_, v___f_903_, v___x_912_, v___x_912_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec_ref_known(v___x_913_, 1);
v___x_914_ = l_Lean_Expr_getAppFn(v_probeExpr_889_);
lean_dec_ref(v_probeExpr_889_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
v___x_915_ = lean_infer_type(v___x_914_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_916_, v___f_904_, v___x_912_, v___x_912_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
return v___x_917_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v___f_904_);
v_a_918_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_915_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_915_);
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
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
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
lean_dec_ref(v___f_904_);
lean_dec_ref(v_probeExpr_889_);
return v___x_913_;
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v___f_904_);
lean_dec_ref(v___f_903_);
lean_dec_ref(v_probeExpr_889_);
v_a_926_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_910_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_910_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec_ref(v_reject_901_);
lean_dec_ref(v_probeExpr_889_);
lean_dec_ref(v_forwarded_888_);
v___x_937_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3);
v___x_938_ = l_Lean_MessageData_ofExpr(v_a_900_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_887_, lean_box(0), v___x_941_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
return v___x_942_;
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v_probeExpr_889_);
lean_dec_ref(v_forwarded_888_);
lean_dec(v_headApp_887_);
v_a_943_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_899_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_899_);
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
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
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
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref(v_probeExpr_889_);
lean_dec_ref(v_forwarded_888_);
lean_dec(v_headApp_887_);
v_a_951_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_895_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_895_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___boxed(lean_object* v_headApp_959_, lean_object* v_forwarded_960_, lean_object* v_probeExpr_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_headApp_959_, v_forwarded_960_, v_probeExpr_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(lean_object* v_00_u03b1_968_, lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___boxed(lean_object* v_00_u03b1_976_, lean_object* v_msg_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(v_00_u03b1_976_, v_msg_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_983_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3));
v___x_993_ = l_String_toRawSubstring_x27(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_fst_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_ref_1013_; lean_object* v_quotContext_1014_; lean_object* v_currMacroScope_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; 
v_ref_1013_ = lean_ctor_get(v___y_1010_, 5);
v_quotContext_1014_ = lean_ctor_get(v___y_1010_, 10);
v_currMacroScope_1015_ = lean_ctor_get(v___y_1010_, 11);
v___x_1016_ = 0;
v___x_1017_ = l_Lean_SourceInfo_fromRef(v_ref_1013_, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1));
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2));
lean_inc_n(v___x_1017_, 3);
v___x_1020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1017_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4, &l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4);
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5));
lean_inc(v_currMacroScope_1015_);
lean_inc(v_quotContext_1014_);
v___x_1023_ = l_Lean_addMacroScope(v_quotContext_1014_, v___x_1022_, v_currMacroScope_1015_);
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1017_);
lean_ctor_set(v___x_1025_, 1, v___x_1021_);
lean_ctor_set(v___x_1025_, 2, v___x_1023_);
lean_ctor_set(v___x_1025_, 3, v___x_1024_);
v___x_1026_ = l_Lean_Syntax_node2(v___x_1017_, v___x_1018_, v___x_1020_, v___x_1025_);
v___x_1027_ = lean_box(0);
v___x_1028_ = 1;
lean_inc(v___x_1026_);
v___x_1029_ = l_Lean_Elab_Term_elabTerm(v___x_1026_, v___x_1027_, v___x_1028_, v___x_1028_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7));
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9));
lean_inc(v___x_1017_);
v___x_1033_ = l_Lean_Syntax_node1(v___x_1017_, v___x_1032_, v___x_1026_);
v___x_1034_ = l_Lean_Syntax_node2(v___x_1017_, v___x_1031_, v_fst_1009_, v___x_1033_);
v___x_1035_ = l_Lean_Elab_Term_elabTerm(v___x_1034_, v___x_1027_, v___x_1028_, v___x_1028_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v___y_1010_, v___y_1011_);
lean_dec_ref(v___y_1010_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v_a_1030_);
lean_ctor_set(v___x_1040_, 1, v_a_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_a_1030_);
v_a_1045_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1035_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1035_);
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
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
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
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec(v___x_1026_);
lean_dec(v___x_1017_);
lean_dec_ref(v___y_1010_);
lean_dec(v_fst_1009_);
v_a_1053_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1029_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1029_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed(lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_fst_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_fst_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(lean_object* v_body_1070_, lean_object* v_cont_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
uint8_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = 1;
v___x_1081_ = l_Lean_Elab_Do_elabDoSeq(v_body_1070_, v_cont_1071_, v___x_1080_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed(lean_object* v_body_1082_, lean_object* v_cont_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(v_body_1082_, v_cont_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(lean_object* v_a_1093_, lean_object* v___f_1094_, lean_object* v_a_1095_, lean_object* v_bsExpr_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_Elab_Do_EffectForwarder_lift(v_a_1093_, v___f_1094_, v_a_1095_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; uint8_t v___x_1107_; uint8_t v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___x_1107_ = 0;
v___x_1108_ = 1;
v___x_1109_ = 1;
v___x_1110_ = l_Lean_Meta_mkLambdaFVars(v_bsExpr_1096_, v_a_1106_, v___x_1107_, v___x_1108_, v___x_1107_, v___x_1108_, v___x_1109_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
return v___x_1110_;
}
else
{
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed(lean_object* v_a_1111_, lean_object* v___f_1112_, lean_object* v_a_1113_, lean_object* v_bsExpr_1114_, lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(v_a_1111_, v___f_1112_, v_a_1113_, v_bsExpr_1114_, v_x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_x_1115_);
lean_dec_ref(v_bsExpr_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(lean_object* v_msg_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_ref_1130_; lean_object* v___x_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1140_; 
v_ref_1130_ = lean_ctor_get(v___y_1127_, 5);
v___x_1131_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_inc(v_ref_1130_);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_ref_1130_);
lean_ctor_set(v___x_1136_, 1, v_a_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 1);
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg___boxed(lean_object* v_msg_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_msg_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(size_t v_sz_1148_, size_t v_i_1149_, lean_object* v_bs_1150_){
_start:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_usize_dec_lt(v_i_1149_, v_sz_1148_);
if (v___x_1151_ == 0)
{
return v_bs_1150_;
}
else
{
lean_object* v_v_1152_; lean_object* v___x_1153_; lean_object* v_bs_x27_1154_; size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; 
v_v_1152_ = lean_array_uget(v_bs_1150_, v_i_1149_);
v___x_1153_ = lean_unsigned_to_nat(0u);
v_bs_x27_1154_ = lean_array_uset(v_bs_1150_, v_i_1149_, v___x_1153_);
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1149_, v___x_1155_);
v___x_1157_ = lean_array_uset(v_bs_x27_1154_, v_i_1149_, v_v_1152_);
v_i_1149_ = v___x_1156_;
v_bs_1150_ = v___x_1157_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___boxed(lean_object* v_sz_1159_, lean_object* v_i_1160_, lean_object* v_bs_1161_){
_start:
{
size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1159_);
lean_dec(v_sz_1159_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(v_sz_boxed_1162_, v_i_boxed_1163_, v_bs_1161_);
return v_res_1164_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f(lean_object* v_e_1168_, lean_object* v_dec_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v_e_1168_);
if (lean_obj_tag(v___x_1178_) == 1)
{
lean_object* v_val_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1305_; 
v_val_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1305_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_val_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1305_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_fst_1183_; lean_object* v_snd_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; 
v_fst_1183_ = lean_ctor_get(v_val_1179_, 0);
lean_inc_n(v_fst_1183_, 2);
v_snd_1184_ = lean_ctor_get(v_val_1179_, 1);
lean_inc(v_snd_1184_);
lean_dec(v_val_1179_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc(v_a_1172_);
lean_inc_ref(v_a_1171_);
v___f_1185_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed), 8, 5);
lean_closure_set(v___f_1185_, 0, v_a_1171_);
lean_closure_set(v___f_1185_, 1, v_a_1172_);
lean_closure_set(v___f_1185_, 2, v_a_1173_);
lean_closure_set(v___f_1185_, 3, v_a_1174_);
lean_closure_set(v___f_1185_, 4, v_fst_1183_);
v___x_1186_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_1185_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v___x_1190_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v_fst_1188_ = lean_ctor_get(v_a_1187_, 0);
lean_inc_n(v_fst_1188_, 2);
v_snd_1189_ = lean_ctor_get(v_a_1187_, 1);
lean_inc_n(v_snd_1189_, 2);
lean_dec(v_a_1187_);
v___x_1190_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_fst_1183_, v_fst_1188_, v_snd_1189_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_binders_1191_; lean_object* v_body_1192_; lean_object* v___x_1193_; 
lean_dec_ref_known(v___x_1190_, 1);
v_binders_1191_ = lean_ctor_get(v_snd_1184_, 0);
lean_inc_ref(v_binders_1191_);
v_body_1192_ = lean_ctor_get(v_snd_1184_, 1);
lean_inc_n(v_body_1192_, 2);
lean_dec(v_snd_1184_);
v___x_1193_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_1192_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_a_1194_, v_dec_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec(v_a_1194_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___f_1235_; lean_object* v___f_1236_; size_t v_sz_1237_; size_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_n(v_a_1196_, 2);
lean_dec_ref_known(v___x_1195_, 1);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1235_, 0, v_body_1192_);
lean_inc_ref(v_a_1170_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed), 12, 3);
lean_closure_set(v___f_1236_, 0, v_a_1196_);
lean_closure_set(v___f_1236_, 1, v___f_1235_);
lean_closure_set(v___f_1236_, 2, v_a_1170_);
v_sz_1237_ = lean_array_size(v_binders_1191_);
v___x_1238_ = ((size_t)0ULL);
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(v_sz_1237_, v___x_1238_, v_binders_1191_);
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Lean_Elab_Term_elabFunBinders___redArg(v___x_1239_, v___x_1240_, v___f_1236_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec_ref(v___x_1239_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = l_Lean_Expr_mvarId_x21(v_fst_1188_);
lean_dec(v_fst_1188_);
lean_inc(v_a_1176_);
lean_inc_ref(v_a_1175_);
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
v___x_1244_ = lean_checked_assign(v___x_1243_, v_a_1242_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; uint8_t v___x_1246_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = lean_unbox(v_a_1245_);
lean_dec(v_a_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v_a_1196_);
lean_dec(v_snd_1189_);
lean_del_object(v___x_1181_);
v___x_1247_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1);
v___x_1248_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v___x_1247_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
v___y_1198_ = v_a_1170_;
v___y_1199_ = v_a_1171_;
v___y_1200_ = v_a_1172_;
v___y_1201_ = v_a_1173_;
v___y_1202_ = v_a_1174_;
v___y_1203_ = v_a_1175_;
v___y_1204_ = v_a_1176_;
goto v___jp_1197_;
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_a_1196_);
lean_dec(v_snd_1189_);
lean_del_object(v___x_1181_);
v_a_1257_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1244_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1244_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_a_1196_);
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
lean_del_object(v___x_1181_);
v_a_1265_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1241_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1241_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
v___jp_1197_:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_a_1196_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1207_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v___x_1205_, 1);
v___x_1207_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_1206_, v_snd_1189_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1218_; 
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1210_ = v___x_1207_;
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1207_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1218_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v_a_1208_);
v___x_1213_ = v___x_1181_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1213_);
v___x_1215_ = v___x_1210_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_del_object(v___x_1181_);
v_a_1219_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1207_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1207_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec(v_snd_1189_);
lean_del_object(v___x_1181_);
v_a_1227_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1205_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1205_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_body_1192_);
lean_dec_ref(v_binders_1191_);
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
lean_del_object(v___x_1181_);
v_a_1273_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1195_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1195_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_body_1192_);
lean_dec_ref(v_binders_1191_);
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
lean_del_object(v___x_1181_);
lean_dec_ref(v_dec_1169_);
v_a_1281_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1193_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1193_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
lean_dec(v_snd_1184_);
lean_del_object(v___x_1181_);
lean_dec_ref(v_dec_1169_);
v_a_1289_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1190_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1190_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec(v_snd_1184_);
lean_dec(v_fst_1183_);
lean_del_object(v___x_1181_);
lean_dec_ref(v_dec_1169_);
v_a_1297_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1186_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1186_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec(v___x_1178_);
lean_dec_ref(v_dec_1169_);
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___boxed(lean_object* v_e_1308_, lean_object* v_dec_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Elab_Do_tryElabForwardApp_x3f(v_e_1308_, v_dec_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec_ref(v_a_1310_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(lean_object* v_00_u03b1_1319_, lean_object* v_msg_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_msg_1320_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_msg_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(v_00_u03b1_1330_, v_msg_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1340_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin) {
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
lean_object* initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin) {
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
res = initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Forward(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_Forward(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_Forward(builtin);
}
#ifdef __cplusplus
}
#endif
