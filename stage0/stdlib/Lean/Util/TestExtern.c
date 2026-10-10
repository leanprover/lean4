// Lean compiler output
// Module: Lean.Util.TestExtern
// Imports: public meta import Lean.Meta.Tactic.Unfold public meta import Lean.Meta.Eval public meta import Lean.Compiler.ImplementedByAttr public meta import Lean.Elab.Command public import Init.Notation import Lean.Exception public meta import Lean.Compiler.ExternAttr
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getImplementedBy_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_testExternCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_testExternCmd___closed__0 = (const lean_object*)&l_Lean_testExternCmd___closed__0_value;
static const lean_string_object l_Lean_testExternCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "testExternCmd"};
static const lean_object* l_Lean_testExternCmd___closed__1 = (const lean_object*)&l_Lean_testExternCmd___closed__1_value;
static const lean_ctor_object l_Lean_testExternCmd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_testExternCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_testExternCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_testExternCmd___closed__2_value_aux_0),((lean_object*)&l_Lean_testExternCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 105, 245, 61, 9, 235, 143, 113)}};
static const lean_object* l_Lean_testExternCmd___closed__2 = (const lean_object*)&l_Lean_testExternCmd___closed__2_value;
static const lean_string_object l_Lean_testExternCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_testExternCmd___closed__3 = (const lean_object*)&l_Lean_testExternCmd___closed__3_value;
static const lean_ctor_object l_Lean_testExternCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_testExternCmd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_testExternCmd___closed__4 = (const lean_object*)&l_Lean_testExternCmd___closed__4_value;
static const lean_string_object l_Lean_testExternCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "test_extern "};
static const lean_object* l_Lean_testExternCmd___closed__5 = (const lean_object*)&l_Lean_testExternCmd___closed__5_value;
static const lean_ctor_object l_Lean_testExternCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_testExternCmd___closed__5_value)}};
static const lean_object* l_Lean_testExternCmd___closed__6 = (const lean_object*)&l_Lean_testExternCmd___closed__6_value;
static const lean_string_object l_Lean_testExternCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_testExternCmd___closed__7 = (const lean_object*)&l_Lean_testExternCmd___closed__7_value;
static const lean_ctor_object l_Lean_testExternCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_testExternCmd___closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_testExternCmd___closed__8 = (const lean_object*)&l_Lean_testExternCmd___closed__8_value;
static const lean_ctor_object l_Lean_testExternCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_testExternCmd___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_testExternCmd___closed__9 = (const lean_object*)&l_Lean_testExternCmd___closed__9_value;
static const lean_ctor_object l_Lean_testExternCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_testExternCmd___closed__4_value),((lean_object*)&l_Lean_testExternCmd___closed__6_value),((lean_object*)&l_Lean_testExternCmd___closed__9_value)}};
static const lean_object* l_Lean_testExternCmd___closed__10 = (const lean_object*)&l_Lean_testExternCmd___closed__10_value;
static const lean_ctor_object l_Lean_testExternCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_testExternCmd___closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_testExternCmd___closed__10_value)}};
static const lean_object* l_Lean_testExternCmd___closed__11 = (const lean_object*)&l_Lean_testExternCmd___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_testExternCmd = (const lean_object*)&l_Lean_testExternCmd___closed__11_value;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__0 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_elabTestExtern___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_elabTestExtern___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__1 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__2;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "native implementation did not agree with reference implementation!\n"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__3 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_elabTestExtern___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_elabTestExtern___lam__0___closed__3_value)}};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__4 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__5;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Compare the outputs of:\n#eval "};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__6 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__7;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\n and\n#eval "};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__8 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__9;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "test_extern: "};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__10 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__11;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = " does not have an @[extern] attribute or @[implemented_by] attribute"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__12 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__13;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "test_extern: expects a function application"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__14 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__15;
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_elabTestExtern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_29_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
return v___x_29_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg(){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_33_;
v_res_33_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg();
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___boxed(lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg();
return v_res_35_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0(lean_object* v_00_u03b1_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg();
return v___x_40_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_37_ = stack[1].m_obj;
lean_object* v___y_38_ = stack[2].m_obj;
lean_object* v_res_41_;
v_res_41_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0(lean_box(0), v___y_37_, v___y_38_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___boxed(lean_object* v_00_u03b1_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0(v_00_u03b1_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
return v_res_46_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1(lean_object* v_msgData_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v___x_53_; lean_object* v_env_54_; uint8_t v___x_55_; lean_object* v_env_56_; lean_object* v___x_57_; lean_object* v_toCold_58_; lean_object* v_mctx_59_; lean_object* v_lctx_60_; lean_object* v_options_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_53_ = lean_st_ref_get(v___y_51_);
v_env_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_ref(v_env_54_);
lean_dec(v___x_53_);
v___x_55_ = 0;
v_env_56_ = l_Lean_Environment_setRecordingDeps(v_env_54_, v___x_55_);
v___x_57_ = lean_st_ref_get(v___y_49_);
v_toCold_58_ = lean_ctor_get(v___y_50_, 0);
v_mctx_59_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_mctx_59_);
lean_dec(v___x_57_);
v_lctx_60_ = lean_ctor_get(v___y_48_, 2);
v_options_61_ = lean_ctor_get(v_toCold_58_, 2);
lean_inc_ref(v_options_61_);
lean_inc_ref(v_lctx_60_);
v___x_62_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_62_, 0, v_env_56_);
lean_ctor_set(v___x_62_, 1, v_mctx_59_);
lean_ctor_set(v___x_62_, 2, v_lctx_60_);
lean_ctor_set(v___x_62_, 3, v_options_61_);
v___x_63_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v_msgData_47_);
v___x_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_47_ = stack[0].m_obj;
lean_object* v___y_48_ = stack[1].m_obj;
lean_object* v___y_49_ = stack[2].m_obj;
lean_object* v___y_50_ = stack[3].m_obj;
lean_object* v___y_51_ = stack[4].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1(v_msgData_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1___boxed(lean_object* v_msgData_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1(v_msgData_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_72_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3(lean_object* v_opts_73_, lean_object* v_opt_74_){
_start:
{
lean_object* v_name_75_; lean_object* v_defValue_76_; lean_object* v_map_77_; lean_object* v___x_78_; 
v_name_75_ = lean_ctor_get(v_opt_74_, 0);
v_defValue_76_ = lean_ctor_get(v_opt_74_, 1);
v_map_77_ = lean_ctor_get(v_opts_73_, 0);
v___x_78_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_77_, v_name_75_);
if (lean_obj_tag(v___x_78_) == 0)
{
uint8_t v___x_79_; 
v___x_79_ = lean_unbox(v_defValue_76_);
return v___x_79_;
}
else
{
lean_object* v_val_80_; 
v_val_80_ = lean_ctor_get(v___x_78_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v___x_78_, 1);
if (lean_obj_tag(v_val_80_) == 1)
{
uint8_t v_v_81_; 
v_v_81_ = lean_ctor_get_uint8(v_val_80_, 0);
lean_dec_ref_known(v_val_80_, 0);
return v_v_81_;
}
else
{
uint8_t v___x_82_; 
lean_dec(v_val_80_);
v___x_82_ = lean_unbox(v_defValue_76_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_73_ = stack[0].m_obj;
lean_object* v_opt_74_ = stack[1].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3(v_opts_73_, v_opt_74_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_84_, lean_object* v_opt_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3(v_opts_84_, v_opt_85_);
lean_dec_ref(v_opt_85_);
lean_dec_ref(v_opts_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_box(1);
v___x_89_ = l_Lean_MessageData_ofFormat(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__2));
v___x_94_ = l_Lean_MessageData_ofFormat(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
return v_x_95_;
}
else
{
lean_object* v_head_97_; lean_object* v_tail_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_120_; 
v_head_97_ = lean_ctor_get(v_x_96_, 0);
v_tail_98_ = lean_ctor_get(v_x_96_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_96_);
if (v_isSharedCheck_120_ == 0)
{
v___x_100_ = v_x_96_;
v_isShared_101_ = v_isSharedCheck_120_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_tail_98_);
lean_inc(v_head_97_);
lean_dec(v_x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_120_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_before_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_118_; 
v_before_102_ = lean_ctor_get(v_head_97_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_head_97_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v_head_97_, 1);
lean_dec(v_unused_119_);
v___x_104_ = v_head_97_;
v_isShared_105_ = v_isSharedCheck_118_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_before_102_);
lean_dec(v_head_97_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_118_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_105_ == 0)
{
lean_ctor_set_tag(v___x_104_, 7);
lean_ctor_set(v___x_104_, 1, v___x_106_);
lean_ctor_set(v___x_104_, 0, v_x_95_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_x_95_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_106_);
v___x_108_ = v_reuseFailAlloc_117_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_101_ == 0)
{
lean_ctor_set_tag(v___x_100_, 7);
lean_ctor_set(v___x_100_, 1, v___x_109_);
lean_ctor_set(v___x_100_, 0, v___x_108_);
v___x_111_ = v___x_100_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_116_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = l_Lean_MessageData_ofSyntax(v_before_102_);
v___x_113_ = l_Lean_indentD(v___x_112_);
v___x_114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_111_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v_x_95_ = v___x_114_;
v_x_96_ = v_tail_98_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__1));
v___x_125_ = l_Lean_MessageData_ofFormat(v___x_124_);
return v___x_125_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(lean_object* v_msgData_126_, lean_object* v_macroStack_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_130_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_128_);
v___x_131_ = l_Lean_Elab_pp_macroStack;
v___x_132_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3(v___x_130_, v___x_131_);
lean_dec_ref(v___x_130_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
lean_dec(v_macroStack_127_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_msgData_126_);
return v___x_133_;
}
else
{
if (lean_obj_tag(v_macroStack_127_) == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v_msgData_126_);
return v___x_134_;
}
else
{
lean_object* v_head_135_; lean_object* v_after_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_151_; 
v_head_135_ = lean_ctor_get(v_macroStack_127_, 0);
lean_inc(v_head_135_);
v_after_136_ = lean_ctor_get(v_head_135_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_head_135_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v_head_135_, 0);
lean_dec(v_unused_152_);
v___x_138_ = v_head_135_;
v_isShared_139_ = v_isSharedCheck_151_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_after_136_);
lean_dec(v_head_135_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_151_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 7);
lean_ctor_set(v___x_138_, 1, v___x_140_);
lean_ctor_set(v___x_138_, 0, v_msgData_126_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_msgData_126_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_150_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v_msgData_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_143_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2);
v___x_144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = l_Lean_MessageData_ofSyntax(v_after_136_);
v___x_146_ = l_Lean_indentD(v___x_145_);
v_msgData_147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_147_, 0, v___x_144_);
lean_ctor_set(v_msgData_147_, 1, v___x_146_);
v___x_148_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4(v_msgData_147_, v_macroStack_127_);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_126_ = stack[0].m_obj;
lean_object* v_macroStack_127_ = stack[1].m_obj;
lean_object* v___y_128_ = stack[2].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(v_msgData_126_, v_macroStack_127_, v___y_128_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_154_, lean_object* v_macroStack_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(v_msgData_154_, v_macroStack_155_, v___y_156_);
lean_dec_ref(v___y_156_);
return v_res_158_;
}
}
lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(lean_object* v_msg_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_ref_167_; lean_object* v_macroStack_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v_a_171_; lean_object* v___x_172_; lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_ref_167_ = lean_ctor_get(v___y_164_, 2);
v_macroStack_168_ = lean_ctor_get(v___y_160_, 1);
v___x_169_ = l_Lean_Elab_getBetterRef(v_ref_167_, v_macroStack_168_);
v___x_170_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1(v_msg_159_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
lean_inc(v_macroStack_168_);
v___x_172_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(v_a_171_, v_macroStack_168_, v___y_164_);
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_169_);
lean_ctor_set(v___x_177_, 1, v_a_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set_tag(v___x_175_, 1);
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_159_ = stack[0].m_obj;
lean_object* v___y_160_ = stack[1].m_obj;
lean_object* v___y_161_ = stack[2].m_obj;
lean_object* v___y_162_ = stack[3].m_obj;
lean_object* v___y_163_ = stack[4].m_obj;
lean_object* v___y_164_ = stack[5].m_obj;
lean_object* v___y_165_ = stack[6].m_obj;
lean_object* v_res_182_;
v_res_182_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v_msg_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg___boxed(lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v_msg_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_191_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__2(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_box(0);
v___x_196_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__1));
v___x_197_ = l_Lean_Expr_const___override(v___x_196_, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__5(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__4));
v___x_202_ = l_Lean_MessageData_ofFormat(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__7(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__6));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__9(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__8));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__11(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__10));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__13(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__12));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__15(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__14));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
lean_object* l_Lean_elabTestExtern___lam__0(lean_object* v___x_218_, lean_object* v___x_219_, uint8_t v___x_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Elab_Term_elabTermAndSynthesize(v___x_218_, v___x_219_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v___x_230_ = l_Lean_Expr_getAppFn(v_a_229_);
if (lean_obj_tag(v___x_230_) == 4)
{
lean_object* v_declName_231_; lean_object* v___x_232_; uint8_t v___y_297_; lean_object* v_env_304_; uint8_t v___x_305_; 
v_declName_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc_n(v_declName_231_, 2);
lean_dec_ref_known(v___x_230_, 2);
v___x_232_ = lean_st_ref_get(v___y_226_);
v_env_304_ = lean_ctor_get(v___x_232_, 0);
lean_inc_ref_n(v_env_304_, 2);
lean_dec(v___x_232_);
v___x_305_ = l_Lean_isExtern(v_env_304_, v_declName_231_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
lean_inc(v_declName_231_);
v___x_306_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_304_, v_declName_231_);
if (lean_obj_tag(v___x_306_) == 0)
{
v___y_297_ = v___x_305_;
goto v___jp_296_;
}
else
{
lean_dec_ref_known(v___x_306_, 1);
v___y_297_ = v___x_220_;
goto v___jp_296_;
}
}
else
{
lean_dec_ref(v_env_304_);
goto v___jp_233_;
}
v___jp_233_:
{
lean_object* v___x_234_; 
lean_inc(v_a_229_);
v___x_234_ = l_Lean_Meta_unfold(v_a_229_, v_declName_231_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v_expr_236_; lean_object* v___x_237_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v_expr_236_ = lean_ctor_get(v_a_235_, 0);
lean_inc_ref_n(v_expr_236_, 2);
lean_dec(v_a_235_);
lean_inc(v_a_229_);
v___x_237_ = l_Lean_Meta_mkEq(v_a_229_, v_expr_236_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = l_Lean_Meta_mkDecide(v_a_238_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
v___x_241_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__2, &l_Lean_elabTestExtern___lam__0___closed__2_once, _init_l_Lean_elabTestExtern___lam__0___closed__2);
v___x_242_ = 1;
v___x_243_ = l_Lean_Meta_evalExpr___redArg(v___x_241_, v_a_240_, v___x_242_, v___x_220_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_263_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_263_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_263_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_263_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___x_248_; 
v___x_248_ = lean_unbox(v_a_244_);
lean_dec(v_a_244_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_del_object(v___x_246_);
v___x_249_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__5, &l_Lean_elabTestExtern___lam__0___closed__5_once, _init_l_Lean_elabTestExtern___lam__0___closed__5);
v___x_250_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__7, &l_Lean_elabTestExtern___lam__0___closed__7_once, _init_l_Lean_elabTestExtern___lam__0___closed__7);
v___x_251_ = l_Lean_MessageData_ofExpr(v_a_229_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__9, &l_Lean_elabTestExtern___lam__0___closed__9_once, _init_l_Lean_elabTestExtern___lam__0___closed__9);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = l_Lean_MessageData_ofExpr(v_expr_236_);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_249_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v___x_257_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_dec_ref(v_expr_236_);
lean_dec(v_a_229_);
v___x_259_ = lean_box(0);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_259_);
v___x_261_ = v___x_246_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec_ref(v_expr_236_);
lean_dec(v_a_229_);
v_a_264_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_243_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_243_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v_expr_236_);
lean_dec(v_a_229_);
v_a_272_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_239_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_239_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec_ref(v_expr_236_);
lean_dec(v_a_229_);
v_a_280_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_237_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_237_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v_a_229_);
v_a_288_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_234_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_234_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
v___jp_296_:
{
if (v___y_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_a_229_);
v___x_298_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__11, &l_Lean_elabTestExtern___lam__0___closed__11_once, _init_l_Lean_elabTestExtern___lam__0___closed__11);
v___x_299_ = l_Lean_MessageData_ofName(v_declName_231_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__13, &l_Lean_elabTestExtern___lam__0___closed__13_once, _init_l_Lean_elabTestExtern___lam__0___closed__13);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v___x_302_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_303_;
}
else
{
goto v___jp_233_;
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref(v___x_230_);
lean_dec(v_a_229_);
v___x_307_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__15, &l_Lean_elabTestExtern___lam__0___closed__15_once, _init_l_Lean_elabTestExtern___lam__0___closed__15);
v___x_308_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v___x_307_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
return v___x_308_;
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_228_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_228_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_elabTestExtern___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_218_ = stack[0].m_obj;
lean_object* v___x_219_ = stack[1].m_obj;
uint8_t v___x_220_ = stack[2].m_num;
lean_object* v___y_221_ = stack[3].m_obj;
lean_object* v___y_222_ = stack[4].m_obj;
lean_object* v___y_223_ = stack[5].m_obj;
lean_object* v___y_224_ = stack[6].m_obj;
lean_object* v___y_225_ = stack[7].m_obj;
lean_object* v___y_226_ = stack[8].m_obj;
lean_object* v_res_317_;
v_res_317_ = l_Lean_elabTestExtern___lam__0(v___x_218_, v___x_219_, v___x_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
stack->m_obj
 = v_res_317_;
}
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___lam__0___boxed(lean_object* v___x_318_, lean_object* v___x_319_, lean_object* v___x_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v___x_4141__boxed_328_; lean_object* v_res_329_; 
v___x_4141__boxed_328_ = lean_unbox(v___x_320_);
v_res_329_ = l_Lean_elabTestExtern___lam__0(v___x_318_, v___x_319_, v___x_4141__boxed_328_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_329_;
}
}
lean_object* l_Lean_elabTestExtern(lean_object* v_x_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_testExternCmd___closed__2));
lean_inc(v_x_330_);
v___x_335_ = l_Lean_Syntax_isOfKind(v_x_330_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v_x_330_);
v___x_336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg();
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___f_341_; lean_object* v___x_342_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = l_Lean_Syntax_getArg(v_x_330_, v___x_337_);
lean_dec(v_x_330_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_box(v___x_335_);
v___f_341_ = lean_alloc_closure((void*)(l_Lean_elabTestExtern___lam__0___boxed), 10, 3);
lean_closure_set(v___f_341_, 0, v___x_338_);
lean_closure_set(v___f_341_, 1, v___x_339_);
lean_closure_set(v___f_341_, 2, v___x_340_);
v___x_342_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_341_, v_a_331_, v_a_332_);
return v___x_342_;
}
}
}
LEAN_EXPORT void l_Lean_elabTestExtern_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_330_ = stack[0].m_obj;
lean_object* v_a_331_ = stack[1].m_obj;
lean_object* v_a_332_ = stack[2].m_obj;
lean_object* v_res_343_;
v_res_343_ = l_Lean_elabTestExtern(v_x_330_, v_a_331_, v_a_332_);
stack->m_obj
 = v_res_343_;
}
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___boxed(lean_object* v_x_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_elabTestExtern(v_x_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
return v_res_348_;
}
}
lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1(lean_object* v_00_u03b1_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
return v___x_358_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_elabTestExtern_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_350_ = stack[1].m_obj;
lean_object* v___y_351_ = stack[2].m_obj;
lean_object* v___y_352_ = stack[3].m_obj;
lean_object* v___y_353_ = stack[4].m_obj;
lean_object* v___y_354_ = stack[5].m_obj;
lean_object* v___y_355_ = stack[6].m_obj;
lean_object* v___y_356_ = stack[7].m_obj;
lean_object* v_res_359_;
v_res_359_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1(lean_box(0), v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___boxed(lean_object* v_00_u03b1_360_, lean_object* v_msg_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1(v_00_u03b1_360_, v_msg_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_369_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2(lean_object* v_msgData_370_, lean_object* v_macroStack_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(v_msgData_370_, v_macroStack_371_, v___y_376_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_370_ = stack[0].m_obj;
lean_object* v_macroStack_371_ = stack[1].m_obj;
lean_object* v___y_372_ = stack[2].m_obj;
lean_object* v___y_373_ = stack[3].m_obj;
lean_object* v___y_374_ = stack[4].m_obj;
lean_object* v___y_375_ = stack[5].m_obj;
lean_object* v___y_376_ = stack[6].m_obj;
lean_object* v___y_377_ = stack[7].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2(v_msgData_370_, v_macroStack_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___boxed(lean_object* v_msgData_381_, lean_object* v_macroStack_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2(v_msgData_381_, v_macroStack_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_390_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_TestExtern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_TestExtern(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Lean_Exception(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_TestExtern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_TestExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_TestExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_TestExtern(builtin);
}
#ifdef __cplusplus
}
#endif
