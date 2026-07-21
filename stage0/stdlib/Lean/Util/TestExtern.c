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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceBool"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__0 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__0_value;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__1 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_elabTestExtern___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_elabTestExtern___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__2 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__3;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "native implementation did not agree with reference implementation!\n"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__4 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_elabTestExtern___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_elabTestExtern___lam__0___closed__4_value)}};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__5 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__6;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Compare the outputs of:\n#eval "};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__7 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__8;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\n and\n#eval "};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__9 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__10;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "test_extern: "};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__11 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__12;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = " does not have an @[extern] attribute or @[implemented_by] attribute"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__13 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__13_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__14;
static const lean_string_object l_Lean_elabTestExtern___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "test_extern: expects a function application"};
static const lean_object* l_Lean_elabTestExtern___lam__0___closed__15 = (const lean_object*)&l_Lean_elabTestExtern___lam__0___closed__15_value;
static lean_once_cell_t l_Lean_elabTestExtern___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_elabTestExtern___lam__0___closed__16;
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg(){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___closed__0);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg___boxed(lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg();
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0(lean_object* v_00_u03b1_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg();
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___boxed(lean_object* v_00_u03b1_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0(v_00_u03b1_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1(lean_object* v_msgData_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; lean_object* v_env_52_; lean_object* v___x_53_; lean_object* v_mctx_54_; lean_object* v_lctx_55_; lean_object* v_options_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_51_ = lean_st_ref_get(v___y_49_);
v_env_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc_ref(v_env_52_);
lean_dec(v___x_51_);
v___x_53_ = lean_st_ref_get(v___y_47_);
v_mctx_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc_ref(v_mctx_54_);
lean_dec(v___x_53_);
v_lctx_55_ = lean_ctor_get(v___y_46_, 2);
v_options_56_ = lean_ctor_get(v___y_48_, 2);
lean_inc_ref(v_options_56_);
lean_inc_ref(v_lctx_55_);
v___x_57_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_57_, 0, v_env_52_);
lean_ctor_set(v___x_57_, 1, v_mctx_54_);
lean_ctor_set(v___x_57_, 2, v_lctx_55_);
lean_ctor_set(v___x_57_, 3, v_options_56_);
v___x_58_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v_msgData_45_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1___boxed(lean_object* v_msgData_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1(v_msgData_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
return v_res_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3(lean_object* v_opts_67_, lean_object* v_opt_68_){
_start:
{
lean_object* v_name_69_; lean_object* v_defValue_70_; lean_object* v_map_71_; lean_object* v___x_72_; 
v_name_69_ = lean_ctor_get(v_opt_68_, 0);
v_defValue_70_ = lean_ctor_get(v_opt_68_, 1);
v_map_71_ = lean_ctor_get(v_opts_67_, 0);
v___x_72_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_71_, v_name_69_);
if (lean_obj_tag(v___x_72_) == 0)
{
uint8_t v___x_73_; 
v___x_73_ = lean_unbox(v_defValue_70_);
return v___x_73_;
}
else
{
lean_object* v_val_74_; 
v_val_74_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_val_74_);
lean_dec_ref_known(v___x_72_, 1);
if (lean_obj_tag(v_val_74_) == 1)
{
uint8_t v_v_75_; 
v_v_75_ = lean_ctor_get_uint8(v_val_74_, 0);
lean_dec_ref_known(v_val_74_, 0);
return v_v_75_;
}
else
{
uint8_t v___x_76_; 
lean_dec(v_val_74_);
v___x_76_ = lean_unbox(v_defValue_70_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_77_, lean_object* v_opt_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3(v_opts_77_, v_opt_78_);
lean_dec_ref(v_opt_78_);
lean_dec_ref(v_opts_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_box(1);
v___x_82_ = l_Lean_MessageData_ofFormat(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__2));
v___x_87_ = l_Lean_MessageData_ofFormat(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
return v_x_88_;
}
else
{
lean_object* v_head_90_; lean_object* v_tail_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_113_; 
v_head_90_ = lean_ctor_get(v_x_89_, 0);
v_tail_91_ = lean_ctor_get(v_x_89_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_113_ == 0)
{
v___x_93_ = v_x_89_;
v_isShared_94_ = v_isSharedCheck_113_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_tail_91_);
lean_inc(v_head_90_);
lean_dec(v_x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_113_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_before_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_111_; 
v_before_95_ = lean_ctor_get(v_head_90_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v_head_90_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v_head_90_, 1);
lean_dec(v_unused_112_);
v___x_97_ = v_head_90_;
v_isShared_98_ = v_isSharedCheck_111_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_before_95_);
lean_dec(v_head_90_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_111_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_98_ == 0)
{
lean_ctor_set_tag(v___x_97_, 7);
lean_ctor_set(v___x_97_, 1, v___x_99_);
lean_ctor_set(v___x_97_, 0, v_x_88_);
v___x_101_ = v___x_97_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_x_88_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_110_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 7);
lean_ctor_set(v___x_93_, 1, v___x_102_);
lean_ctor_set(v___x_93_, 0, v___x_101_);
v___x_104_ = v___x_93_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_109_, 1, v___x_102_);
v___x_104_ = v_reuseFailAlloc_109_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = l_Lean_MessageData_ofSyntax(v_before_95_);
v___x_106_ = l_Lean_indentD(v___x_105_);
v___x_107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_104_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v_x_88_ = v___x_107_;
v_x_89_ = v_tail_91_;
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
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__1));
v___x_118_ = l_Lean_MessageData_ofFormat(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(lean_object* v_msgData_119_, lean_object* v_macroStack_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_options_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_options_123_ = lean_ctor_get(v___y_121_, 2);
v___x_124_ = l_Lean_Elab_pp_macroStack;
v___x_125_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__3(v_options_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_dec(v_macroStack_120_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v_msgData_119_);
return v___x_126_;
}
else
{
if (lean_obj_tag(v_macroStack_120_) == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v_msgData_119_);
return v___x_127_;
}
else
{
lean_object* v_head_128_; lean_object* v_after_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_144_; 
v_head_128_ = lean_ctor_get(v_macroStack_120_, 0);
lean_inc(v_head_128_);
v_after_129_ = lean_ctor_get(v_head_128_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_head_128_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v_head_128_, 0);
lean_dec(v_unused_145_);
v___x_131_ = v_head_128_;
v_isShared_132_ = v_isSharedCheck_144_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_after_129_);
lean_dec(v_head_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_144_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_133_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_132_ == 0)
{
lean_ctor_set_tag(v___x_131_, 7);
lean_ctor_set(v___x_131_, 1, v___x_133_);
lean_ctor_set(v___x_131_, 0, v_msgData_119_);
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_msgData_119_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_143_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_msgData_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_136_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___closed__2);
v___x_137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = l_Lean_MessageData_ofSyntax(v_after_129_);
v___x_139_ = l_Lean_indentD(v___x_138_);
v_msgData_140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_140_, 0, v___x_137_);
lean_ctor_set(v_msgData_140_, 1, v___x_139_);
v___x_141_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2_spec__4(v_msgData_140_, v_macroStack_120_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_146_, lean_object* v_macroStack_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(v_msgData_146_, v_macroStack_147_, v___y_148_);
lean_dec_ref(v___y_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_ref_159_; lean_object* v___x_160_; lean_object* v_a_161_; lean_object* v_macroStack_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_173_; 
v_ref_159_ = lean_ctor_get(v___y_156_, 5);
v___x_160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__1(v_msg_151_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref(v___x_160_);
v_macroStack_162_ = lean_ctor_get(v___y_152_, 1);
v___x_163_ = l_Lean_Elab_getBetterRef(v_ref_159_, v_macroStack_162_);
lean_inc(v_macroStack_162_);
v___x_164_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(v_a_161_, v_macroStack_162_, v___y_156_);
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_173_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_173_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_163_);
lean_ctor_set(v___x_169_, 1, v_a_165_);
if (v_isShared_168_ == 0)
{
lean_ctor_set_tag(v___x_167_, 1);
lean_ctor_set(v___x_167_, 0, v___x_169_);
v___x_171_ = v___x_167_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg___boxed(lean_object* v_msg_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v_msg_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_182_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__3(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_box(0);
v___x_188_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__2));
v___x_189_ = l_Lean_Expr_const___override(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__6(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__5));
v___x_194_ = l_Lean_MessageData_ofFormat(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__8(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__7));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__10(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__9));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__12(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__11));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__14(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__13));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_Lean_elabTestExtern___lam__0___closed__16(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__15));
v___x_209_ = l_Lean_stringToMessageData(v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___lam__0(lean_object* v___x_210_, lean_object* v___x_211_, lean_object* v___x_212_, uint8_t v___x_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Elab_Term_elabTermAndSynthesize(v___x_210_, v___x_211_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_221_, 1);
v___x_223_ = l_Lean_Expr_getAppFn(v_a_222_);
if (lean_obj_tag(v___x_223_) == 4)
{
lean_object* v_declName_224_; lean_object* v___x_225_; uint8_t v___y_295_; lean_object* v_env_302_; uint8_t v___x_303_; 
v_declName_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc_n(v_declName_224_, 2);
lean_dec_ref_known(v___x_223_, 2);
v___x_225_ = lean_st_ref_get(v___y_219_);
v_env_302_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref_n(v_env_302_, 2);
lean_dec(v___x_225_);
v___x_303_ = l_Lean_isExtern(v_env_302_, v_declName_224_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_inc(v_declName_224_);
v___x_304_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_302_, v_declName_224_);
if (lean_obj_tag(v___x_304_) == 0)
{
v___y_295_ = v___x_303_;
goto v___jp_294_;
}
else
{
lean_dec_ref_known(v___x_304_, 1);
v___y_295_ = v___x_213_;
goto v___jp_294_;
}
}
else
{
lean_dec_ref(v_env_302_);
goto v___jp_226_;
}
v___jp_226_:
{
lean_object* v___x_227_; 
lean_inc(v_a_222_);
v___x_227_ = l_Lean_Meta_unfold(v_a_222_, v_declName_224_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v_expr_229_; lean_object* v___x_230_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v_expr_229_ = lean_ctor_get(v_a_228_, 0);
lean_inc_ref_n(v_expr_229_, 2);
lean_dec(v_a_228_);
lean_inc(v_a_222_);
v___x_230_ = l_Lean_Meta_mkEq(v_a_222_, v_expr_229_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = l_Lean_Meta_mkDecide(v_a_231_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = ((lean_object*)(l_Lean_elabTestExtern___lam__0___closed__0));
v___x_235_ = l_Lean_Name_mkStr2(v___x_212_, v___x_234_);
v___x_236_ = lean_box(0);
v___x_237_ = l_Lean_Expr_const___override(v___x_235_, v___x_236_);
v___x_238_ = l_Lean_Expr_app___override(v___x_237_, v_a_233_);
v___x_239_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__3, &l_Lean_elabTestExtern___lam__0___closed__3_once, _init_l_Lean_elabTestExtern___lam__0___closed__3);
v___x_240_ = 1;
v___x_241_ = l_Lean_Meta_evalExpr___redArg(v___x_239_, v___x_238_, v___x_240_, v___x_213_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_261_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_261_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_261_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_261_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
uint8_t v___x_246_; 
v___x_246_ = lean_unbox(v_a_242_);
lean_dec(v_a_242_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_del_object(v___x_244_);
v___x_247_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__6, &l_Lean_elabTestExtern___lam__0___closed__6_once, _init_l_Lean_elabTestExtern___lam__0___closed__6);
v___x_248_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__8, &l_Lean_elabTestExtern___lam__0___closed__8_once, _init_l_Lean_elabTestExtern___lam__0___closed__8);
v___x_249_ = l_Lean_MessageData_ofExpr(v_a_222_);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__10, &l_Lean_elabTestExtern___lam__0___closed__10_once, _init_l_Lean_elabTestExtern___lam__0___closed__10);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = l_Lean_MessageData_ofExpr(v_expr_229_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_247_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v___x_255_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_259_; 
lean_dec_ref(v_expr_229_);
lean_dec(v_a_222_);
v___x_257_ = lean_box(0);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_257_);
v___x_259_ = v___x_244_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref(v_expr_229_);
lean_dec(v_a_222_);
v_a_262_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_241_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_241_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_expr_229_);
lean_dec(v_a_222_);
lean_dec_ref(v___x_212_);
v_a_270_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_232_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_232_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_expr_229_);
lean_dec(v_a_222_);
lean_dec_ref(v___x_212_);
v_a_278_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_230_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_230_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec(v_a_222_);
lean_dec_ref(v___x_212_);
v_a_286_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_227_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_227_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
v___jp_294_:
{
if (v___y_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_a_222_);
lean_dec_ref(v___x_212_);
v___x_296_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__12, &l_Lean_elabTestExtern___lam__0___closed__12_once, _init_l_Lean_elabTestExtern___lam__0___closed__12);
v___x_297_ = l_Lean_MessageData_ofName(v_declName_224_);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__14, &l_Lean_elabTestExtern___lam__0___closed__14_once, _init_l_Lean_elabTestExtern___lam__0___closed__14);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v___x_300_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_301_;
}
else
{
goto v___jp_226_;
}
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref(v___x_223_);
lean_dec(v_a_222_);
lean_dec_ref(v___x_212_);
v___x_305_ = lean_obj_once(&l_Lean_elabTestExtern___lam__0___closed__16, &l_Lean_elabTestExtern___lam__0___closed__16_once, _init_l_Lean_elabTestExtern___lam__0___closed__16);
v___x_306_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v___x_305_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
return v___x_306_;
}
}
else
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec_ref(v___x_212_);
v_a_307_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_221_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_221_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___lam__0___boxed(lean_object* v___x_315_, lean_object* v___x_316_, lean_object* v___x_317_, lean_object* v___x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
uint8_t v___x_5006__boxed_326_; lean_object* v_res_327_; 
v___x_5006__boxed_326_ = lean_unbox(v___x_318_);
v_res_327_ = l_Lean_elabTestExtern___lam__0(v___x_315_, v___x_316_, v___x_317_, v___x_5006__boxed_326_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_elabTestExtern(lean_object* v_x_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = ((lean_object*)(l_Lean_testExternCmd___closed__0));
v___x_333_ = ((lean_object*)(l_Lean_testExternCmd___closed__2));
lean_inc(v_x_328_);
v___x_334_ = l_Lean_Syntax_isOfKind(v_x_328_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_x_328_);
v___x_335_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_elabTestExtern_spec__0___redArg();
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___f_340_; lean_object* v___x_341_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = l_Lean_Syntax_getArg(v_x_328_, v___x_336_);
lean_dec(v_x_328_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_box(v___x_334_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_elabTestExtern___lam__0___boxed), 11, 4);
lean_closure_set(v___f_340_, 0, v___x_337_);
lean_closure_set(v___f_340_, 1, v___x_338_);
lean_closure_set(v___f_340_, 2, v___x_332_);
lean_closure_set(v___f_340_, 3, v___x_339_);
v___x_341_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_340_, v_a_329_, v_a_330_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_elabTestExtern___boxed(lean_object* v_x_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_elabTestExtern(v_x_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1(lean_object* v_00_u03b1_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___redArg(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_elabTestExtern_spec__1___boxed(lean_object* v_00_u03b1_357_, lean_object* v_msg_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_throwError___at___00Lean_elabTestExtern_spec__1(v_00_u03b1_357_, v_msg_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2(lean_object* v_msgData_367_, lean_object* v_macroStack_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___redArg(v_msgData_367_, v_macroStack_368_, v___y_373_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2___boxed(lean_object* v_msgData_377_, lean_object* v_macroStack_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_elabTestExtern_spec__1_spec__2(v_msgData_377_, v_macroStack_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_386_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_TestExtern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
