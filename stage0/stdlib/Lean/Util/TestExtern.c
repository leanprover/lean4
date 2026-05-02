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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getImplementedBy_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_testExternCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "testExternCmd"};
static const lean_object* l_testExternCmd___closed__0 = (const lean_object*)&l_testExternCmd___closed__0_value;
static const lean_ctor_object l_testExternCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_testExternCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 24, 25, 40, 221, 224, 5, 217)}};
static const lean_object* l_testExternCmd___closed__1 = (const lean_object*)&l_testExternCmd___closed__1_value;
static const lean_string_object l_testExternCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_testExternCmd___closed__2 = (const lean_object*)&l_testExternCmd___closed__2_value;
static const lean_ctor_object l_testExternCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_testExternCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_testExternCmd___closed__3 = (const lean_object*)&l_testExternCmd___closed__3_value;
static const lean_string_object l_testExternCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "test_extern "};
static const lean_object* l_testExternCmd___closed__4 = (const lean_object*)&l_testExternCmd___closed__4_value;
static const lean_ctor_object l_testExternCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_testExternCmd___closed__4_value)}};
static const lean_object* l_testExternCmd___closed__5 = (const lean_object*)&l_testExternCmd___closed__5_value;
static const lean_string_object l_testExternCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_testExternCmd___closed__6 = (const lean_object*)&l_testExternCmd___closed__6_value;
static const lean_ctor_object l_testExternCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_testExternCmd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_testExternCmd___closed__7 = (const lean_object*)&l_testExternCmd___closed__7_value;
static const lean_ctor_object l_testExternCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_testExternCmd___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_testExternCmd___closed__8 = (const lean_object*)&l_testExternCmd___closed__8_value;
static const lean_ctor_object l_testExternCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_testExternCmd___closed__3_value),((lean_object*)&l_testExternCmd___closed__5_value),((lean_object*)&l_testExternCmd___closed__8_value)}};
static const lean_object* l_testExternCmd___closed__9 = (const lean_object*)&l_testExternCmd___closed__9_value;
static const lean_ctor_object l_testExternCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_testExternCmd___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_testExternCmd___closed__9_value)}};
static const lean_object* l_testExternCmd___closed__10 = (const lean_object*)&l_testExternCmd___closed__10_value;
LEAN_EXPORT const lean_object* l_testExternCmd = (const lean_object*)&l_testExternCmd___closed__10_value;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_elabTestExtern___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_elabTestExtern___lam__0___closed__0 = (const lean_object*)&l_elabTestExtern___lam__0___closed__0_value;
static const lean_string_object l_elabTestExtern___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceBool"};
static const lean_object* l_elabTestExtern___lam__0___closed__1 = (const lean_object*)&l_elabTestExtern___lam__0___closed__1_value;
static const lean_ctor_object l_elabTestExtern___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_elabTestExtern___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_elabTestExtern___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_elabTestExtern___lam__0___closed__2_value_aux_0),((lean_object*)&l_elabTestExtern___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(114, 197, 237, 28, 99, 199, 232, 30)}};
static const lean_object* l_elabTestExtern___lam__0___closed__2 = (const lean_object*)&l_elabTestExtern___lam__0___closed__2_value;
static lean_once_cell_t l_elabTestExtern___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabTestExtern___lam__0___closed__3;
static const lean_string_object l_elabTestExtern___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_elabTestExtern___lam__0___closed__4 = (const lean_object*)&l_elabTestExtern___lam__0___closed__4_value;
static const lean_ctor_object l_elabTestExtern___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_elabTestExtern___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_elabTestExtern___lam__0___closed__5 = (const lean_object*)&l_elabTestExtern___lam__0___closed__5_value;
static lean_once_cell_t l_elabTestExtern___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabTestExtern___lam__0___closed__6;
static const lean_string_object l_elabTestExtern___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "native implementation did not agree with reference implementation!\n"};
static const lean_object* l_elabTestExtern___lam__0___closed__7 = (const lean_object*)&l_elabTestExtern___lam__0___closed__7_value;
static const lean_ctor_object l_elabTestExtern___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_elabTestExtern___lam__0___closed__7_value)}};
static const lean_object* l_elabTestExtern___lam__0___closed__8 = (const lean_object*)&l_elabTestExtern___lam__0___closed__8_value;
static lean_once_cell_t l_elabTestExtern___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabTestExtern___lam__0___closed__9;
static const lean_string_object l_elabTestExtern___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Compare the outputs of:\n#eval "};
static const lean_object* l_elabTestExtern___lam__0___closed__10 = (const lean_object*)&l_elabTestExtern___lam__0___closed__10_value;
static lean_once_cell_t l_elabTestExtern___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabTestExtern___lam__0___closed__11;
static const lean_string_object l_elabTestExtern___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\n and\n#eval "};
static const lean_object* l_elabTestExtern___lam__0___closed__12 = (const lean_object*)&l_elabTestExtern___lam__0___closed__12_value;
static lean_once_cell_t l_elabTestExtern___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabTestExtern___lam__0___closed__13;
static const lean_string_object l_elabTestExtern___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "test_extern: "};
static const lean_object* l_elabTestExtern___lam__0___closed__14 = (const lean_object*)&l_elabTestExtern___lam__0___closed__14_value;
static lean_once_cell_t l_elabTestExtern___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabTestExtern___lam__0___closed__15;
static const lean_string_object l_elabTestExtern___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = " does not have an @[extern] attribute or @[implemented_by] attribute"};
static const lean_object* l_elabTestExtern___lam__0___closed__16 = (const lean_object*)&l_elabTestExtern___lam__0___closed__16_value;
static lean_once_cell_t l_elabTestExtern___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabTestExtern___lam__0___closed__17;
static const lean_string_object l_elabTestExtern___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "test_extern: expects a function application"};
static const lean_object* l_elabTestExtern___lam__0___closed__18 = (const lean_object*)&l_elabTestExtern___lam__0___closed__18_value;
static lean_once_cell_t l_elabTestExtern___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_elabTestExtern___lam__0___closed__19;
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_box(0);
v___x_26_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___x_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg(){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0);
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___boxed(lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(lean_object* v_00_u03b1_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___boxed(lean_object* v_00_u03b1_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(v_00_u03b1_38_, v___y_39_, v___y_40_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(lean_object* v_msgData_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; lean_object* v_env_50_; lean_object* v___x_51_; lean_object* v_mctx_52_; lean_object* v_lctx_53_; lean_object* v_options_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_49_ = lean_st_ref_get(v___y_47_);
v_env_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc_ref(v_env_50_);
lean_dec(v___x_49_);
v___x_51_ = lean_st_ref_get(v___y_45_);
v_mctx_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc_ref(v_mctx_52_);
lean_dec(v___x_51_);
v_lctx_53_ = lean_ctor_get(v___y_44_, 2);
v_options_54_ = lean_ctor_get(v___y_46_, 2);
lean_inc_ref(v_options_54_);
lean_inc_ref(v_lctx_53_);
v___x_55_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_55_, 0, v_env_50_);
lean_ctor_set(v___x_55_, 1, v_mctx_52_);
lean_ctor_set(v___x_55_, 2, v_lctx_53_);
lean_ctor_set(v___x_55_, 3, v_options_54_);
v___x_56_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v_msgData_43_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1___boxed(lean_object* v_msgData_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(v_msgData_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_64_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(lean_object* v_opts_65_, lean_object* v_opt_66_){
_start:
{
lean_object* v_name_67_; lean_object* v_defValue_68_; lean_object* v_map_69_; lean_object* v___x_70_; 
v_name_67_ = lean_ctor_get(v_opt_66_, 0);
v_defValue_68_ = lean_ctor_get(v_opt_66_, 1);
v_map_69_ = lean_ctor_get(v_opts_65_, 0);
v___x_70_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_69_, v_name_67_);
if (lean_obj_tag(v___x_70_) == 0)
{
uint8_t v___x_71_; 
v___x_71_ = lean_unbox(v_defValue_68_);
return v___x_71_;
}
else
{
lean_object* v_val_72_; 
v_val_72_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_val_72_);
lean_dec_ref(v___x_70_);
if (lean_obj_tag(v_val_72_) == 1)
{
uint8_t v_v_73_; 
v_v_73_ = lean_ctor_get_uint8(v_val_72_, 0);
lean_dec_ref(v_val_72_);
return v_v_73_;
}
else
{
uint8_t v___x_74_; 
lean_dec(v_val_72_);
v___x_74_ = lean_unbox(v_defValue_68_);
return v___x_74_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_75_, lean_object* v_opt_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(v_opts_75_, v_opt_76_);
lean_dec_ref(v_opt_76_);
lean_dec_ref(v_opts_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_box(1);
v___x_80_ = l_Lean_MessageData_ofFormat(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2));
v___x_85_ = l_Lean_MessageData_ofFormat(v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
return v_x_86_;
}
else
{
lean_object* v_head_88_; lean_object* v_tail_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_111_; 
v_head_88_ = lean_ctor_get(v_x_87_, 0);
v_tail_89_ = lean_ctor_get(v_x_87_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_111_ == 0)
{
v___x_91_ = v_x_87_;
v_isShared_92_ = v_isSharedCheck_111_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_tail_89_);
lean_inc(v_head_88_);
lean_dec(v_x_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_111_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_before_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_109_; 
v_before_93_ = lean_ctor_get(v_head_88_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v_head_88_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v_head_88_, 1);
lean_dec(v_unused_110_);
v___x_95_ = v_head_88_;
v_isShared_96_ = v_isSharedCheck_109_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_before_93_);
lean_dec(v_head_88_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_109_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 7);
lean_ctor_set(v___x_95_, 1, v___x_97_);
lean_ctor_set(v___x_95_, 0, v_x_86_);
v___x_99_ = v___x_95_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_x_86_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v___x_97_);
v___x_99_ = v_reuseFailAlloc_108_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_92_ == 0)
{
lean_ctor_set_tag(v___x_91_, 7);
lean_ctor_set(v___x_91_, 1, v___x_100_);
lean_ctor_set(v___x_91_, 0, v___x_99_);
v___x_102_ = v___x_91_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_99_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_100_);
v___x_102_ = v_reuseFailAlloc_107_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = l_Lean_MessageData_ofSyntax(v_before_93_);
v___x_104_ = l_Lean_indentD(v___x_103_);
v___x_105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_102_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v_x_86_ = v___x_105_;
v_x_87_ = v_tail_89_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1));
v___x_116_ = l_Lean_MessageData_ofFormat(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(lean_object* v_msgData_117_, lean_object* v_macroStack_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_options_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v_options_121_ = lean_ctor_get(v___y_119_, 2);
v___x_122_ = l_Lean_Elab_pp_macroStack;
v___x_123_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(v_options_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec(v_macroStack_118_);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v_msgData_117_);
return v___x_124_;
}
else
{
if (lean_obj_tag(v_macroStack_118_) == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v_msgData_117_);
return v___x_125_;
}
else
{
lean_object* v_head_126_; lean_object* v_after_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_142_; 
v_head_126_ = lean_ctor_get(v_macroStack_118_, 0);
lean_inc(v_head_126_);
v_after_127_ = lean_ctor_get(v_head_126_, 1);
v_isSharedCheck_142_ = !lean_is_exclusive(v_head_126_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_head_126_, 0);
lean_dec(v_unused_143_);
v___x_129_ = v_head_126_;
v_isShared_130_ = v_isSharedCheck_142_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_after_127_);
lean_dec(v_head_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_142_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 7);
lean_ctor_set(v___x_129_, 1, v___x_131_);
lean_ctor_set(v___x_129_, 0, v_msgData_117_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_msgData_117_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_141_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_msgData_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_134_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2);
v___x_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = l_Lean_MessageData_ofSyntax(v_after_127_);
v___x_137_ = l_Lean_indentD(v___x_136_);
v_msgData_138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_138_, 0, v___x_135_);
lean_ctor_set(v_msgData_138_, 1, v___x_137_);
v___x_139_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(v_msgData_138_, v_macroStack_118_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_144_, lean_object* v_macroStack_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_msgData_144_, v_macroStack_145_, v___y_146_);
lean_dec_ref(v___y_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(lean_object* v_msg_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_ref_157_; lean_object* v___x_158_; lean_object* v_a_159_; lean_object* v_macroStack_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_171_; 
v_ref_157_ = lean_ctor_get(v___y_154_, 5);
v___x_158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(v_msg_149_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref(v___x_158_);
v_macroStack_160_ = lean_ctor_get(v___y_150_, 1);
v___x_161_ = l_Lean_Elab_getBetterRef(v_ref_157_, v_macroStack_160_);
lean_inc(v_macroStack_160_);
v___x_162_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_a_159_, v_macroStack_160_, v___y_154_);
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_171_ == 0)
{
v___x_165_ = v___x_162_;
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_162_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_171_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_161_);
lean_ctor_set(v___x_167_, 1, v_a_163_);
if (v_isShared_166_ == 0)
{
lean_ctor_set_tag(v___x_165_, 1);
lean_ctor_set(v___x_165_, 0, v___x_167_);
v___x_169_ = v___x_165_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg___boxed(lean_object* v_msg_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v_msg_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_180_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__3(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_box(0);
v___x_187_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__2));
v___x_188_ = l_Lean_Expr_const___override(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__6(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_box(0);
v___x_193_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__5));
v___x_194_ = l_Lean_Expr_const___override(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__9(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__8));
v___x_199_ = l_Lean_MessageData_ofFormat(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__11(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__10));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__13(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__12));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__15(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__14));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__17(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__16));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__19(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__18));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object* v___x_215_, lean_object* v___x_216_, uint8_t v___x_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Elab_Term_elabTermAndSynthesize(v___x_215_, v___x_216_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref(v___x_225_);
v___x_227_ = l_Lean_Expr_getAppFn(v_a_226_);
if (lean_obj_tag(v___x_227_) == 4)
{
lean_object* v_declName_228_; lean_object* v___x_229_; uint8_t v___y_296_; lean_object* v_env_303_; uint8_t v___x_304_; 
v_declName_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc_n(v_declName_228_, 2);
lean_dec_ref(v___x_227_);
v___x_229_ = lean_st_ref_get(v___y_223_);
v_env_303_ = lean_ctor_get(v___x_229_, 0);
lean_inc_ref_n(v_env_303_, 2);
lean_dec(v___x_229_);
v___x_304_ = l_Lean_isExtern(v_env_303_, v_declName_228_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_inc(v_declName_228_);
v___x_305_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_303_, v_declName_228_);
if (lean_obj_tag(v___x_305_) == 0)
{
v___y_296_ = v___x_304_;
goto v___jp_295_;
}
else
{
lean_dec_ref(v___x_305_);
v___y_296_ = v___x_217_;
goto v___jp_295_;
}
}
else
{
lean_dec_ref(v_env_303_);
goto v___jp_230_;
}
v___jp_230_:
{
lean_object* v___x_231_; 
lean_inc(v_a_226_);
v___x_231_ = l_Lean_Meta_unfold(v_a_226_, v_declName_228_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v_expr_233_; lean_object* v___x_234_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref(v___x_231_);
v_expr_233_ = lean_ctor_get(v_a_232_, 0);
lean_inc_ref_n(v_expr_233_, 2);
lean_dec(v_a_232_);
lean_inc(v_a_226_);
v___x_234_ = l_Lean_Meta_mkEq(v_a_226_, v_expr_233_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_236_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref(v___x_234_);
v___x_236_ = l_Lean_Meta_mkDecide(v_a_235_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_236_);
v___x_238_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__3, &l_elabTestExtern___lam__0___closed__3_once, _init_l_elabTestExtern___lam__0___closed__3);
v___x_239_ = l_Lean_Expr_app___override(v___x_238_, v_a_237_);
v___x_240_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__6, &l_elabTestExtern___lam__0___closed__6_once, _init_l_elabTestExtern___lam__0___closed__6);
v___x_241_ = 1;
v___x_242_ = l_Lean_Meta_evalExpr___redArg(v___x_240_, v___x_239_, v___x_241_, v___x_217_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_262_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_262_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_262_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_262_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
uint8_t v___x_247_; 
v___x_247_ = lean_unbox(v_a_243_);
lean_dec(v_a_243_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_del_object(v___x_245_);
v___x_248_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__9, &l_elabTestExtern___lam__0___closed__9_once, _init_l_elabTestExtern___lam__0___closed__9);
v___x_249_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__11, &l_elabTestExtern___lam__0___closed__11_once, _init_l_elabTestExtern___lam__0___closed__11);
v___x_250_ = l_Lean_MessageData_ofExpr(v_a_226_);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__13, &l_elabTestExtern___lam__0___closed__13_once, _init_l_elabTestExtern___lam__0___closed__13);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = l_Lean_MessageData_ofExpr(v_expr_233_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_248_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v___x_256_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec_ref(v_expr_233_);
lean_dec(v_a_226_);
v___x_258_ = lean_box(0);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_258_);
v___x_260_ = v___x_245_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec_ref(v_expr_233_);
lean_dec(v_a_226_);
v_a_263_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_242_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_242_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_dec_ref(v_expr_233_);
lean_dec(v_a_226_);
v_a_271_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_236_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_236_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec_ref(v_expr_233_);
lean_dec(v_a_226_);
v_a_279_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_234_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_234_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec(v_a_226_);
v_a_287_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_231_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_231_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
v___jp_295_:
{
if (v___y_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v_a_226_);
v___x_297_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__15, &l_elabTestExtern___lam__0___closed__15_once, _init_l_elabTestExtern___lam__0___closed__15);
v___x_298_ = l_Lean_MessageData_ofName(v_declName_228_);
v___x_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__17, &l_elabTestExtern___lam__0___closed__17_once, _init_l_elabTestExtern___lam__0___closed__17);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v___x_301_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_302_;
}
else
{
goto v___jp_230_;
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref(v___x_227_);
lean_dec(v_a_226_);
v___x_306_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__19, &l_elabTestExtern___lam__0___closed__19_once, _init_l_elabTestExtern___lam__0___closed__19);
v___x_307_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v___x_306_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_307_;
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_a_308_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_225_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_225_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object* v___x_316_, lean_object* v___x_317_, lean_object* v___x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
uint8_t v___x_5035__boxed_326_; lean_object* v_res_327_; 
v___x_5035__boxed_326_ = lean_unbox(v___x_318_);
v_res_327_ = l_elabTestExtern___lam__0(v___x_316_, v___x_317_, v___x_5035__boxed_326_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object* v_x_328_, lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l_testExternCmd___closed__1));
lean_inc(v_x_328_);
v___x_333_ = l_Lean_Syntax_isOfKind(v_x_328_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
lean_dec(v_x_328_);
v___x_334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___f_339_; lean_object* v___x_340_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = l_Lean_Syntax_getArg(v_x_328_, v___x_335_);
lean_dec(v_x_328_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_box(v___x_333_);
v___f_339_ = lean_alloc_closure((void*)(l_elabTestExtern___lam__0___boxed), 10, 3);
lean_closure_set(v___f_339_, 0, v___x_336_);
lean_closure_set(v___f_339_, 1, v___x_337_);
lean_closure_set(v___f_339_, 2, v___x_338_);
v___x_340_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_339_, v_a_329_, v_a_330_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object* v_x_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_elabTestExtern(v_x_341_, v_a_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1(lean_object* v_00_u03b1_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___boxed(lean_object* v_00_u03b1_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_throwError___at___00elabTestExtern_spec__1(v_00_u03b1_356_, v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(lean_object* v_msgData_366_, lean_object* v_macroStack_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_msgData_366_, v_macroStack_367_, v___y_372_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___boxed(lean_object* v_msgData_376_, lean_object* v_macroStack_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(v_msgData_376_, v_macroStack_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_385_;
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
