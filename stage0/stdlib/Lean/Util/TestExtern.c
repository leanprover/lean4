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
uint8_t lean_bool_not(uint8_t);
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
lean_dec_ref_known(v___x_70_, 1);
if (lean_obj_tag(v_val_72_) == 1)
{
uint8_t v_v_73_; 
v_v_73_ = lean_ctor_get_uint8(v_val_72_, 0);
lean_dec_ref_known(v_val_72_, 0);
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
lean_object* v_options_121_; lean_object* v___x_122_; uint8_t v___x_123_; uint8_t v___x_124_; 
v_options_121_ = lean_ctor_get(v___y_119_, 2);
v___x_122_ = l_Lean_Elab_pp_macroStack;
v___x_123_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(v_options_121_, v___x_122_);
v___x_124_ = lean_bool_not(v___x_123_);
if (v___x_124_ == 0)
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
else
{
lean_object* v___x_144_; 
lean_dec(v_macroStack_118_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v_msgData_117_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_145_, lean_object* v_macroStack_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_msgData_145_, v_macroStack_146_, v___y_147_);
lean_dec_ref(v___y_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(lean_object* v_msg_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_ref_158_; lean_object* v___x_159_; lean_object* v_a_160_; lean_object* v_macroStack_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_172_; 
v_ref_158_ = lean_ctor_get(v___y_155_, 5);
v___x_159_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(v_msg_150_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref(v___x_159_);
v_macroStack_161_ = lean_ctor_get(v___y_151_, 1);
v___x_162_ = l_Lean_Elab_getBetterRef(v_ref_158_, v_macroStack_161_);
lean_inc(v_macroStack_161_);
v___x_163_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_a_160_, v_macroStack_161_, v___y_155_);
v_a_164_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_172_ == 0)
{
v___x_166_ = v___x_163_;
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_162_);
lean_ctor_set(v___x_168_, 1, v_a_164_);
if (v_isShared_167_ == 0)
{
lean_ctor_set_tag(v___x_166_, 1);
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg___boxed(lean_object* v_msg_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v_msg_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_181_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__3(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_box(0);
v___x_188_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__2));
v___x_189_ = l_Lean_Expr_const___override(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__6(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__5));
v___x_195_ = l_Lean_Expr_const___override(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__9(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__8));
v___x_200_ = l_Lean_MessageData_ofFormat(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__11(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__10));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__13(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__12));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__15(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__14));
v___x_209_ = l_Lean_stringToMessageData(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__17(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__16));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__19(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l_elabTestExtern___lam__0___closed__18));
v___x_215_ = l_Lean_stringToMessageData(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object* v___x_216_, lean_object* v___x_217_, uint8_t v___x_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Elab_Term_elabTermAndSynthesize(v___x_216_, v___x_217_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_Expr_getAppFn(v_a_227_);
if (lean_obj_tag(v___x_228_) == 4)
{
lean_object* v_declName_229_; lean_object* v___x_230_; uint8_t v___y_298_; lean_object* v_env_305_; uint8_t v___x_306_; 
v_declName_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_n(v_declName_229_, 2);
lean_dec_ref_known(v___x_228_, 2);
v___x_230_ = lean_st_ref_get(v___y_224_);
v_env_305_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref_n(v_env_305_, 2);
lean_dec(v___x_230_);
v___x_306_ = l_Lean_isExtern(v_env_305_, v_declName_229_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_inc(v_declName_229_);
v___x_307_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_305_, v_declName_229_);
if (lean_obj_tag(v___x_307_) == 0)
{
v___y_298_ = v___x_306_;
goto v___jp_297_;
}
else
{
lean_dec_ref_known(v___x_307_, 1);
v___y_298_ = v___x_218_;
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v_env_305_);
goto v___jp_231_;
}
v___jp_231_:
{
lean_object* v___x_232_; 
lean_inc(v_a_227_);
v___x_232_ = l_Lean_Meta_unfold(v_a_227_, v_declName_229_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v_expr_234_; lean_object* v___x_235_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
v_expr_234_ = lean_ctor_get(v_a_233_, 0);
lean_inc_ref_n(v_expr_234_, 2);
lean_dec(v_a_233_);
lean_inc(v_a_227_);
v___x_235_ = l_Lean_Meta_mkEq(v_a_227_, v_expr_234_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_237_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = l_Lean_Meta_mkDecide(v_a_236_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__3, &l_elabTestExtern___lam__0___closed__3_once, _init_l_elabTestExtern___lam__0___closed__3);
v___x_240_ = l_Lean_Expr_app___override(v___x_239_, v_a_238_);
v___x_241_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__6, &l_elabTestExtern___lam__0___closed__6_once, _init_l_elabTestExtern___lam__0___closed__6);
v___x_242_ = 1;
v___x_243_ = l_Lean_Meta_evalExpr___redArg(v___x_241_, v___x_240_, v___x_242_, v___x_218_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_264_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_264_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_264_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_264_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_unbox(v_a_244_);
lean_dec(v_a_244_);
v___x_249_ = lean_bool_not(v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec_ref(v_expr_234_);
lean_dec(v_a_227_);
v___x_250_ = lean_box(0);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_250_);
v___x_252_ = v___x_246_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_del_object(v___x_246_);
v___x_254_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__9, &l_elabTestExtern___lam__0___closed__9_once, _init_l_elabTestExtern___lam__0___closed__9);
v___x_255_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__11, &l_elabTestExtern___lam__0___closed__11_once, _init_l_elabTestExtern___lam__0___closed__11);
v___x_256_ = l_Lean_MessageData_ofExpr(v_a_227_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__13, &l_elabTestExtern___lam__0___closed__13_once, _init_l_elabTestExtern___lam__0___closed__13);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = l_Lean_MessageData_ofExpr(v_expr_234_);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_254_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v___x_262_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
return v___x_263_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref(v_expr_234_);
lean_dec(v_a_227_);
v_a_265_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_243_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_243_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_expr_234_);
lean_dec(v_a_227_);
v_a_273_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_237_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_237_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_expr_234_);
lean_dec(v_a_227_);
v_a_281_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_235_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_235_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_a_227_);
v_a_289_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_232_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_232_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
v___jp_297_:
{
if (v___y_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec(v_a_227_);
v___x_299_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__15, &l_elabTestExtern___lam__0___closed__15_once, _init_l_elabTestExtern___lam__0___closed__15);
v___x_300_ = l_Lean_MessageData_ofName(v_declName_229_);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__17, &l_elabTestExtern___lam__0___closed__17_once, _init_l_elabTestExtern___lam__0___closed__17);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v___x_303_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
return v___x_304_;
}
else
{
goto v___jp_231_;
}
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec_ref(v___x_228_);
lean_dec(v_a_227_);
v___x_308_ = lean_obj_once(&l_elabTestExtern___lam__0___closed__19, &l_elabTestExtern___lam__0___closed__19_once, _init_l_elabTestExtern___lam__0___closed__19);
v___x_309_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v___x_308_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
return v___x_309_;
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_a_310_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_317_ == 0)
{
v___x_312_ = v___x_226_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_226_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_310_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object* v___x_318_, lean_object* v___x_319_, lean_object* v___x_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v___x_4932__boxed_328_; lean_object* v_res_329_; 
v___x_4932__boxed_328_ = lean_unbox(v___x_320_);
v_res_329_ = l_elabTestExtern___lam__0(v___x_318_, v___x_319_, v___x_4932__boxed_328_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object* v_x_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = ((lean_object*)(l_testExternCmd___closed__1));
lean_inc(v_x_330_);
v___x_335_ = l_Lean_Syntax_isOfKind(v_x_330_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v_x_330_);
v___x_336_ = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
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
v___f_341_ = lean_alloc_closure((void*)(l_elabTestExtern___lam__0___boxed), 10, 3);
lean_closure_set(v___f_341_, 0, v___x_338_);
lean_closure_set(v___f_341_, 1, v___x_339_);
lean_closure_set(v___f_341_, 2, v___x_340_);
v___x_342_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_341_, v_a_331_, v_a_332_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object* v_x_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_elabTestExtern(v_x_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1(lean_object* v_00_u03b1_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(v_msg_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___boxed(lean_object* v_00_u03b1_358_, lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_throwError___at___00elabTestExtern_spec__1(v_00_u03b1_358_, v_msg_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(lean_object* v_msgData_368_, lean_object* v_macroStack_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(v_msgData_368_, v_macroStack_369_, v___y_374_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___boxed(lean_object* v_msgData_378_, lean_object* v_macroStack_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(v_msgData_378_, v_macroStack_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_387_;
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
