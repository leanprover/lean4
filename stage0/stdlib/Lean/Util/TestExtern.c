// Lean compiler output
// Module: Lean.Util.TestExtern
// Imports: public meta import Lean.Meta.Tactic.Unfold public meta import Lean.Meta.Eval public meta import Lean.Compiler.ImplementedByAttr public meta import Lean.Elab.Command
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
static const lean_string_object l_testExternCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "testExternCmd"};
static const lean_object* l_testExternCmd___closed__0 = (const lean_object*)&l_testExternCmd___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2_value;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1_value;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_elabTestExtern___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_elabTestExtern___lam__0___closed__0 = (const lean_object*)&l_elabTestExtern___lam__0___closed__0_value;
static const lean_string_object l_elabTestExtern___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "reduceBool"};
static const lean_object* l_elabTestExtern___lam__0___closed__1 = (const lean_object*)&l_elabTestExtern___lam__0___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_elabTestExtern___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_elabTestExtern___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_elabTestExtern___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_elabTestExtern___lam__0___closed__2_value_aux_0),((lean_object*)&l_elabTestExtern___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(114, 197, 237, 28, 99, 199, 232, 30)}};
static const lean_object* l_elabTestExtern___lam__0___closed__2 = (const lean_object*)&l_elabTestExtern___lam__0___closed__2_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__3;
static const lean_string_object l_elabTestExtern___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_elabTestExtern___lam__0___closed__4 = (const lean_object*)&l_elabTestExtern___lam__0___closed__4_value;
static const lean_ctor_object l_elabTestExtern___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_elabTestExtern___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_elabTestExtern___lam__0___closed__5 = (const lean_object*)&l_elabTestExtern___lam__0___closed__5_value;
static lean_object* l_elabTestExtern___lam__0___closed__6;
static const lean_string_object l_elabTestExtern___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "native implementation did not agree with reference implementation!\n"};
static const lean_object* l_elabTestExtern___lam__0___closed__7 = (const lean_object*)&l_elabTestExtern___lam__0___closed__7_value;
static const lean_ctor_object l_elabTestExtern___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_elabTestExtern___lam__0___closed__7_value)}};
static const lean_object* l_elabTestExtern___lam__0___closed__8 = (const lean_object*)&l_elabTestExtern___lam__0___closed__8_value;
static lean_object* l_elabTestExtern___lam__0___closed__9;
static const lean_string_object l_elabTestExtern___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Compare the outputs of:\n#eval "};
static const lean_object* l_elabTestExtern___lam__0___closed__10 = (const lean_object*)&l_elabTestExtern___lam__0___closed__10_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_elabTestExtern___lam__0___closed__11;
static const lean_string_object l_elabTestExtern___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\n and\n#eval "};
static const lean_object* l_elabTestExtern___lam__0___closed__12 = (const lean_object*)&l_elabTestExtern___lam__0___closed__12_value;
static lean_object* l_elabTestExtern___lam__0___closed__13;
static const lean_string_object l_elabTestExtern___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "test_extern: "};
static const lean_object* l_elabTestExtern___lam__0___closed__14 = (const lean_object*)&l_elabTestExtern___lam__0___closed__14_value;
static lean_object* l_elabTestExtern___lam__0___closed__15;
static const lean_string_object l_elabTestExtern___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = " does not have an @[extern] attribute or @[implemented_by] attribute"};
static const lean_object* l_elabTestExtern___lam__0___closed__16 = (const lean_object*)&l_elabTestExtern___lam__0___closed__16_value;
static lean_object* l_elabTestExtern___lam__0___closed__17;
static const lean_string_object l_elabTestExtern___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "test_extern: expects a function application"};
static const lean_object* l_elabTestExtern___lam__0___closed__18 = (const lean_object*)&l_elabTestExtern___lam__0___closed__18_value;
static lean_object* l_elabTestExtern___lam__0___closed__19;
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
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0;
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_1);
x_10 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_7);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
x_20 = l_Lean_MessageData_ofSyntax(x_16);
x_21 = l_Lean_indentD(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0;
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(7, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 7);
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofSyntax(x_26);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_1 = x_34;
x_2 = x_25;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__3(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_1);
x_15 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofSyntax(x_12);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(x_19, x_2);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofSyntax(x_22);
x_28 = l_Lean_indentD(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4(x_29, x_2);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__1(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(x_11, x_12, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_elabTestExtern___lam__0___closed__2));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_elabTestExtern___lam__0___closed__5));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_elabTestExtern___lam__0___closed__8));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_elabTestExtern___lam__0___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_elabTestExtern___lam__0___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_elabTestExtern___lam__0___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_elabTestExtern___lam__0___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_elabTestExtern___lam__0___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_elabTestExtern___lam__0___closed__18));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_11 = l_Lean_Elab_Term_elabTermAndSynthesize(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; uint8_t x_69; lean_object* x_77; uint8_t x_78; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_st_ref_get(x_9);
x_77 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_77);
lean_dec(x_15);
lean_inc(x_14);
lean_inc_ref(x_77);
x_78 = l_Lean_isExtern(x_77, x_14);
if (x_78 == 0)
{
lean_object* x_79; 
lean_inc(x_14);
x_79 = l_Lean_Compiler_getImplementedBy_x3f(x_77, x_14);
if (lean_obj_tag(x_79) == 0)
{
x_69 = x_78;
goto block_76;
}
else
{
lean_dec_ref(x_79);
x_69 = x_3;
goto block_76;
}
}
else
{
lean_dec_ref(x_77);
goto block_68;
}
block_68:
{
lean_object* x_16; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_12);
x_16 = l_Lean_Meta_unfold(x_12, x_14, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_18);
lean_inc(x_12);
x_19 = l_Lean_Meta_mkEq(x_12, x_18, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_21 = l_Lean_Meta_mkDecide(x_20, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_elabTestExtern___lam__0___closed__3;
x_24 = l_Lean_Expr_app___override(x_23, x_22);
x_25 = l_elabTestExtern___lam__0___closed__6;
x_26 = 1;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_27 = l_Lean_Meta_evalExpr___redArg(x_25, x_24, x_26, x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_27);
x_31 = l_elabTestExtern___lam__0___closed__9;
x_32 = l_elabTestExtern___lam__0___closed__11;
x_33 = l_Lean_MessageData_ofExpr(x_12);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_elabTestExtern___lam__0___closed__13;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_MessageData_ofExpr(x_18);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(x_39, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec_ref(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_41 = lean_box(0);
lean_ctor_set(x_27, 0, x_41);
return x_27;
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_27, 0);
lean_inc(x_42);
lean_dec(x_27);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_elabTestExtern___lam__0___closed__9;
x_45 = l_elabTestExtern___lam__0___closed__11;
x_46 = l_Lean_MessageData_ofExpr(x_12);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_elabTestExtern___lam__0___closed__13;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_ofExpr(x_18);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(x_52, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_56 = !lean_is_exclusive(x_27);
if (x_56 == 0)
{
return x_27;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_27, 0);
lean_inc(x_57);
lean_dec(x_27);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_59 = !lean_is_exclusive(x_21);
if (x_59 == 0)
{
return x_21;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_21, 0);
lean_inc(x_60);
lean_dec(x_21);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec_ref(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
return x_19;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_19, 0);
lean_inc(x_63);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_65 = !lean_is_exclusive(x_16);
if (x_65 == 0)
{
return x_16;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_16, 0);
lean_inc(x_66);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
block_76:
{
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_12);
x_70 = l_elabTestExtern___lam__0___closed__15;
x_71 = l_Lean_MessageData_ofName(x_14);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_elabTestExtern___lam__0___closed__17;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(x_74, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_75;
}
else
{
goto block_68;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_13);
lean_dec(x_12);
x_80 = l_elabTestExtern___lam__0___closed__19;
x_81 = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(x_80, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_82 = !lean_is_exclusive(x_11);
if (x_82 == 0)
{
return x_11;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_11, 0);
lean_inc(x_83);
lean_dec(x_11);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_elabTestExtern___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_elabTestExtern(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l_testExternCmd___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg();
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_box(x_6);
x_12 = lean_alloc_closure((void*)(l_elabTestExtern___lam__0___boxed), 10, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_Elab_Command_liftTermElabM___redArg(x_12, x_2, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_elabTestExtern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_elabTestExtern(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00elabTestExtern_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00elabTestExtern_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00elabTestExtern_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
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
l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00elabTestExtern_spec__0___redArg___closed__0);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__0);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2_spec__4___closed__3);
l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2 = _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00elabTestExtern_spec__1_spec__2___redArg___closed__2);
l_elabTestExtern___lam__0___closed__3 = _init_l_elabTestExtern___lam__0___closed__3();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__3);
l_elabTestExtern___lam__0___closed__6 = _init_l_elabTestExtern___lam__0___closed__6();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__6);
l_elabTestExtern___lam__0___closed__9 = _init_l_elabTestExtern___lam__0___closed__9();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__9);
l_elabTestExtern___lam__0___closed__11 = _init_l_elabTestExtern___lam__0___closed__11();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__11);
l_elabTestExtern___lam__0___closed__13 = _init_l_elabTestExtern___lam__0___closed__13();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__13);
l_elabTestExtern___lam__0___closed__15 = _init_l_elabTestExtern___lam__0___closed__15();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__15);
l_elabTestExtern___lam__0___closed__17 = _init_l_elabTestExtern___lam__0___closed__17();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__17);
l_elabTestExtern___lam__0___closed__19 = _init_l_elabTestExtern___lam__0___closed__19();
lean_mark_persistent(l_elabTestExtern___lam__0___closed__19);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
