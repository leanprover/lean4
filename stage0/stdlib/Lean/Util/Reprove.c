// Lean compiler output
// Module: Lean.Util.Reprove
// Imports: public meta import Lean.Elab.Command public import Init.Notation import Lean.Exception
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_addAndCompile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_reproveDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reprove_example"};
static const lean_object* l_Lean_Elab_Command_reproveDecl___closed__0 = (const lean_object*)&l_Lean_Elab_Command_reproveDecl___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_reproveDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_reproveDecl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(4, 17, 150, 111, 232, 223, 228, 151)}};
static const lean_object* l_Lean_Elab_Command_reproveDecl___closed__1 = (const lean_object*)&l_Lean_Elab_Command_reproveDecl___closed__1_value;
static const lean_closure_object l_Lean_Elab_Command_reproveDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_mkFreshUserName___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reproveDecl___closed__1_value)} };
static const lean_object* l_Lean_Elab_Command_reproveDecl___closed__2 = (const lean_object*)&l_Lean_Elab_Command_reproveDecl___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_reproveDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unknown declaration '"};
static const lean_object* l_Lean_Elab_Command_reproveDecl___closed__3 = (const lean_object*)&l_Lean_Elab_Command_reproveDecl___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Command_reproveDecl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_reproveDecl___closed__4;
static const lean_string_object l_Lean_Elab_Command_reproveDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_Command_reproveDecl___closed__5 = (const lean_object*)&l_Lean_Elab_Command_reproveDecl___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Command_reproveDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_reproveDecl___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_reprove___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Command_reprove___closed__0 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Command_reprove___closed__1 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Command_reprove___closed__2 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__2_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reprove"};
static const lean_object* l_Lean_Elab_Command_reprove___closed__3 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_reprove___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Command_reprove___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Command_reprove___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Command_reprove___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 205, 199, 204, 102, 230, 156, 30)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__4 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__4_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Elab_Command_reprove___closed__5 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_reprove___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__6 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__6_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "reprove "};
static const lean_object* l_Lean_Elab_Command_reprove___closed__7 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__7_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__8 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__8_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Elab_Command_reprove___closed__9 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_reprove___closed__9_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__10 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__10_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Command_reprove___closed__11 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_reprove___closed__11_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__12 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__12_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__13 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__10_value),((lean_object*)&l_Lean_Elab_Command_reprove___closed__13_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__14 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__6_value),((lean_object*)&l_Lean_Elab_Command_reprove___closed__8_value),((lean_object*)&l_Lean_Elab_Command_reprove___closed__14_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__15 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__15_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " by "};
static const lean_object* l_Lean_Elab_Command_reprove___closed__16 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__16_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__17 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__6_value),((lean_object*)&l_Lean_Elab_Command_reprove___closed__15_value),((lean_object*)&l_Lean_Elab_Command_reprove___closed__17_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__18 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__18_value;
static const lean_string_object l_Lean_Elab_Command_reprove___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Command_reprove___closed__19 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_reprove___closed__19_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__20 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__20_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__21 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__6_value),((lean_object*)&l_Lean_Elab_Command_reprove___closed__18_value),((lean_object*)&l_Lean_Elab_Command_reprove___closed__21_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__22 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Command_reprove___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Command_reprove___closed__4_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_reprove___closed__22_value)}};
static const lean_object* l_Lean_Elab_Command_reprove___closed__23 = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__23_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Command_reprove = (const lean_object*)&l_Lean_Elab_Command_reprove___closed__23_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReprove(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReprove___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(v_e_30_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl___lam__0(lean_object* v___x_48_, uint8_t v___x_49_, lean_object* v___x_50_, lean_object* v_tacticSeq_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Meta_mkFreshExprMVar(v___x_48_, v___x_49_, v___x_50_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_a_60_);
lean_dec_ref(v___x_59_);
v___x_61_ = l_Lean_Expr_mvarId_x21(v_a_60_);
v___x_62_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_62_, 0, v_tacticSeq_51_);
v___x_63_ = l_Lean_Elab_Tactic_run(v___x_61_, v___x_62_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_64_; 
lean_dec_ref(v___x_63_);
v___x_64_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(v_a_60_, v___y_55_);
return v___x_64_;
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
lean_dec(v_a_60_);
v_a_65_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_63_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
else
{
lean_dec(v_tacticSeq_51_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl___lam__0___boxed(lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v___x_75_, lean_object* v_tacticSeq_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
uint8_t v___x_2579__boxed_84_; lean_object* v_res_85_; 
v___x_2579__boxed_84_ = lean_unbox(v___x_74_);
v_res_85_ = l_Lean_Elab_Command_reproveDecl___lam__0(v___x_73_, v___x_2579__boxed_84_, v___x_75_, v_tacticSeq_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_85_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_86_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1);
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
lean_ctor_set(v___x_91_, 3, v___x_90_);
lean_ctor_set(v___x_91_, 4, v___x_89_);
lean_ctor_set(v___x_91_, 5, v___x_89_);
lean_ctor_set(v___x_91_, 6, v___x_89_);
lean_ctor_set(v___x_91_, 7, v___x_89_);
lean_ctor_set(v___x_91_, 8, v___x_89_);
lean_ctor_set(v___x_91_, 9, v___x_89_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_unsigned_to_nat(32u);
v___x_93_ = lean_mk_empty_array_with_capacity(v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_95_ = ((size_t)5ULL);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_unsigned_to_nat(32u);
v___x_98_ = lean_mk_empty_array_with_capacity(v___x_97_);
v___x_99_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3);
v___x_100_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_96_);
lean_ctor_set(v___x_100_, 3, v___x_96_);
lean_ctor_set_usize(v___x_100_, 4, v___x_95_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = lean_box(1);
v___x_102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4);
v___x_103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_101_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(lean_object* v_msgData_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_env_109_; lean_object* v___x_110_; lean_object* v_scopes_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v_opts_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_108_ = lean_st_ref_get(v___y_106_);
v_env_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_env_109_);
lean_dec(v___x_108_);
v___x_110_ = lean_st_ref_get(v___y_106_);
v_scopes_111_ = lean_ctor_get(v___x_110_, 2);
lean_inc(v_scopes_111_);
lean_dec(v___x_110_);
v___x_112_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_113_ = l_List_head_x21___redArg(v___x_112_, v_scopes_111_);
lean_dec(v_scopes_111_);
v_opts_114_ = lean_ctor_get(v___x_113_, 1);
lean_inc_ref(v_opts_114_);
lean_dec(v___x_113_);
v___x_115_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2);
v___x_116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5);
v___x_117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_117_, 0, v_env_109_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_116_);
lean_ctor_set(v___x_117_, 3, v_opts_114_);
v___x_118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_msgData_105_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msgData_120_, v___y_121_);
lean_dec(v___y_121_);
return v_res_123_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_box(1);
v___x_125_ = l_Lean_MessageData_ofFormat(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2));
v___x_130_ = l_Lean_MessageData_ofFormat(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4(lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
return v_x_131_;
}
else
{
lean_object* v_head_133_; lean_object* v_tail_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_156_; 
v_head_133_ = lean_ctor_get(v_x_132_, 0);
v_tail_134_ = lean_ctor_get(v_x_132_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_156_ == 0)
{
v___x_136_ = v_x_132_;
v_isShared_137_ = v_isSharedCheck_156_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_tail_134_);
lean_inc(v_head_133_);
lean_dec(v_x_132_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_156_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v_before_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_154_; 
v_before_138_ = lean_ctor_get(v_head_133_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_head_133_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; 
v_unused_155_ = lean_ctor_get(v_head_133_, 1);
lean_dec(v_unused_155_);
v___x_140_ = v_head_133_;
v_isShared_141_ = v_isSharedCheck_154_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_before_138_);
lean_dec(v_head_133_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_154_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 7);
lean_ctor_set(v___x_140_, 1, v___x_142_);
lean_ctor_set(v___x_140_, 0, v_x_131_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_x_131_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_153_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_137_ == 0)
{
lean_ctor_set_tag(v___x_136_, 7);
lean_ctor_set(v___x_136_, 1, v___x_145_);
lean_ctor_set(v___x_136_, 0, v___x_144_);
v___x_147_ = v___x_136_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_152_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = l_Lean_MessageData_ofSyntax(v_before_138_);
v___x_149_ = l_Lean_indentD(v___x_148_);
v___x_150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_147_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v_x_131_ = v___x_150_;
v_x_132_ = v_tail_134_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(lean_object* v_opts_157_, lean_object* v_opt_158_){
_start:
{
lean_object* v_name_159_; lean_object* v_defValue_160_; lean_object* v_map_161_; lean_object* v___x_162_; 
v_name_159_ = lean_ctor_get(v_opt_158_, 0);
v_defValue_160_ = lean_ctor_get(v_opt_158_, 1);
v_map_161_ = lean_ctor_get(v_opts_157_, 0);
v___x_162_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_161_, v_name_159_);
if (lean_obj_tag(v___x_162_) == 0)
{
uint8_t v___x_163_; 
v___x_163_ = lean_unbox(v_defValue_160_);
return v___x_163_;
}
else
{
lean_object* v_val_164_; 
v_val_164_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_val_164_);
lean_dec_ref(v___x_162_);
if (lean_obj_tag(v_val_164_) == 1)
{
uint8_t v_v_165_; 
v_v_165_ = lean_ctor_get_uint8(v_val_164_, 0);
lean_dec_ref(v_val_164_);
return v_v_165_;
}
else
{
uint8_t v___x_166_; 
lean_dec(v_val_164_);
v___x_166_ = lean_unbox(v_defValue_160_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_167_, lean_object* v_opt_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(v_opts_167_, v_opt_168_);
lean_dec_ref(v_opt_168_);
lean_dec_ref(v_opts_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1));
v___x_175_ = l_Lean_MessageData_ofFormat(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(lean_object* v_msgData_176_, lean_object* v_macroStack_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; lean_object* v_scopes_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_opts_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_180_ = lean_st_ref_get(v___y_178_);
v_scopes_181_ = lean_ctor_get(v___x_180_, 2);
lean_inc(v_scopes_181_);
lean_dec(v___x_180_);
v___x_182_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_183_ = l_List_head_x21___redArg(v___x_182_, v_scopes_181_);
lean_dec(v_scopes_181_);
v_opts_184_ = lean_ctor_get(v___x_183_, 1);
lean_inc_ref(v_opts_184_);
lean_dec(v___x_183_);
v___x_185_ = l_Lean_Elab_pp_macroStack;
v___x_186_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(v_opts_184_, v___x_185_);
lean_dec_ref(v_opts_184_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; 
lean_dec(v_macroStack_177_);
v___x_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_187_, 0, v_msgData_176_);
return v___x_187_;
}
else
{
if (lean_obj_tag(v_macroStack_177_) == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_msgData_176_);
return v___x_188_;
}
else
{
lean_object* v_head_189_; lean_object* v_after_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_205_; 
v_head_189_ = lean_ctor_get(v_macroStack_177_, 0);
lean_inc(v_head_189_);
v_after_190_ = lean_ctor_get(v_head_189_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_head_189_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_head_189_, 0);
lean_dec(v_unused_206_);
v___x_192_ = v_head_189_;
v_isShared_193_ = v_isSharedCheck_205_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_after_190_);
lean_dec(v_head_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_205_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 7);
lean_ctor_set(v___x_192_, 1, v___x_194_);
lean_ctor_set(v___x_192_, 0, v_msgData_176_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_msgData_176_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_194_);
v___x_196_ = v_reuseFailAlloc_204_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_msgData_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_197_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2);
v___x_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = l_Lean_MessageData_ofSyntax(v_after_190_);
v___x_200_ = l_Lean_indentD(v___x_199_);
v_msgData_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_201_, 0, v___x_198_);
lean_ctor_set(v_msgData_201_, 1, v___x_200_);
v___x_202_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4(v_msgData_201_, v_macroStack_177_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_207_, lean_object* v_macroStack_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_msgData_207_, v_macroStack_208_, v___y_209_);
lean_dec(v___y_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Elab_Command_getRef___redArg(v___y_213_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v_macroStack_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref(v___x_216_);
v_macroStack_218_ = lean_ctor_get(v___y_213_, 4);
v___x_219_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msg_212_, v___y_214_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_a_220_);
lean_dec_ref(v___x_219_);
lean_inc_n(v_macroStack_218_, 2);
v___x_221_ = l_Lean_Elab_getBetterRef(v_a_217_, v_macroStack_218_);
lean_dec(v_a_217_);
v___x_222_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_a_220_, v_macroStack_218_, v___y_214_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_221_);
lean_ctor_set(v___x_227_, 1, v_a_223_);
if (v_isShared_226_ == 0)
{
lean_ctor_set_tag(v___x_225_, 1);
lean_ctor_set(v___x_225_, 0, v___x_227_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec_ref(v_msg_212_);
v_a_232_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_216_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_216_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg___boxed(lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(v_msg_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_244_;
}
}
static lean_object* _init_l_Lean_Elab_Command_reproveDecl___closed__4(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Command_reproveDecl___closed__3));
v___x_252_ = l_Lean_stringToMessageData(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Elab_Command_reproveDecl___closed__6(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_Elab_Command_reproveDecl___closed__5));
v___x_255_ = l_Lean_stringToMessageData(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl(lean_object* v_declName_256_, lean_object* v_tacticSeq_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___x_261_; lean_object* v_env_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_st_ref_get(v_a_259_);
v_env_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc_ref(v_env_262_);
lean_dec(v___x_261_);
v___x_263_ = 0;
lean_inc(v_declName_256_);
v___x_264_ = l_Lean_Environment_find_x3f(v_env_262_, v_declName_256_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 1)
{
lean_object* v_val_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_declName_256_);
v_val_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_312_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_312_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_val_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_312_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Elab_Command_reproveDecl___closed__2));
v___x_270_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_269_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v___x_270_);
v___x_272_ = l_Lean_ConstantInfo_type(v_val_265_);
lean_inc_ref(v___x_272_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_272_);
v___x_274_ = v___x_267_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_303_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_275_ = 0;
v___x_276_ = lean_box(0);
v___x_277_ = lean_box(v___x_275_);
v___f_278_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_reproveDecl___lam__0___boxed), 11, 4);
lean_closure_set(v___f_278_, 0, v___x_274_);
lean_closure_set(v___f_278_, 1, v___x_277_);
lean_closure_set(v___f_278_, 2, v___x_276_);
lean_closure_set(v___f_278_, 3, v_tacticSeq_257_);
lean_inc(v_a_271_);
v___x_279_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_279_, 0, lean_box(0));
lean_closure_set(v___x_279_, 1, v_a_271_);
lean_closure_set(v___x_279_, 2, v___f_278_);
v___x_280_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_279_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref(v___x_280_);
v___x_282_ = l_Lean_ConstantInfo_levelParams(v_val_265_);
lean_dec(v_val_265_);
lean_inc(v_a_271_);
v___x_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_283_, 0, v_a_271_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
lean_ctor_set(v___x_283_, 2, v___x_272_);
v___x_284_ = lean_box(0);
v___x_285_ = 1;
v___x_286_ = lean_box(0);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v_a_271_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_288_, 0, v___x_283_);
lean_ctor_set(v___x_288_, 1, v_a_281_);
lean_ctor_set(v___x_288_, 2, v___x_284_);
lean_ctor_set(v___x_288_, 3, v___x_287_);
lean_ctor_set_uint8(v___x_288_, sizeof(void*)*4, v___x_285_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = 1;
v___x_291_ = lean_box(v___x_290_);
v___x_292_ = lean_box(v___x_263_);
v___x_293_ = lean_alloc_closure((void*)(l_Lean_addAndCompile___boxed), 6, 3);
lean_closure_set(v___x_293_, 0, v___x_289_);
lean_closure_set(v___x_293_, 1, v___x_291_);
lean_closure_set(v___x_293_, 2, v___x_292_);
v___x_294_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_293_, v_a_258_, v_a_259_);
return v___x_294_;
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v___x_272_);
lean_dec(v_a_271_);
lean_dec(v_val_265_);
v_a_295_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_280_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_280_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_del_object(v___x_267_);
lean_dec(v_val_265_);
lean_dec(v_tacticSeq_257_);
v_a_304_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_270_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_270_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v___x_264_);
lean_dec(v_tacticSeq_257_);
v___x_313_ = lean_obj_once(&l_Lean_Elab_Command_reproveDecl___closed__4, &l_Lean_Elab_Command_reproveDecl___closed__4_once, _init_l_Lean_Elab_Command_reproveDecl___closed__4);
v___x_314_ = l_Lean_MessageData_ofName(v_declName_256_);
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_obj_once(&l_Lean_Elab_Command_reproveDecl___closed__6, &l_Lean_Elab_Command_reproveDecl___closed__6_once, _init_l_Lean_Elab_Command_reproveDecl___closed__6);
v___x_317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(v___x_317_, v_a_258_, v_a_259_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl___boxed(lean_object* v_declName_319_, lean_object* v_tacticSeq_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Elab_Command_reproveDecl(v_declName_319_, v_tacticSeq_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1(lean_object* v_msgData_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msgData_325_, v___y_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___boxed(lean_object* v_msgData_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1(v_msgData_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1(lean_object* v_00_u03b1_335_, lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(v_msg_336_, v___y_337_, v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___boxed(lean_object* v_00_u03b1_341_, lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1(v_00_u03b1_341_, v_msg_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2(lean_object* v_msgData_347_, lean_object* v_macroStack_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_msgData_347_, v_macroStack_348_, v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___boxed(lean_object* v_msgData_353_, lean_object* v_macroStack_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2(v_msgData_353_, v_macroStack_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(lean_object* v_tacticSeq_410_, lean_object* v_as_411_, size_t v_sz_412_, size_t v_i_413_, lean_object* v_b_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_lt(v_i_413_, v_sz_412_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v_tacticSeq_410_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_b_414_);
return v___x_419_;
}
else
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_a_420_ = lean_array_uget_borrowed(v_as_411_, v_i_413_);
v___x_421_ = lean_box(0);
lean_inc(v_a_420_);
v___x_422_ = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed), 5, 2);
lean_closure_set(v___x_422_, 0, v_a_420_);
lean_closure_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_422_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref(v___x_423_);
lean_inc(v_tacticSeq_410_);
v___x_425_ = l_Lean_Elab_Command_reproveDecl(v_a_424_, v_tacticSeq_410_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v___x_426_; size_t v___x_427_; size_t v___x_428_; 
lean_dec_ref(v___x_425_);
v___x_426_ = lean_box(0);
v___x_427_ = ((size_t)1ULL);
v___x_428_ = lean_usize_add(v_i_413_, v___x_427_);
v_i_413_ = v___x_428_;
v_b_414_ = v___x_426_;
goto _start;
}
else
{
lean_dec(v_tacticSeq_410_);
return v___x_425_;
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_tacticSeq_410_);
v_a_430_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_423_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_423_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0___boxed(lean_object* v_tacticSeq_438_, lean_object* v_as_439_, lean_object* v_sz_440_, lean_object* v_i_441_, lean_object* v_b_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
size_t v_sz_boxed_446_; size_t v_i_boxed_447_; lean_object* v_res_448_; 
v_sz_boxed_446_ = lean_unbox_usize(v_sz_440_);
lean_dec(v_sz_440_);
v_i_boxed_447_ = lean_unbox_usize(v_i_441_);
lean_dec(v_i_441_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(v_tacticSeq_438_, v_as_439_, v_sz_boxed_446_, v_i_boxed_447_, v_b_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec_ref(v_as_439_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReprove(lean_object* v_stx_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_identStxs_455_; lean_object* v___x_456_; lean_object* v_tacticSeq_457_; lean_object* v___x_458_; size_t v_sz_459_; size_t v___x_460_; lean_object* v___x_461_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = l_Lean_Syntax_getArg(v_stx_449_, v___x_453_);
v_identStxs_455_ = l_Lean_Syntax_getArgs(v___x_454_);
lean_dec(v___x_454_);
v___x_456_ = lean_unsigned_to_nat(3u);
v_tacticSeq_457_ = l_Lean_Syntax_getArg(v_stx_449_, v___x_456_);
v___x_458_ = lean_box(0);
v_sz_459_ = lean_array_size(v_identStxs_455_);
v___x_460_ = ((size_t)0ULL);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(v_tacticSeq_457_, v_identStxs_455_, v_sz_459_, v___x_460_, v___x_458_, v_a_450_, v_a_451_);
lean_dec_ref(v_identStxs_455_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_468_ == 0)
{
lean_object* v_unused_469_; 
v_unused_469_ = lean_ctor_get(v___x_461_, 0);
lean_dec(v_unused_469_);
v___x_463_ = v___x_461_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_dec(v___x_461_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_458_);
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_458_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReprove___boxed(lean_object* v_stx_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_Command_elabReprove(v_stx_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_stx_470_);
return v_res_474_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Reprove(uint8_t builtin) {
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
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Reprove(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
lean_object* initialize_Lean_Exception(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Reprove(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Reprove(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Reprove(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Reprove(builtin);
}
#ifdef __cplusplus
}
#endif
