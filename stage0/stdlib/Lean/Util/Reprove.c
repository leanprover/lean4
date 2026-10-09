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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(v_e_31_, v___y_35_);
return v___x_39_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v_res_40_;
v_res_40_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
stack->m_obj
 = v_res_40_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_49_;
}
}
lean_object* l_Lean_Elab_Command_reproveDecl___lam__0(lean_object* v___x_50_, uint8_t v___x_51_, lean_object* v___x_52_, lean_object* v_tacticSeq_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Meta_mkFreshExprMVar(v___x_50_, v___x_51_, v___x_52_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_62_);
lean_dec_ref_known(v___x_61_, 1);
v___x_63_ = l_Lean_Expr_mvarId_x21(v_a_62_);
v___x_64_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_64_, 0, v_tacticSeq_53_);
v___x_65_ = l_Lean_Elab_Tactic_run(v___x_63_, v___x_64_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v___x_66_; 
lean_dec_ref_known(v___x_65_, 1);
v___x_66_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(v_a_62_, v___y_57_);
return v___x_66_;
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v_a_62_);
v_a_67_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_65_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_65_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_dec(v_tacticSeq_53_);
return v___x_61_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_reproveDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_50_ = stack[0].m_obj;
uint8_t v___x_51_ = stack[1].m_num;
lean_object* v___x_52_ = stack[2].m_obj;
lean_object* v_tacticSeq_53_ = stack[3].m_obj;
lean_object* v___y_54_ = stack[4].m_obj;
lean_object* v___y_55_ = stack[5].m_obj;
lean_object* v___y_56_ = stack[6].m_obj;
lean_object* v___y_57_ = stack[7].m_obj;
lean_object* v___y_58_ = stack[8].m_obj;
lean_object* v___y_59_ = stack[9].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_Elab_Command_reproveDecl___lam__0(v___x_50_, v___x_51_, v___x_52_, v_tacticSeq_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl___lam__0___boxed(lean_object* v___x_76_, lean_object* v___x_77_, lean_object* v___x_78_, lean_object* v_tacticSeq_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
uint8_t v___x_2734__boxed_87_; lean_object* v_res_88_; 
v___x_2734__boxed_87_ = lean_unbox(v___x_77_);
v_res_88_ = l_Lean_Elab_Command_reproveDecl___lam__0(v___x_76_, v___x_2734__boxed_87_, v___x_78_, v_tacticSeq_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_88_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_89_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_93_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
lean_ctor_set(v___x_95_, 2, v___x_94_);
lean_ctor_set(v___x_95_, 3, v___x_94_);
lean_ctor_set(v___x_95_, 4, v___x_93_);
lean_ctor_set(v___x_95_, 5, v___x_93_);
lean_ctor_set(v___x_95_, 6, v___x_93_);
lean_ctor_set(v___x_95_, 7, v___x_93_);
lean_ctor_set(v___x_95_, 8, v___x_93_);
lean_ctor_set(v___x_95_, 9, v___x_93_);
lean_ctor_set(v___x_95_, 10, v___x_93_);
lean_ctor_set(v___x_95_, 11, v___x_92_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_unsigned_to_nat(32u);
v___x_97_ = lean_mk_empty_array_with_capacity(v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_99_ = ((size_t)5ULL);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_unsigned_to_nat(32u);
v___x_102_ = lean_mk_empty_array_with_capacity(v___x_101_);
v___x_103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3);
v___x_104_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_100_);
lean_ctor_set(v___x_104_, 3, v___x_100_);
lean_ctor_set_usize(v___x_104_, 4, v___x_99_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_105_ = lean_box(1);
v___x_106_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4);
v___x_107_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1);
v___x_108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_105_);
return v___x_108_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(lean_object* v_msgData_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; lean_object* v_env_113_; uint8_t v___x_114_; lean_object* v_env_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_scopes_118_; lean_object* v___x_119_; lean_object* v_opts_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_112_ = lean_st_ref_get(v___y_110_);
v_env_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc_ref(v_env_113_);
lean_dec(v___x_112_);
v___x_114_ = 0;
v_env_115_ = l_Lean_Environment_setRecordingDeps(v_env_113_, v___x_114_);
v___x_116_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_117_ = lean_st_ref_get(v___y_110_);
v_scopes_118_ = lean_ctor_get(v___x_117_, 2);
lean_inc(v_scopes_118_);
lean_dec(v___x_117_);
v___x_119_ = l_List_head_x21___redArg(v___x_116_, v_scopes_118_);
lean_dec(v_scopes_118_);
v_opts_120_ = lean_ctor_get(v___x_119_, 1);
lean_inc_ref(v_opts_120_);
lean_dec(v___x_119_);
v___x_121_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2);
v___x_122_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5);
v___x_123_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_123_, 0, v_env_115_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
lean_ctor_set(v___x_123_, 3, v_opts_120_);
v___x_124_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v_msgData_109_);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_109_ = stack[0].m_obj;
lean_object* v___y_110_ = stack[1].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msgData_109_, v___y_110_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msgData_127_, v___y_128_);
lean_dec(v___y_128_);
return v_res_130_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_box(1);
v___x_132_ = l_Lean_MessageData_ofFormat(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2));
v___x_137_ = l_Lean_MessageData_ofFormat(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
return v_x_138_;
}
else
{
lean_object* v_head_140_; lean_object* v_tail_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_163_; 
v_head_140_ = lean_ctor_get(v_x_139_, 0);
v_tail_141_ = lean_ctor_get(v_x_139_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_163_ == 0)
{
v___x_143_ = v_x_139_;
v_isShared_144_ = v_isSharedCheck_163_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_tail_141_);
lean_inc(v_head_140_);
lean_dec(v_x_139_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_163_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v_before_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_161_; 
v_before_145_ = lean_ctor_get(v_head_140_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v_head_140_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v_head_140_, 1);
lean_dec(v_unused_162_);
v___x_147_ = v_head_140_;
v_isShared_148_ = v_isSharedCheck_161_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_before_145_);
lean_dec(v_head_140_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_161_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 7);
lean_ctor_set(v___x_147_, 1, v___x_149_);
lean_ctor_set(v___x_147_, 0, v_x_138_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_x_138_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_160_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 7);
lean_ctor_set(v___x_143_, 1, v___x_152_);
lean_ctor_set(v___x_143_, 0, v___x_151_);
v___x_154_ = v___x_143_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_159_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = l_Lean_MessageData_ofSyntax(v_before_145_);
v___x_156_ = l_Lean_indentD(v___x_155_);
v___x_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_154_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v_x_138_ = v___x_157_;
v_x_139_ = v_tail_141_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(lean_object* v_opts_164_, lean_object* v_opt_165_){
_start:
{
lean_object* v_name_166_; lean_object* v_defValue_167_; lean_object* v_map_168_; lean_object* v___x_169_; 
v_name_166_ = lean_ctor_get(v_opt_165_, 0);
v_defValue_167_ = lean_ctor_get(v_opt_165_, 1);
v_map_168_ = lean_ctor_get(v_opts_164_, 0);
v___x_169_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_168_, v_name_166_);
if (lean_obj_tag(v___x_169_) == 0)
{
uint8_t v___x_170_; 
v___x_170_ = lean_unbox(v_defValue_167_);
return v___x_170_;
}
else
{
lean_object* v_val_171_; 
v_val_171_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_val_171_);
lean_dec_ref_known(v___x_169_, 1);
if (lean_obj_tag(v_val_171_) == 1)
{
uint8_t v_v_172_; 
v_v_172_ = lean_ctor_get_uint8(v_val_171_, 0);
lean_dec_ref_known(v_val_171_, 0);
return v_v_172_;
}
else
{
uint8_t v___x_173_; 
lean_dec(v_val_171_);
v___x_173_ = lean_unbox(v_defValue_167_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_164_ = stack[0].m_obj;
lean_object* v_opt_165_ = stack[1].m_obj;
uint8_t v_res_174_;
v_res_174_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(v_opts_164_, v_opt_165_);
stack->m_num = v_res_174_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_175_, lean_object* v_opt_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(v_opts_175_, v_opt_176_);
lean_dec_ref(v_opt_176_);
lean_dec_ref(v_opts_175_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1));
v___x_183_ = l_Lean_MessageData_ofFormat(v___x_182_);
return v___x_183_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(lean_object* v_msgData_184_, lean_object* v_macroStack_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_scopes_190_; lean_object* v___x_191_; lean_object* v_opts_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_188_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_189_ = lean_st_ref_get(v___y_186_);
v_scopes_190_ = lean_ctor_get(v___x_189_, 2);
lean_inc(v_scopes_190_);
lean_dec(v___x_189_);
v___x_191_ = l_List_head_x21___redArg(v___x_188_, v_scopes_190_);
lean_dec(v_scopes_190_);
v_opts_192_ = lean_ctor_get(v___x_191_, 1);
lean_inc_ref(v_opts_192_);
lean_dec(v___x_191_);
v___x_193_ = l_Lean_Elab_pp_macroStack;
v___x_194_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(v_opts_192_, v___x_193_);
lean_dec_ref(v_opts_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec(v_macroStack_185_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_msgData_184_);
return v___x_195_;
}
else
{
if (lean_obj_tag(v_macroStack_185_) == 0)
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v_msgData_184_);
return v___x_196_;
}
else
{
lean_object* v_head_197_; lean_object* v_after_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_213_; 
v_head_197_ = lean_ctor_get(v_macroStack_185_, 0);
lean_inc(v_head_197_);
v_after_198_ = lean_ctor_get(v_head_197_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_head_197_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_head_197_, 0);
lean_dec(v_unused_214_);
v___x_200_ = v_head_197_;
v_isShared_201_ = v_isSharedCheck_213_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_after_198_);
lean_dec(v_head_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_213_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 7);
lean_ctor_set(v___x_200_, 1, v___x_202_);
lean_ctor_set(v___x_200_, 0, v_msgData_184_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_msgData_184_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_212_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_msgData_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_205_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2);
v___x_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = l_Lean_MessageData_ofSyntax(v_after_198_);
v___x_208_ = l_Lean_indentD(v___x_207_);
v_msgData_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_209_, 0, v___x_206_);
lean_ctor_set(v_msgData_209_, 1, v___x_208_);
v___x_210_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4(v_msgData_209_, v_macroStack_185_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_184_ = stack[0].m_obj;
lean_object* v_macroStack_185_ = stack[1].m_obj;
lean_object* v___y_186_ = stack[2].m_obj;
lean_object* v_res_215_;
v_res_215_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_msgData_184_, v_macroStack_185_, v___y_186_);
stack->m_obj
 = v_res_215_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_216_, lean_object* v_macroStack_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_msgData_216_, v_macroStack_217_, v___y_218_);
lean_dec(v___y_218_);
return v_res_220_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(lean_object* v_msg_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Elab_Command_getRef___redArg(v___y_222_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v_macroStack_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_a_230_; lean_object* v___x_231_; lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_240_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v_macroStack_227_ = lean_ctor_get(v___y_222_, 4);
v___x_228_ = l_Lean_Elab_getBetterRef(v_a_226_, v_macroStack_227_);
lean_dec(v_a_226_);
v___x_229_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msg_221_, v___y_223_);
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref(v___x_229_);
lean_inc(v_macroStack_227_);
v___x_231_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_a_230_, v_macroStack_227_, v___y_223_);
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_240_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_228_);
lean_ctor_set(v___x_236_, 1, v_a_232_);
if (v_isShared_235_ == 0)
{
lean_ctor_set_tag(v___x_234_, 1);
lean_ctor_set(v___x_234_, 0, v___x_236_);
v___x_238_ = v___x_234_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref(v_msg_221_);
v_a_241_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_225_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_225_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_221_ = stack[0].m_obj;
lean_object* v___y_222_ = stack[1].m_obj;
lean_object* v___y_223_ = stack[2].m_obj;
lean_object* v_res_249_;
v_res_249_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(v_msg_221_, v___y_222_, v___y_223_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg___boxed(lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(v_msg_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_254_;
}
}
static lean_object* _init_l_Lean_Elab_Command_reproveDecl___closed__4(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Elab_Command_reproveDecl___closed__3));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Elab_Command_reproveDecl___closed__6(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Elab_Command_reproveDecl___closed__5));
v___x_265_ = l_Lean_stringToMessageData(v___x_264_);
return v___x_265_;
}
}
lean_object* l_Lean_Elab_Command_reproveDecl(lean_object* v_declName_266_, lean_object* v_tacticSeq_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; lean_object* v_env_272_; uint8_t v___x_273_; lean_object* v___x_274_; 
v___x_271_ = lean_st_ref_get(v_a_269_);
v_env_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_env_272_);
lean_dec(v___x_271_);
v___x_273_ = 0;
lean_inc(v_declName_266_);
v___x_274_ = l_Lean_Environment_find_x3f(v_env_272_, v_declName_266_, v___x_273_);
if (lean_obj_tag(v___x_274_) == 1)
{
lean_object* v_val_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_declName_266_);
v_val_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_322_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_322_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_val_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_322_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l_Lean_Elab_Command_reproveDecl___closed__2));
v___x_280_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_279_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = l_Lean_ConstantInfo_type(v_val_275_);
lean_inc_ref(v___x_282_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_282_);
v___x_284_ = v___x_277_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_313_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_285_ = 0;
v___x_286_ = lean_box(0);
v___x_287_ = lean_box(v___x_285_);
v___f_288_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_reproveDecl___lam__0___boxed), 11, 4);
lean_closure_set(v___f_288_, 0, v___x_284_);
lean_closure_set(v___f_288_, 1, v___x_287_);
lean_closure_set(v___f_288_, 2, v___x_286_);
lean_closure_set(v___f_288_, 3, v_tacticSeq_267_);
lean_inc(v_a_281_);
v___x_289_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withDeclName___boxed), 10, 3);
lean_closure_set(v___x_289_, 0, lean_box(0));
lean_closure_set(v___x_289_, 1, v_a_281_);
lean_closure_set(v___x_289_, 2, v___f_288_);
v___x_290_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_289_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = l_Lean_ConstantInfo_levelParams(v_val_275_);
lean_dec(v_val_275_);
lean_inc(v_a_281_);
v___x_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_293_, 0, v_a_281_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_ctor_set(v___x_293_, 2, v___x_282_);
v___x_294_ = lean_box(0);
v___x_295_ = 1;
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_297_, 0, v_a_281_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_298_, 0, v___x_293_);
lean_ctor_set(v___x_298_, 1, v_a_291_);
lean_ctor_set(v___x_298_, 2, v___x_294_);
lean_ctor_set(v___x_298_, 3, v___x_297_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*4, v___x_295_);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
v___x_300_ = 1;
v___x_301_ = lean_box(v___x_300_);
v___x_302_ = lean_box(v___x_273_);
v___x_303_ = lean_alloc_closure((void*)(l_Lean_addAndCompile___boxed), 6, 3);
lean_closure_set(v___x_303_, 0, v___x_299_);
lean_closure_set(v___x_303_, 1, v___x_301_);
lean_closure_set(v___x_303_, 2, v___x_302_);
v___x_304_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_303_, v_a_268_, v_a_269_);
return v___x_304_;
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec_ref(v___x_282_);
lean_dec(v_a_281_);
lean_dec(v_val_275_);
v_a_305_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_290_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_290_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_del_object(v___x_277_);
lean_dec(v_val_275_);
lean_dec(v_tacticSeq_267_);
v_a_314_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_280_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_280_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v___x_274_);
lean_dec(v_tacticSeq_267_);
v___x_323_ = lean_obj_once(&l_Lean_Elab_Command_reproveDecl___closed__4, &l_Lean_Elab_Command_reproveDecl___closed__4_once, _init_l_Lean_Elab_Command_reproveDecl___closed__4);
v___x_324_ = l_Lean_MessageData_ofName(v_declName_266_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_obj_once(&l_Lean_Elab_Command_reproveDecl___closed__6, &l_Lean_Elab_Command_reproveDecl___closed__6_once, _init_l_Lean_Elab_Command_reproveDecl___closed__6);
v___x_327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(v___x_327_, v_a_268_, v_a_269_);
return v___x_328_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_reproveDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_266_ = stack[0].m_obj;
lean_object* v_tacticSeq_267_ = stack[1].m_obj;
lean_object* v_a_268_ = stack[2].m_obj;
lean_object* v_a_269_ = stack[3].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_Elab_Command_reproveDecl(v_declName_266_, v_tacticSeq_267_, v_a_268_, v_a_269_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_reproveDecl___boxed(lean_object* v_declName_330_, lean_object* v_tacticSeq_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_Command_reproveDecl(v_declName_330_, v_tacticSeq_331_, v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_335_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msgData_336_, v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_336_ = stack[0].m_obj;
lean_object* v___y_337_ = stack[1].m_obj;
lean_object* v___y_338_ = stack[2].m_obj;
lean_object* v_res_341_;
v_res_341_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1(v_msgData_336_, v___y_337_, v___y_338_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___boxed(lean_object* v_msgData_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1(v_msgData_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
return v_res_346_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1(lean_object* v_00_u03b1_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(v_msg_348_, v___y_349_, v___y_350_);
return v___x_352_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_348_ = stack[1].m_obj;
lean_object* v___y_349_ = stack[2].m_obj;
lean_object* v___y_350_ = stack[3].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1(lean_box(0), v_msg_348_, v___y_349_, v___y_350_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___boxed(lean_object* v_00_u03b1_354_, lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1(v_00_u03b1_354_, v_msg_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_359_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2(lean_object* v_msgData_360_, lean_object* v_macroStack_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_msgData_360_, v_macroStack_361_, v___y_363_);
return v___x_365_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_360_ = stack[0].m_obj;
lean_object* v_macroStack_361_ = stack[1].m_obj;
lean_object* v___y_362_ = stack[2].m_obj;
lean_object* v___y_363_ = stack[3].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2(v_msgData_360_, v_macroStack_361_, v___y_362_, v___y_363_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___boxed(lean_object* v_msgData_367_, lean_object* v_macroStack_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2(v_msgData_367_, v_macroStack_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
return v_res_372_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(lean_object* v_tacticSeq_424_, lean_object* v_as_425_, size_t v_sz_426_, size_t v_i_427_, lean_object* v_b_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_usize_dec_lt(v_i_427_, v_sz_426_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec(v_tacticSeq_424_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v_b_428_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_434_ = lean_box(0);
v_a_435_ = lean_array_uget_borrowed(v_as_425_, v_i_427_);
v___x_436_ = lean_box(0);
lean_inc(v_a_435_);
v___x_437_ = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed), 5, 2);
lean_closure_set(v___x_437_, 0, v_a_435_);
lean_closure_set(v___x_437_, 1, v___x_436_);
v___x_438_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_437_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
lean_inc(v_tacticSeq_424_);
v___x_440_ = l_Lean_Elab_Command_reproveDecl(v_a_439_, v_tacticSeq_424_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_440_) == 0)
{
size_t v___x_441_; size_t v___x_442_; 
lean_dec_ref_known(v___x_440_, 1);
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_427_, v___x_441_);
v_i_427_ = v___x_442_;
v_b_428_ = v___x_434_;
goto _start;
}
else
{
lean_dec(v_tacticSeq_424_);
return v___x_440_;
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_dec(v_tacticSeq_424_);
v_a_444_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_438_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_438_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticSeq_424_ = stack[0].m_obj;
lean_object* v_as_425_ = stack[1].m_obj;
size_t v_sz_426_ = stack[2].m_num;
size_t v_i_427_ = stack[3].m_num;
lean_object* v_b_428_ = stack[4].m_obj;
lean_object* v___y_429_ = stack[5].m_obj;
lean_object* v___y_430_ = stack[6].m_obj;
lean_object* v_res_452_;
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(v_tacticSeq_424_, v_as_425_, v_sz_426_, v_i_427_, v_b_428_, v___y_429_, v___y_430_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0___boxed(lean_object* v_tacticSeq_453_, lean_object* v_as_454_, lean_object* v_sz_455_, lean_object* v_i_456_, lean_object* v_b_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
size_t v_sz_boxed_461_; size_t v_i_boxed_462_; lean_object* v_res_463_; 
v_sz_boxed_461_ = lean_unbox_usize(v_sz_455_);
lean_dec(v_sz_455_);
v_i_boxed_462_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(v_tacticSeq_453_, v_as_454_, v_sz_boxed_461_, v_i_boxed_462_, v_b_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_as_454_);
return v_res_463_;
}
}
lean_object* l_Lean_Elab_Command_elabReprove(lean_object* v_stx_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_identStxs_470_; lean_object* v___x_471_; lean_object* v_tacticSeq_472_; lean_object* v___x_473_; size_t v_sz_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = l_Lean_Syntax_getArg(v_stx_464_, v___x_468_);
v_identStxs_470_ = l_Lean_Syntax_getArgs(v___x_469_);
lean_dec(v___x_469_);
v___x_471_ = lean_unsigned_to_nat(3u);
v_tacticSeq_472_ = l_Lean_Syntax_getArg(v_stx_464_, v___x_471_);
v___x_473_ = lean_box(0);
v_sz_474_ = lean_array_size(v_identStxs_470_);
v___x_475_ = ((size_t)0ULL);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(v_tacticSeq_472_, v_identStxs_470_, v_sz_474_, v___x_475_, v___x_473_, v_a_465_, v_a_466_);
lean_dec_ref(v_identStxs_470_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v___x_476_, 0);
lean_dec(v_unused_484_);
v___x_478_ = v___x_476_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_dec(v___x_476_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_473_);
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_473_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
return v___x_476_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabReprove_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_464_ = stack[0].m_obj;
lean_object* v_a_465_ = stack[1].m_obj;
lean_object* v_a_466_ = stack[2].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Lean_Elab_Command_elabReprove(v_stx_464_, v_a_465_, v_a_466_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReprove___boxed(lean_object* v_stx_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Elab_Command_elabReprove(v_stx_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_stx_486_);
return v_res_490_;
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Reprove(uint8_t builtin) {
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
