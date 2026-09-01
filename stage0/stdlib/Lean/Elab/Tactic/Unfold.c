// Lean compiler output
// Module: Lean.Elab.Tactic.Unfold
// Imports: public import Lean.Meta.Tactic.Unfold public import Lean.Elab.Tactic.Location
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_isLetVar___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldTarget___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaTarget___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unfold"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 37, 25, 138, 30, 217, 227, 180)}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "did not unfold '"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Tactic `unfold` failed: Local variable `"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` has no definition"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expression "};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = " is not a global or local constant"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 165, 59, 41, 65, 58, 102, 253)}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalUnfold"};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(50, 231, 186, 51, 228, 140, 188, 50)}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "\"unfold \" ident+ (location)\? "};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(28) << 1) | 1)),((lean_object*)(((size_t)(129) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__0_value),((lean_object*)(((size_t)(44) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__1_value),((lean_object*)(((size_t)(129) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(21) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__3_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__4_value),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(lean_object* v_declName_1_, lean_object* v_fvarId_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v___x_9_, 1);
v___x_11_ = l_Lean_Meta_unfoldLocalDecl(v_a_10_, v_fvarId_2_, v_declName_1_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_a_12_);
lean_dec_ref_known(v___x_11_, 1);
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_14_, 0, v_a_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
v___x_15_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_14_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_23_; 
v_a_16_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_23_ == 0)
{
v___x_18_ = v___x_11_;
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_11_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_21_; 
if (v_isShared_19_ == 0)
{
v___x_21_ = v___x_18_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_a_16_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
else
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
lean_dec(v_fvarId_2_);
lean_dec(v_declName_1_);
v_a_24_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_9_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_9_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldLocalDecl___redArg___boxed(lean_object* v_declName_32_, lean_object* v_fvarId_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(v_declName_32_, v_fvarId_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldLocalDecl(lean_object* v_declName_41_, lean_object* v_fvarId_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Elab_Tactic_unfoldLocalDecl___redArg(v_declName_41_, v_fvarId_42_, v_a_44_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldLocalDecl___boxed(lean_object* v_declName_53_, lean_object* v_fvarId_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Elab_Tactic_unfoldLocalDecl(v_declName_53_, v_fvarId_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldTarget___redArg(lean_object* v_declName_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = l_Lean_Meta_unfoldTarget(v_a_73_, v_declName_65_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v___x_74_, 1);
v___x_76_ = lean_box(0);
v___x_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_77_, 0, v_a_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_77_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
return v___x_78_;
}
else
{
lean_object* v_a_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
v_a_79_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v___x_74_;
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_a_79_);
lean_dec(v___x_74_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
lean_dec(v_declName_65_);
v_a_87_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_72_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_72_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldTarget___redArg___boxed(lean_object* v_declName_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Elab_Tactic_unfoldTarget___redArg(v_declName_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldTarget(lean_object* v_declName_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Elab_Tactic_unfoldTarget___redArg(v_declName_103_, v_a_105_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_unfoldTarget___boxed(lean_object* v_declName_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Elab_Tactic_unfoldTarget(v_declName_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(lean_object* v_declFVarId_125_, lean_object* v_fvarId_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = l_Lean_Meta_zetaDeltaLocalDecl(v_a_134_, v_fvarId_126_, v_declFVarId_125_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v___x_137_ = lean_box(0);
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v_a_136_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_138_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_);
return v___x_139_;
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_135_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_135_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v_fvarId_126_);
lean_dec(v_declFVarId_125_);
v_a_148_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_133_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_133_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg___boxed(lean_object* v_declFVarId_156_, lean_object* v_fvarId_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(v_declFVarId_156_, v_fvarId_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaLocalDecl(lean_object* v_declFVarId_165_, lean_object* v_fvarId_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Elab_Tactic_zetaDeltaLocalDecl___redArg(v_declFVarId_165_, v_fvarId_166_, v_a_168_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaLocalDecl___boxed(lean_object* v_declFVarId_177_, lean_object* v_fvarId_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Elab_Tactic_zetaDeltaLocalDecl(v_declFVarId_177_, v_fvarId_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(lean_object* v_declFVarId_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_198_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_198_ = l_Lean_Meta_zetaDeltaTarget(v_a_197_, v_declFVarId_189_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v_a_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_201_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
return v___x_202_;
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_198_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_198_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_declFVarId_189_);
v_a_211_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_196_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_196_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaTarget___redArg___boxed(lean_object* v_declFVarId_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(v_declFVarId_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaTarget(lean_object* v_declFVarId_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Elab_Tactic_zetaDeltaTarget___redArg(v_declFVarId_227_, v_a_229_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_zetaDeltaTarget___boxed(lean_object* v_declFVarId_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Elab_Tactic_zetaDeltaTarget(v_declFVarId_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
return v_res_248_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__2));
v___x_254_ = l_Lean_stringToMessageData(v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__4));
v___x_257_ = l_Lean_stringToMessageData(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0(lean_object* v_declName_258_, lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1));
v___x_270_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3);
v___x_271_ = l_Lean_MessageData_ofName(v_declName_258_);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
v___x_276_ = l_Lean_Meta_throwTacticEx___redArg(v___x_269_, v_x_259_, v___x_275_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___boxed(lean_object* v_declName_277_, lean_object* v_x_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0(v_declName_277_, v_x_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1(lean_object* v_a_289_, lean_object* v_x_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1));
v___x_301_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__3);
v___x_302_ = l_Lean_MessageData_ofExpr(v_a_289_);
v___x_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__5);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = l_Lean_Meta_throwTacticEx___redArg(v___x_300_, v_x_290_, v___x_306_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1___boxed(lean_object* v_a_308_, lean_object* v_x_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1(v_a_308_, v_x_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_env_327_; lean_object* v___x_328_; lean_object* v_mctx_329_; lean_object* v_lctx_330_; lean_object* v_options_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = lean_st_ref_get(v___y_322_);
v_mctx_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc_ref(v_mctx_329_);
lean_dec(v___x_328_);
v_lctx_330_ = lean_ctor_get(v___y_321_, 2);
v_options_331_ = lean_ctor_get(v___y_323_, 1);
lean_inc_ref(v_options_331_);
lean_inc_ref(v_lctx_330_);
v___x_332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_332_, 0, v_env_327_);
lean_ctor_set(v___x_332_, 1, v_mctx_329_);
lean_ctor_set(v___x_332_, 2, v_lctx_330_);
lean_ctor_set(v___x_332_, 3, v_options_331_);
v___x_333_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_msgData_320_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0___boxed(lean_object* v_msgData_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(v_msgData_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(lean_object* v_msg_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_ref_348_; lean_object* v___x_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_ref_348_ = lean_ctor_get(v___y_345_, 4);
v___x_349_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0_spec__0(v_msg_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
lean_inc(v_ref_348_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_ref_348_);
lean_ctor_set(v___x_354_, 1, v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 1);
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg___boxed(lean_object* v_msg_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v_msg_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__0));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__2));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__4));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__6));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2(lean_object* v_declNameId_378_, lean_object* v___x_379_, lean_object* v_loc_380_, uint8_t v___x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_toCold_391_; lean_object* v_options_392_; lean_object* v_currRecDepth_393_; lean_object* v_maxRecDepth_394_; lean_object* v_ref_395_; lean_object* v_currNamespace_396_; lean_object* v_openDecls_397_; lean_object* v_initHeartbeats_398_; lean_object* v_maxHeartbeats_399_; lean_object* v_currMacroScope_400_; uint8_t v_diag_401_; uint8_t v_suppressElabErrors_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_474_; 
v_toCold_391_ = lean_ctor_get(v___y_388_, 0);
v_options_392_ = lean_ctor_get(v___y_388_, 1);
v_currRecDepth_393_ = lean_ctor_get(v___y_388_, 2);
v_maxRecDepth_394_ = lean_ctor_get(v___y_388_, 3);
v_ref_395_ = lean_ctor_get(v___y_388_, 4);
v_currNamespace_396_ = lean_ctor_get(v___y_388_, 5);
v_openDecls_397_ = lean_ctor_get(v___y_388_, 6);
v_initHeartbeats_398_ = lean_ctor_get(v___y_388_, 7);
v_maxHeartbeats_399_ = lean_ctor_get(v___y_388_, 8);
v_currMacroScope_400_ = lean_ctor_get(v___y_388_, 9);
v_diag_401_ = lean_ctor_get_uint8(v___y_388_, sizeof(void*)*10);
v_suppressElabErrors_402_ = lean_ctor_get_uint8(v___y_388_, sizeof(void*)*10 + 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v___y_388_);
if (v_isSharedCheck_474_ == 0)
{
v___x_404_ = v___y_388_;
v_isShared_405_ = v_isSharedCheck_474_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_currMacroScope_400_);
lean_inc(v_maxHeartbeats_399_);
lean_inc(v_initHeartbeats_398_);
lean_inc(v_openDecls_397_);
lean_inc(v_currNamespace_396_);
lean_inc(v_ref_395_);
lean_inc(v_maxRecDepth_394_);
lean_inc(v_currRecDepth_393_);
lean_inc(v_options_392_);
lean_inc(v_toCold_391_);
lean_dec(v___y_388_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_474_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_ref_406_; lean_object* v___x_408_; 
v_ref_406_ = l_Lean_replaceRef(v_declNameId_378_, v_ref_395_);
lean_dec(v_ref_395_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 4, v_ref_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_toCold_391_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_options_392_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_currRecDepth_393_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_maxRecDepth_394_);
lean_ctor_set(v_reuseFailAlloc_473_, 4, v_ref_406_);
lean_ctor_set(v_reuseFailAlloc_473_, 5, v_currNamespace_396_);
lean_ctor_set(v_reuseFailAlloc_473_, 6, v_openDecls_397_);
lean_ctor_set(v_reuseFailAlloc_473_, 7, v_initHeartbeats_398_);
lean_ctor_set(v_reuseFailAlloc_473_, 8, v_maxHeartbeats_399_);
lean_ctor_set(v_reuseFailAlloc_473_, 9, v_currMacroScope_400_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, sizeof(void*)*10, v_diag_401_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, sizeof(void*)*10 + 1, v_suppressElabErrors_402_);
v___x_408_ = v_reuseFailAlloc_473_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_379_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___x_408_, v___y_389_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
switch(lean_obj_tag(v_a_410_))
{
case 4:
{
lean_object* v_declName_411_; lean_object* v___f_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_declName_411_ = lean_ctor_get(v_a_410_, 0);
lean_inc_n(v_declName_411_, 3);
lean_dec_ref_known(v_a_410_, 2);
v___f_412_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___boxed), 11, 1);
lean_closure_set(v___f_412_, 0, v_declName_411_);
v___x_413_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_unfoldLocalDecl___boxed), 11, 1);
lean_closure_set(v___x_413_, 0, v_declName_411_);
v___x_414_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_unfoldTarget___boxed), 10, 1);
lean_closure_set(v___x_414_, 0, v_declName_411_);
v___x_415_ = l_Lean_Elab_Tactic_withLocation(v_loc_380_, v___x_413_, v___x_414_, v___f_412_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___x_408_, v___y_389_);
lean_dec_ref(v___x_408_);
return v___x_415_;
}
case 1:
{
lean_object* v_fvarId_416_; lean_object* v___x_417_; 
v_fvarId_416_ = lean_ctor_get(v_a_410_, 0);
lean_inc(v_fvarId_416_);
v___x_417_ = l_Lean_FVarId_isLetVar___redArg(v_fvarId_416_, v___x_381_, v___y_386_, v___x_408_, v___y_389_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___f_419_; lean_object* v___y_421_; lean_object* v___y_422_; lean_object* v___y_423_; lean_object* v___y_424_; lean_object* v___y_425_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; uint8_t v___x_432_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_417_, 1);
lean_inc_ref(v_a_410_);
v___f_419_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__1___boxed), 11, 1);
lean_closure_set(v___f_419_, 0, v_a_410_);
v___x_432_ = lean_unbox(v_a_418_);
lean_dec(v_a_418_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec_ref(v___f_419_);
v___x_433_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1, &l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1_once, _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__1);
v___x_434_ = l_Lean_MessageData_ofExpr(v_a_410_);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3, &l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3_once, _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__3);
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v___x_437_, v___y_386_, v___y_387_, v___x_408_, v___y_389_);
lean_dec_ref(v___x_408_);
return v___x_438_;
}
else
{
lean_inc(v_fvarId_416_);
lean_dec_ref_known(v_a_410_, 1);
v___y_421_ = v___y_382_;
v___y_422_ = v___y_383_;
v___y_423_ = v___y_384_;
v___y_424_ = v___y_385_;
v___y_425_ = v___y_386_;
v___y_426_ = v___y_387_;
v___y_427_ = v___x_408_;
v___y_428_ = v___y_389_;
goto v___jp_420_;
}
v___jp_420_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_inc(v_fvarId_416_);
v___x_429_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_zetaDeltaLocalDecl___boxed), 11, 1);
lean_closure_set(v___x_429_, 0, v_fvarId_416_);
v___x_430_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_zetaDeltaTarget___boxed), 10, 1);
lean_closure_set(v___x_430_, 0, v_fvarId_416_);
v___x_431_ = l_Lean_Elab_Tactic_withLocation(v_loc_380_, v___x_429_, v___x_430_, v___f_419_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec_ref(v___y_427_);
return v___x_431_;
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref_known(v_a_410_, 1);
lean_dec_ref(v___x_408_);
v_a_439_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_417_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_417_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
default: 
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_383_, v___y_386_, v___y_387_, v___x_408_, v___y_389_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__0___closed__1));
v___x_450_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5, &l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5_once, _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__5);
v___x_451_ = l_Lean_MessageData_ofExpr(v_a_410_);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7, &l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7_once, _init_l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___closed__7);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
v___x_456_ = l_Lean_Meta_throwTacticEx___redArg(v___x_449_, v_a_448_, v___x_455_, v___y_386_, v___y_387_, v___x_408_, v___y_389_);
lean_dec_ref(v___x_408_);
return v___x_456_;
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_a_410_);
lean_dec_ref(v___x_408_);
v_a_457_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_447_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_447_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v___x_408_);
v_a_465_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_409_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_409_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___boxed(lean_object* v_declNameId_475_, lean_object* v___x_476_, lean_object* v_loc_477_, lean_object* v___x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
uint8_t v___x_5170__boxed_488_; lean_object* v_res_489_; 
v___x_5170__boxed_488_ = lean_unbox(v___x_478_);
v_res_489_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2(v_declNameId_475_, v___x_476_, v_loc_477_, v___x_5170__boxed_488_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v_loc_477_);
lean_dec(v_declNameId_475_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go(lean_object* v_declNameId_490_, lean_object* v_loc_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
uint8_t v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___f_505_; lean_object* v___x_506_; 
v___x_501_ = 0;
v___x_502_ = lean_box(v___x_501_);
lean_inc(v_declNameId_490_);
v___x_503_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(v___x_503_, 0, v_declNameId_490_);
lean_closure_set(v___x_503_, 1, v___x_502_);
v___x_504_ = lean_box(v___x_501_);
v___f_505_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___lam__2___boxed), 13, 4);
lean_closure_set(v___f_505_, 0, v_declNameId_490_);
lean_closure_set(v___f_505_, 1, v___x_503_);
lean_closure_set(v___f_505_, 2, v_loc_491_);
lean_closure_set(v___f_505_, 3, v___x_504_);
v___x_506_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_505_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go___boxed(lean_object* v_declNameId_507_, lean_object* v_loc_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go(v_declNameId_507_, v_loc_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0(lean_object* v_00_u03b1_519_, lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___redArg(v_msg_520_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0___boxed(lean_object* v_00_u03b1_531_, lean_object* v_msg_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go_spec__0(v_00_u03b1_531_, v_msg_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(lean_object* v_loc_543_, lean_object* v_as_544_, size_t v_sz_545_, size_t v_i_546_, lean_object* v_b_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_546_, v_sz_545_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v_loc_543_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v_b_547_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_array_uget_borrowed(v_as_544_, v_i_546_);
lean_inc(v_loc_543_);
lean_inc(v_a_559_);
v___x_560_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold_go(v_a_559_, v_loc_543_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; size_t v___x_562_; size_t v___x_563_; 
lean_dec_ref_known(v___x_560_, 1);
v___x_561_ = lean_box(0);
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_add(v_i_546_, v___x_562_);
v_i_546_ = v___x_563_;
v_b_547_ = v___x_561_;
goto _start;
}
else
{
lean_dec(v_loc_543_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0___boxed(lean_object* v_loc_565_, lean_object* v_as_566_, lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_580_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(v_loc_565_, v_as_566_, v_sz_boxed_579_, v_i_boxed_580_, v_b_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v_as_566_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnfold(lean_object* v_stx_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_loc_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; size_t v_sz_599_; size_t v___x_600_; lean_object* v___x_601_; 
v___x_592_ = lean_unsigned_to_nat(2u);
v___x_593_ = l_Lean_Syntax_getArg(v_stx_582_, v___x_592_);
v_loc_594_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_593_);
lean_dec(v___x_593_);
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = l_Lean_Syntax_getArg(v_stx_582_, v___x_595_);
v___x_597_ = l_Lean_Syntax_getArgs(v___x_596_);
lean_dec(v___x_596_);
v___x_598_ = lean_box(0);
v_sz_599_ = lean_array_size(v___x_597_);
v___x_600_ = ((size_t)0ULL);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalUnfold_spec__0(v_loc_594_, v___x_597_, v_sz_599_, v___x_600_, v___x_598_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec_ref(v___x_597_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_608_ == 0)
{
lean_object* v_unused_609_; 
v_unused_609_ = lean_ctor_get(v___x_601_, 0);
lean_dec(v_unused_609_);
v___x_603_ = v___x_601_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_dec(v___x_601_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_598_);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_598_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnfold___boxed(lean_object* v_stx_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Elab_Tactic_evalUnfold(v_stx_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_stx_610_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1(){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_637_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__3));
v___x_639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6));
v___x_640_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalUnfold___boxed), 10, 0);
v___x_641_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_637_, v___x_638_, v___x_639_, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___boxed(lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1();
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3(){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6));
v___x_647_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___closed__0));
v___x_648_ = l_Lean_addBuiltinDocString(v___x_646_, v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3___boxed(lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3();
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5(){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1___closed__6));
v___x_678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___closed__6));
v___x_679_ = l_Lean_addBuiltinDeclarationRanges(v___x_677_, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5___boxed(lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5();
return v_res_681_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Unfold_0__Lean_Elab_Tactic_evalUnfold___regBuiltin_Lean_Elab_Tactic_evalUnfold_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Unfold(builtin);
}
#ifdef __cplusplus
}
#endif
