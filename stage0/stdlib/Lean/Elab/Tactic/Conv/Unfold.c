// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Unfold
// Imports: public import Lean.Elab.Tactic.Unfold public import Lean.Elab.Tactic.Conv.Simp
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
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_isLetVar___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_changeLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "conv tactic `unfold` failed, local variable `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` has no definition"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "conv tactic `unfold` failed, expression "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = " is not a global or local constant"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unfold"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 13, 86, 191, 228, 222, 83, 199)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalUnfold"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 28, 26, 213, 142, 244, 71)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(49) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__0_value),((lean_object*)(((size_t)(49) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(53) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__3_value),((lean_object*)(((size_t)(53) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__4_value),((lean_object*)(((size_t)(63) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_e_30_, v___y_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__1(lean_object* v_fvarId_52_, lean_object* v_____r_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_55_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_63_, 1);
v___x_65_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_a_64_, v___y_59_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v___x_65_, 1);
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_mk_empty_array_with_capacity(v___x_67_);
v___x_69_ = lean_array_push(v___x_68_, v_fvarId_52_);
v___x_70_ = l_Lean_Meta_zetaDeltaFVars(v_a_66_, v___x_69_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_72_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_70_, 1);
v___x_72_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_71_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
return v___x_72_;
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_a_73_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_70_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_dec(v_fvarId_52_);
v_a_81_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_65_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_65_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v_fvarId_52_);
v_a_89_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_63_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_63_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__1___boxed(lean_object* v_fvarId_97_, lean_object* v_____r_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__1(v_fvarId_97_, v_____r_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(lean_object* v_msgData_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_env_116_; uint8_t v___x_117_; lean_object* v_env_118_; lean_object* v___x_119_; lean_object* v_toCold_120_; lean_object* v_mctx_121_; lean_object* v_lctx_122_; lean_object* v_options_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_115_ = lean_st_ref_get(v___y_113_);
v_env_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc_ref(v_env_116_);
lean_dec(v___x_115_);
v___x_117_ = 0;
v_env_118_ = l_Lean_Environment_setRecordingDeps(v_env_116_, v___x_117_);
v___x_119_ = lean_st_ref_get(v___y_111_);
v_toCold_120_ = lean_ctor_get(v___y_112_, 0);
v_mctx_121_ = lean_ctor_get(v___x_119_, 0);
lean_inc_ref(v_mctx_121_);
lean_dec(v___x_119_);
v_lctx_122_ = lean_ctor_get(v___y_110_, 2);
v_options_123_ = lean_ctor_get(v_toCold_120_, 2);
lean_inc_ref(v_options_123_);
lean_inc_ref(v_lctx_122_);
v___x_124_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_124_, 0, v_env_118_);
lean_ctor_set(v___x_124_, 1, v_mctx_121_);
lean_ctor_set(v___x_124_, 2, v_lctx_122_);
lean_ctor_set(v___x_124_, 3, v_options_123_);
v___x_125_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_msgData_109_);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1___boxed(lean_object* v_msgData_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msgData_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(lean_object* v_msg_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_ref_140_; lean_object* v___x_141_; lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_150_; 
v_ref_140_ = lean_ctor_get(v___y_137_, 2);
v___x_141_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msg_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
v_a_142_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_150_ == 0)
{
v___x_144_ = v___x_141_;
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_141_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_150_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
lean_inc(v_ref_140_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_ref_140_);
lean_ctor_set(v___x_146_, 1, v_a_142_);
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 1);
lean_ctor_set(v___x_144_, 0, v___x_146_);
v___x_148_ = v___x_144_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg___boxed(lean_object* v_msg_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v_msg_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(lean_object* v_a_158_, uint8_t v___x_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_toCold_169_; lean_object* v_currRecDepth_170_; lean_object* v_ref_171_; uint16_t v_optionFlags_172_; uint8_t v_suppressElabErrors_173_; uint8_t v_isRecordingDeps_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_toCold_169_ = lean_ctor_get(v___y_166_, 0);
v_currRecDepth_170_ = lean_ctor_get(v___y_166_, 1);
v_ref_171_ = lean_ctor_get(v___y_166_, 2);
v_optionFlags_172_ = lean_ctor_get_uint16(v___y_166_, sizeof(void*)*3);
v_suppressElabErrors_173_ = lean_ctor_get_uint8(v___y_166_, sizeof(void*)*3 + 2);
v_isRecordingDeps_174_ = lean_ctor_get_uint8(v___y_166_, sizeof(void*)*3 + 4);
v___x_175_ = 2;
lean_inc(v_ref_171_);
lean_inc(v_currRecDepth_170_);
lean_inc_ref(v_toCold_169_);
v___x_176_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_176_, 0, v_toCold_169_);
lean_ctor_set(v___x_176_, 1, v_currRecDepth_170_);
lean_ctor_set(v___x_176_, 2, v_ref_171_);
lean_ctor_set_uint16(v___x_176_, sizeof(void*)*3, v_optionFlags_172_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*3 + 2, v_suppressElabErrors_173_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*3 + 3, v___x_175_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*3 + 4, v_isRecordingDeps_174_);
v___x_177_ = l_Lean_Elab_Tactic_elabTermForApply(v_a_158_, v___x_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___x_176_, v___y_167_);
lean_dec_ref_known(v___x_176_, 3);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0___boxed(lean_object* v_a_178_, lean_object* v___x_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
uint8_t v___x_7909__boxed_189_; lean_object* v_res_190_; 
v___x_7909__boxed_189_ = lean_unbox(v___x_179_);
v_res_190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_a_178_, v___x_7909__boxed_189_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_190_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0));
v___x_193_ = l_Lean_stringToMessageData(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(lean_object* v_as_203_, size_t v_sz_204_, size_t v_i_205_, lean_object* v_b_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
uint8_t v___x_216_; 
v___x_216_ = lean_usize_dec_lt(v_i_205_, v_sz_204_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v_b_206_);
return v___x_217_;
}
else
{
lean_object* v_toCold_218_; lean_object* v_currRecDepth_219_; lean_object* v_ref_220_; uint16_t v_optionFlags_221_; uint8_t v_suppressElabErrors_222_; uint8_t v_checkDeprecated_223_; uint8_t v_isRecordingDeps_224_; lean_object* v___x_225_; lean_object* v___y_227_; lean_object* v_a_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___f_234_; lean_object* v_ref_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_toCold_218_ = lean_ctor_get(v___y_213_, 0);
v_currRecDepth_219_ = lean_ctor_get(v___y_213_, 1);
v_ref_220_ = lean_ctor_get(v___y_213_, 2);
v_optionFlags_221_ = lean_ctor_get_uint16(v___y_213_, sizeof(void*)*3);
v_suppressElabErrors_222_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*3 + 2);
v_checkDeprecated_223_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*3 + 3);
v_isRecordingDeps_224_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*3 + 4);
v___x_225_ = lean_box(0);
v_a_231_ = lean_array_uget_borrowed(v_as_203_, v_i_205_);
v___x_232_ = 0;
v___x_233_ = lean_box(v___x_232_);
lean_inc(v_a_231_);
v___f_234_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0___boxed), 11, 2);
lean_closure_set(v___f_234_, 0, v_a_231_);
lean_closure_set(v___f_234_, 1, v___x_233_);
v_ref_235_ = l_Lean_replaceRef(v_a_231_, v_ref_220_);
lean_inc(v_currRecDepth_219_);
lean_inc_ref(v_toCold_218_);
v___x_236_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_236_, 0, v_toCold_218_);
lean_ctor_set(v___x_236_, 1, v_currRecDepth_219_);
lean_ctor_set(v___x_236_, 2, v_ref_235_);
lean_ctor_set_uint16(v___x_236_, sizeof(void*)*3, v_optionFlags_221_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*3 + 2, v_suppressElabErrors_222_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*3 + 3, v_checkDeprecated_223_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*3 + 4, v_isRecordingDeps_224_);
v___x_237_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___f_234_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___x_236_, v___y_214_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
switch(lean_obj_tag(v_a_238_))
{
case 4:
{
lean_object* v_declName_239_; lean_object* v___x_240_; 
v_declName_239_ = lean_ctor_get(v_a_238_, 0);
lean_inc(v_declName_239_);
lean_dec_ref_known(v_a_238_, 2);
v___x_240_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_208_, v___y_211_, v___y_212_, v___x_236_, v___y_214_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = l_Lean_Meta_unfold(v_a_241_, v_declName_239_, v___y_211_, v___y_212_, v___x_236_, v___y_214_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_243_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___x_236_, v___y_214_);
lean_dec_ref_known(v___x_236_, 3);
v___y_227_ = v___x_244_;
goto v___jp_226_;
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref_known(v___x_236_, 3);
v_a_245_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_242_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_242_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_declName_239_);
lean_dec_ref_known(v___x_236_, 3);
v_a_253_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_240_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_240_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_261_; lean_object* v___x_262_; 
v_fvarId_261_ = lean_ctor_get(v_a_238_, 0);
lean_inc_n(v_fvarId_261_, 2);
v___x_262_ = l_Lean_FVarId_isLetVar___redArg(v_fvarId_261_, v___x_232_, v___y_211_, v___x_236_, v___y_214_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; uint8_t v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
v___x_264_ = lean_unbox(v_a_263_);
lean_dec(v_a_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_265_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1);
v___x_266_ = l_Lean_MessageData_ofExpr(v_a_238_);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v___x_269_, v___y_211_, v___y_212_, v___x_236_, v___y_214_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__1(v_fvarId_261_, v_a_271_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___x_236_, v___y_214_);
lean_dec_ref_known(v___x_236_, 3);
v___y_227_ = v___x_272_;
goto v___jp_226_;
}
else
{
lean_dec(v_fvarId_261_);
lean_dec_ref_known(v___x_236_, 3);
return v___x_270_;
}
}
else
{
lean_object* v___x_273_; 
lean_dec_ref_known(v_a_238_, 1);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__1(v_fvarId_261_, v___x_225_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___x_236_, v___y_214_);
lean_dec_ref_known(v___x_236_, 3);
v___y_227_ = v___x_273_;
goto v___jp_226_;
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref_known(v_a_238_, 1);
lean_dec(v_fvarId_261_);
lean_dec_ref_known(v___x_236_, 3);
v_a_274_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_262_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_262_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
default: 
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_282_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5);
v___x_283_ = l_Lean_MessageData_ofExpr(v_a_238_);
v___x_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v___x_286_, v___y_211_, v___y_212_, v___x_236_, v___y_214_);
lean_dec_ref_known(v___x_236_, 3);
v___y_227_ = v___x_287_;
goto v___jp_226_;
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec_ref_known(v___x_236_, 3);
v_a_288_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_237_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_237_);
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
v___jp_226_:
{
if (lean_obj_tag(v___y_227_) == 0)
{
size_t v___x_228_; size_t v___x_229_; 
lean_dec_ref_known(v___y_227_, 1);
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_205_, v___x_228_);
v_i_205_ = v___x_229_;
v_b_206_ = v___x_225_;
goto _start;
}
else
{
return v___y_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___boxed(lean_object* v_as_296_, lean_object* v_sz_297_, lean_object* v_i_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
size_t v_sz_boxed_309_; size_t v_i_boxed_310_; lean_object* v_res_311_; 
v_sz_boxed_309_ = lean_unbox_usize(v_sz_297_);
lean_dec(v_sz_297_);
v_i_boxed_310_ = lean_unbox_usize(v_i_298_);
lean_dec(v_i_298_);
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v_as_296_, v_sz_boxed_309_, v_i_boxed_310_, v_b_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec_ref(v_as_296_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(lean_object* v___x_312_, size_t v_sz_313_, size_t v___x_314_, lean_object* v___x_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v___x_312_, v_sz_313_, v___x_314_, v___x_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___x_325_, 0);
lean_dec(v_unused_333_);
v___x_327_ = v___x_325_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_dec(v___x_325_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_315_);
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_315_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed(lean_object* v___x_334_, lean_object* v_sz_335_, lean_object* v___x_336_, lean_object* v___x_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
size_t v_sz_boxed_347_; size_t v___x_8155__boxed_348_; lean_object* v_res_349_; 
v_sz_boxed_347_ = lean_unbox_usize(v_sz_335_);
lean_dec(v_sz_335_);
v___x_8155__boxed_348_ = lean_unbox_usize(v___x_336_);
lean_dec(v___x_336_);
v_res_349_ = l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(v___x_334_, v_sz_boxed_347_, v___x_8155__boxed_348_, v___x_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec_ref(v___x_334_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold(lean_object* v_stx_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; size_t v_sz_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___f_369_; lean_object* v___x_370_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = l_Lean_Syntax_getArg(v_stx_352_, v___x_362_);
v___x_364_ = l_Lean_Syntax_getArgs(v___x_363_);
lean_dec(v___x_363_);
v___x_365_ = lean_box(0);
v_sz_366_ = lean_array_size(v___x_364_);
v___x_367_ = lean_box_usize(v_sz_366_);
v___x_368_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1));
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed), 13, 4);
lean_closure_set(v___f_369_, 0, v___x_364_);
lean_closure_set(v___f_369_, 1, v___x_367_);
lean_closure_set(v___f_369_, 2, v___x_368_);
lean_closure_set(v___f_369_, 3, v___x_365_);
v___x_370_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_369_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___boxed(lean_object* v_stx_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Elab_Tactic_Conv_evalUnfold(v_stx_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_stx_371_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(lean_object* v_00_u03b1_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v_msg_383_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___boxed(lean_object* v_00_u03b1_394_, lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(v_00_u03b1_394_, v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1(){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5));
v___x_428_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8));
v___x_429_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalUnfold___boxed), 10, 0);
v___x_430_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_426_, v___x_427_, v___x_428_, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___boxed(lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1();
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8));
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6));
v___x_461_ = l_Lean_addBuiltinDeclarationRanges(v___x_459_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___boxed(lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3();
return v_res_463_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Unfold(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Unfold(builtin);
}
#ifdef __cplusplus
}
#endif
