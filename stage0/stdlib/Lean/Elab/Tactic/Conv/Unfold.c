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
lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_e_31_, v___y_37_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v___y_38_ = stack[7].m_obj;
lean_object* v___y_39_ = stack[8].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___boxed(lean_object* v_e_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0(v_e_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_53_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(lean_object* v_msgData_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; lean_object* v_env_61_; uint8_t v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v_toCold_65_; lean_object* v_mctx_66_; lean_object* v_lctx_67_; lean_object* v_options_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_60_ = lean_st_ref_get(v___y_58_);
v_env_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc_ref(v_env_61_);
lean_dec(v___x_60_);
v___x_62_ = 0;
v_env_63_ = l_Lean_Environment_setRecordingDeps(v_env_61_, v___x_62_);
v___x_64_ = lean_st_ref_get(v___y_56_);
v_toCold_65_ = lean_ctor_get(v___y_57_, 0);
v_mctx_66_ = lean_ctor_get(v___x_64_, 0);
lean_inc_ref(v_mctx_66_);
lean_dec(v___x_64_);
v_lctx_67_ = lean_ctor_get(v___y_55_, 2);
v_options_68_ = lean_ctor_get(v_toCold_65_, 2);
lean_inc_ref(v_options_68_);
lean_inc_ref(v_lctx_67_);
v___x_69_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_69_, 0, v_env_63_);
lean_ctor_set(v___x_69_, 1, v_mctx_66_);
lean_ctor_set(v___x_69_, 2, v_lctx_67_);
lean_ctor_set(v___x_69_, 3, v_options_68_);
v___x_70_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_msgData_54_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_54_ = stack[0].m_obj;
lean_object* v___y_55_ = stack[1].m_obj;
lean_object* v___y_56_ = stack[2].m_obj;
lean_object* v___y_57_ = stack[3].m_obj;
lean_object* v___y_58_ = stack[4].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msgData_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1___boxed(lean_object* v_msgData_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msgData_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_79_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(lean_object* v_msg_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_ref_86_; lean_object* v___x_87_; lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_ref_86_ = lean_ctor_get(v___y_83_, 2);
v___x_87_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msg_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
lean_inc(v_ref_86_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v_ref_86_);
lean_ctor_set(v___x_92_, 1, v_a_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 1);
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_80_ = stack[0].m_obj;
lean_object* v___y_81_ = stack[1].m_obj;
lean_object* v___y_82_ = stack[2].m_obj;
lean_object* v___y_83_ = stack[3].m_obj;
lean_object* v___y_84_ = stack[4].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v_msg_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg___boxed(lean_object* v_msg_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v_msg_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_104_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(lean_object* v_fvarId_105_, lean_object* v_____r_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_108_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_a_117_, v___y_112_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_mk_empty_array_with_capacity(v___x_120_);
v___x_122_ = lean_array_push(v___x_121_, v_fvarId_105_);
v___x_123_ = l_Lean_Meta_zetaDeltaFVars(v_a_119_, v___x_122_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_125_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v___x_123_, 1);
v___x_125_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_124_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
return v___x_125_;
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
v_a_126_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_123_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_123_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_fvarId_105_);
v_a_134_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_118_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_118_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_fvarId_105_);
v_a_142_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_116_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_116_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_105_ = stack[0].m_obj;
lean_object* v_____r_106_ = stack[1].m_obj;
lean_object* v___y_107_ = stack[2].m_obj;
lean_object* v___y_108_ = stack[3].m_obj;
lean_object* v___y_109_ = stack[4].m_obj;
lean_object* v___y_110_ = stack[5].m_obj;
lean_object* v___y_111_ = stack[6].m_obj;
lean_object* v___y_112_ = stack[7].m_obj;
lean_object* v___y_113_ = stack[8].m_obj;
lean_object* v___y_114_ = stack[9].m_obj;
lean_object* v_res_150_;
v_res_150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_105_, v_____r_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0___boxed(lean_object* v_fvarId_151_, lean_object* v_____r_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_151_, v_____r_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_162_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0));
v___x_165_ = l_Lean_stringToMessageData(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2));
v___x_168_ = l_Lean_stringToMessageData(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4));
v___x_171_ = l_Lean_stringToMessageData(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(lean_object* v_as_175_, size_t v_sz_176_, size_t v_i_177_, lean_object* v_b_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = lean_usize_dec_lt(v_i_177_, v_sz_176_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v_b_178_);
return v___x_189_;
}
else
{
lean_object* v_toCold_190_; lean_object* v_currRecDepth_191_; lean_object* v_ref_192_; uint16_t v_optionFlags_193_; uint8_t v_suppressElabErrors_194_; uint8_t v_isRecordingDeps_195_; lean_object* v___x_196_; lean_object* v___y_198_; lean_object* v_a_202_; uint8_t v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v_ref_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_toCold_190_ = lean_ctor_get(v___y_185_, 0);
v_currRecDepth_191_ = lean_ctor_get(v___y_185_, 1);
v_ref_192_ = lean_ctor_get(v___y_185_, 2);
v_optionFlags_193_ = lean_ctor_get_uint16(v___y_185_, sizeof(void*)*3);
v_suppressElabErrors_194_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 2);
v_isRecordingDeps_195_ = lean_ctor_get_uint8(v___y_185_, sizeof(void*)*3 + 3);
v___x_196_ = lean_box(0);
v_a_202_ = lean_array_uget_borrowed(v_as_175_, v_i_177_);
v___x_203_ = 0;
v___x_204_ = lean_box(v___x_203_);
lean_inc(v_a_202_);
v___x_205_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(v___x_205_, 0, v_a_202_);
lean_closure_set(v___x_205_, 1, v___x_204_);
v_ref_206_ = l_Lean_replaceRef(v_a_202_, v_ref_192_);
lean_inc(v_currRecDepth_191_);
lean_inc_ref(v_toCold_190_);
v___x_207_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_207_, 0, v_toCold_190_);
lean_ctor_set(v___x_207_, 1, v_currRecDepth_191_);
lean_ctor_set(v___x_207_, 2, v_ref_206_);
lean_ctor_set_uint16(v___x_207_, sizeof(void*)*3, v_optionFlags_193_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*3 + 2, v_suppressElabErrors_194_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*3 + 3, v_isRecordingDeps_195_);
v___x_208_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_205_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___x_207_, v___y_186_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
switch(lean_obj_tag(v_a_209_))
{
case 4:
{
lean_object* v_declName_210_; lean_object* v___x_211_; 
v_declName_210_ = lean_ctor_get(v_a_209_, 0);
lean_inc(v_declName_210_);
lean_dec_ref_known(v_a_209_, 2);
v___x_211_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_180_, v___y_183_, v___y_184_, v___x_207_, v___y_186_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v___x_213_ = l_Lean_Meta_unfold(v_a_212_, v_declName_210_, v___y_183_, v___y_184_, v___x_207_, v___y_186_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_213_, 1);
v___x_215_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_214_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___x_207_, v___y_186_);
lean_dec_ref_known(v___x_207_, 3);
v___y_198_ = v___x_215_;
goto v___jp_197_;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref_known(v___x_207_, 3);
v_a_216_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_213_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec(v_declName_210_);
lean_dec_ref_known(v___x_207_, 3);
v_a_224_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_211_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_211_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_232_; lean_object* v___x_233_; 
v_fvarId_232_ = lean_ctor_get(v_a_209_, 0);
lean_inc_n(v_fvarId_232_, 2);
v___x_233_ = l_Lean_FVarId_isLetVar___redArg(v_fvarId_232_, v___x_203_, v___y_183_, v___x_207_, v___y_186_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; uint8_t v___x_235_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = lean_unbox(v_a_234_);
lean_dec(v_a_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_236_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1);
v___x_237_ = l_Lean_MessageData_ofExpr(v_a_209_);
v___x_238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v___x_240_, v___y_183_, v___y_184_, v___x_207_, v___y_186_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_243_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_a_242_);
lean_dec_ref_known(v___x_241_, 1);
v___x_243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_232_, v_a_242_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___x_207_, v___y_186_);
lean_dec_ref_known(v___x_207_, 3);
v___y_198_ = v___x_243_;
goto v___jp_197_;
}
else
{
lean_dec(v_fvarId_232_);
lean_dec_ref_known(v___x_207_, 3);
v___y_198_ = v___x_241_;
goto v___jp_197_;
}
}
else
{
lean_object* v___x_244_; 
lean_dec_ref_known(v_a_209_, 1);
v___x_244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_232_, v___x_196_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___x_207_, v___y_186_);
lean_dec_ref_known(v___x_207_, 3);
v___y_198_ = v___x_244_;
goto v___jp_197_;
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref_known(v_a_209_, 1);
lean_dec(v_fvarId_232_);
lean_dec_ref_known(v___x_207_, 3);
v_a_245_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_233_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_233_);
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
default: 
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5);
v___x_254_ = l_Lean_MessageData_ofExpr(v_a_209_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v___x_257_, v___y_183_, v___y_184_, v___x_207_, v___y_186_);
lean_dec_ref_known(v___x_207_, 3);
v___y_198_ = v___x_258_;
goto v___jp_197_;
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec_ref_known(v___x_207_, 3);
v_a_259_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_208_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_208_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
v___jp_197_:
{
if (lean_obj_tag(v___y_198_) == 0)
{
size_t v___x_199_; size_t v___x_200_; 
lean_dec_ref_known(v___y_198_, 1);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_i_177_, v___x_199_);
v_i_177_ = v___x_200_;
v_b_178_ = v___x_196_;
goto _start;
}
else
{
return v___y_198_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_175_ = stack[0].m_obj;
size_t v_sz_176_ = stack[1].m_num;
size_t v_i_177_ = stack[2].m_num;
lean_object* v_b_178_ = stack[3].m_obj;
lean_object* v___y_179_ = stack[4].m_obj;
lean_object* v___y_180_ = stack[5].m_obj;
lean_object* v___y_181_ = stack[6].m_obj;
lean_object* v___y_182_ = stack[7].m_obj;
lean_object* v___y_183_ = stack[8].m_obj;
lean_object* v___y_184_ = stack[9].m_obj;
lean_object* v___y_185_ = stack[10].m_obj;
lean_object* v___y_186_ = stack[11].m_obj;
lean_object* v_res_267_;
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v_as_175_, v_sz_176_, v_i_177_, v_b_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
stack->m_obj
 = v_res_267_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___boxed(lean_object* v_as_268_, lean_object* v_sz_269_, lean_object* v_i_270_, lean_object* v_b_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
size_t v_sz_boxed_281_; size_t v_i_boxed_282_; lean_object* v_res_283_; 
v_sz_boxed_281_ = lean_unbox_usize(v_sz_269_);
lean_dec(v_sz_269_);
v_i_boxed_282_ = lean_unbox_usize(v_i_270_);
lean_dec(v_i_270_);
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v_as_268_, v_sz_boxed_281_, v_i_boxed_282_, v_b_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec_ref(v_as_268_);
return v_res_283_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(lean_object* v___x_284_, size_t v_sz_285_, size_t v___x_286_, lean_object* v___x_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v___x_284_, v_sz_285_, v___x_286_, v___x_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v___x_297_, 0);
lean_dec(v_unused_305_);
v___x_299_ = v___x_297_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_dec(v___x_297_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_287_);
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_287_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
else
{
return v___x_297_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_284_ = stack[0].m_obj;
size_t v_sz_285_ = stack[1].m_num;
size_t v___x_286_ = stack[2].m_num;
lean_object* v___x_287_ = stack[3].m_obj;
lean_object* v___y_288_ = stack[4].m_obj;
lean_object* v___y_289_ = stack[5].m_obj;
lean_object* v___y_290_ = stack[6].m_obj;
lean_object* v___y_291_ = stack[7].m_obj;
lean_object* v___y_292_ = stack[8].m_obj;
lean_object* v___y_293_ = stack[9].m_obj;
lean_object* v___y_294_ = stack[10].m_obj;
lean_object* v___y_295_ = stack[11].m_obj;
lean_object* v_res_306_;
v_res_306_ = l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(v___x_284_, v_sz_285_, v___x_286_, v___x_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
stack->m_obj
 = v_res_306_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed(lean_object* v___x_307_, lean_object* v_sz_308_, lean_object* v___x_309_, lean_object* v___x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
size_t v_sz_boxed_320_; size_t v___x_7635__boxed_321_; lean_object* v_res_322_; 
v_sz_boxed_320_ = lean_unbox_usize(v_sz_308_);
lean_dec(v_sz_308_);
v___x_7635__boxed_321_ = lean_unbox_usize(v___x_309_);
lean_dec(v___x_309_);
v_res_322_ = l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(v___x_307_, v_sz_boxed_320_, v___x_7635__boxed_321_, v___x_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec_ref(v___x_307_);
return v_res_322_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold(lean_object* v_stx_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; size_t v_sz_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___x_343_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = l_Lean_Syntax_getArg(v_stx_325_, v___x_335_);
v___x_337_ = l_Lean_Syntax_getArgs(v___x_336_);
lean_dec(v___x_336_);
v___x_338_ = lean_box(0);
v_sz_339_ = lean_array_size(v___x_337_);
v___x_340_ = lean_box_usize(v_sz_339_);
v___x_341_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1));
v___f_342_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed), 13, 4);
lean_closure_set(v___f_342_, 0, v___x_337_);
lean_closure_set(v___f_342_, 1, v___x_340_);
lean_closure_set(v___f_342_, 2, v___x_341_);
lean_closure_set(v___f_342_, 3, v___x_338_);
v___x_343_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_342_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
return v___x_343_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalUnfold_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_325_ = stack[0].m_obj;
lean_object* v_a_326_ = stack[1].m_obj;
lean_object* v_a_327_ = stack[2].m_obj;
lean_object* v_a_328_ = stack[3].m_obj;
lean_object* v_a_329_ = stack[4].m_obj;
lean_object* v_a_330_ = stack[5].m_obj;
lean_object* v_a_331_ = stack[6].m_obj;
lean_object* v_a_332_ = stack[7].m_obj;
lean_object* v_a_333_ = stack[8].m_obj;
lean_object* v_res_344_;
v_res_344_ = l_Lean_Elab_Tactic_Conv_evalUnfold(v_stx_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
stack->m_obj
 = v_res_344_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___boxed(lean_object* v_stx_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_Tactic_Conv_evalUnfold(v_stx_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_stx_345_);
return v_res_355_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(lean_object* v_00_u03b1_356_, lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v_msg_357_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
return v___x_367_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_357_ = stack[1].m_obj;
lean_object* v___y_358_ = stack[2].m_obj;
lean_object* v___y_359_ = stack[3].m_obj;
lean_object* v___y_360_ = stack[4].m_obj;
lean_object* v___y_361_ = stack[5].m_obj;
lean_object* v___y_362_ = stack[6].m_obj;
lean_object* v___y_363_ = stack[7].m_obj;
lean_object* v___y_364_ = stack[8].m_obj;
lean_object* v___y_365_ = stack[9].m_obj;
lean_object* v_res_368_;
v_res_368_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(lean_box(0), v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___boxed(lean_object* v_00_u03b1_369_, lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(v_00_u03b1_369_, v_msg_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_380_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1(){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_401_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5));
v___x_403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8));
v___x_404_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalUnfold___boxed), 10, 0);
v___x_405_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_401_, v___x_402_, v___x_403_, v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_406_;
v_res_406_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1();
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___boxed(lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1();
return v_res_408_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3(){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8));
v___x_436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6));
v___x_437_ = l_Lean_addBuiltinDeclarationRanges(v___x_435_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_438_;
v_res_438_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3();
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___boxed(lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3();
return v_res_440_;
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
