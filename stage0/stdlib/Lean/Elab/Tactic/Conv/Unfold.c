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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(lean_object* v_msgData_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; lean_object* v_env_59_; uint8_t v___x_60_; lean_object* v_env_61_; lean_object* v___x_62_; lean_object* v_toCold_63_; lean_object* v_mctx_64_; lean_object* v_lctx_65_; lean_object* v_options_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_58_ = lean_st_ref_get(v___y_56_);
v_env_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc_ref(v_env_59_);
lean_dec(v___x_58_);
v___x_60_ = 0;
v_env_61_ = l_Lean_Environment_setRecordingDeps(v_env_59_, v___x_60_);
v___x_62_ = lean_st_ref_get(v___y_54_);
v_toCold_63_ = lean_ctor_get(v___y_55_, 0);
v_mctx_64_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_mctx_64_);
lean_dec(v___x_62_);
v_lctx_65_ = lean_ctor_get(v___y_53_, 2);
v_options_66_ = lean_ctor_get(v_toCold_63_, 2);
lean_inc_ref(v_options_66_);
lean_inc_ref(v_lctx_65_);
v___x_67_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_67_, 0, v_env_61_);
lean_ctor_set(v___x_67_, 1, v_mctx_64_);
lean_ctor_set(v___x_67_, 2, v_lctx_65_);
lean_ctor_set(v___x_67_, 3, v_options_66_);
v___x_68_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_msgData_52_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1___boxed(lean_object* v_msgData_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msgData_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(lean_object* v_msg_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_ref_83_; lean_object* v___x_84_; lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_93_; 
v_ref_83_ = lean_ctor_get(v___y_80_, 2);
v___x_84_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1_spec__1(v_msg_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_93_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_93_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v___x_91_; 
lean_inc(v_ref_83_);
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v_ref_83_);
lean_ctor_set(v___x_89_, 1, v_a_85_);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
lean_ctor_set(v___x_87_, 0, v___x_89_);
v___x_91_ = v___x_87_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg___boxed(lean_object* v_msg_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v_msg_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(lean_object* v_fvarId_101_, lean_object* v_____r_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_104_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_114_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_112_, 1);
v___x_114_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__0___redArg(v_a_113_, v___y_108_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_a_115_);
lean_dec_ref_known(v___x_114_, 1);
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_mk_empty_array_with_capacity(v___x_116_);
v___x_118_ = lean_array_push(v___x_117_, v_fvarId_101_);
v___x_119_ = l_Lean_Meta_zetaDeltaFVars(v_a_115_, v___x_118_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_121_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref_known(v___x_119_, 1);
v___x_121_ = l_Lean_Elab_Tactic_Conv_changeLhs(v_a_120_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
return v___x_121_;
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_122_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_119_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_119_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v_fvarId_101_);
v_a_130_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_114_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_114_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_fvarId_101_);
v_a_138_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_112_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_112_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0___boxed(lean_object* v_fvarId_146_, lean_object* v_____r_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_146_, v_____r_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_157_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__0));
v___x_160_ = l_Lean_stringToMessageData(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__2));
v___x_163_ = l_Lean_stringToMessageData(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__4));
v___x_166_ = l_Lean_stringToMessageData(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__6));
v___x_169_ = l_Lean_stringToMessageData(v___x_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(lean_object* v_as_170_, size_t v_sz_171_, size_t v_i_172_, lean_object* v_b_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_lt(v_i_172_, v_sz_171_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v_b_173_);
return v___x_184_;
}
else
{
lean_object* v_toCold_185_; lean_object* v_currRecDepth_186_; lean_object* v_ref_187_; uint16_t v_optionFlags_188_; uint8_t v_suppressElabErrors_189_; uint8_t v_isRecordingDeps_190_; lean_object* v___x_191_; lean_object* v___y_193_; lean_object* v_a_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_ref_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_toCold_185_ = lean_ctor_get(v___y_180_, 0);
v_currRecDepth_186_ = lean_ctor_get(v___y_180_, 1);
v_ref_187_ = lean_ctor_get(v___y_180_, 2);
v_optionFlags_188_ = lean_ctor_get_uint16(v___y_180_, sizeof(void*)*3);
v_suppressElabErrors_189_ = lean_ctor_get_uint8(v___y_180_, sizeof(void*)*3 + 2);
v_isRecordingDeps_190_ = lean_ctor_get_uint8(v___y_180_, sizeof(void*)*3 + 3);
v___x_191_ = lean_box(0);
v_a_197_ = lean_array_uget_borrowed(v_as_170_, v_i_172_);
v___x_198_ = 0;
v___x_199_ = lean_box(v___x_198_);
lean_inc(v_a_197_);
v___x_200_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(v___x_200_, 0, v_a_197_);
lean_closure_set(v___x_200_, 1, v___x_199_);
v_ref_201_ = l_Lean_replaceRef(v_a_197_, v_ref_187_);
lean_inc(v_currRecDepth_186_);
lean_inc_ref(v_toCold_185_);
v___x_202_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_202_, 0, v_toCold_185_);
lean_ctor_set(v___x_202_, 1, v_currRecDepth_186_);
lean_ctor_set(v___x_202_, 2, v_ref_201_);
lean_ctor_set_uint16(v___x_202_, sizeof(void*)*3, v_optionFlags_188_);
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*3 + 2, v_suppressElabErrors_189_);
lean_ctor_set_uint8(v___x_202_, sizeof(void*)*3 + 3, v_isRecordingDeps_190_);
v___x_203_ = l_Lean_Elab_Tactic_withoutRecover___redArg(v___x_200_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___x_202_, v___y_181_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_a_204_);
lean_dec_ref_known(v___x_203_, 1);
switch(lean_obj_tag(v_a_204_))
{
case 4:
{
lean_object* v_declName_205_; lean_object* v___x_206_; 
v_declName_205_ = lean_ctor_get(v_a_204_, 0);
lean_inc(v_declName_205_);
lean_dec_ref_known(v_a_204_, 2);
v___x_206_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_175_, v___y_178_, v___y_179_, v___x_202_, v___y_181_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_208_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_206_, 1);
v___x_208_ = l_Lean_Meta_unfold(v_a_207_, v_declName_205_, v___y_178_, v___y_179_, v___x_202_, v___y_181_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_210_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_209_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___x_202_, v___y_181_);
lean_dec_ref_known(v___x_202_, 3);
v___y_193_ = v___x_210_;
goto v___jp_192_;
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec_ref_known(v___x_202_, 3);
v_a_211_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_208_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_208_);
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
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec(v_declName_205_);
lean_dec_ref_known(v___x_202_, 3);
v_a_219_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_206_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_206_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
case 1:
{
lean_object* v_fvarId_227_; lean_object* v___x_228_; 
v_fvarId_227_ = lean_ctor_get(v_a_204_, 0);
lean_inc_n(v_fvarId_227_, 2);
v___x_228_ = l_Lean_FVarId_isLetVar___redArg(v_fvarId_227_, v___x_198_, v___y_178_, v___x_202_, v___y_181_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; uint8_t v___x_230_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v___x_230_ = lean_unbox(v_a_229_);
lean_dec(v_a_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_231_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__1);
v___x_232_ = l_Lean_MessageData_ofExpr(v_a_204_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__3);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v___x_235_, v___y_178_, v___y_179_, v___x_202_, v___y_181_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref_known(v___x_236_, 1);
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_227_, v_a_237_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___x_202_, v___y_181_);
lean_dec_ref_known(v___x_202_, 3);
v___y_193_ = v___x_238_;
goto v___jp_192_;
}
else
{
lean_dec(v_fvarId_227_);
lean_dec_ref_known(v___x_202_, 3);
v___y_193_ = v___x_236_;
goto v___jp_192_;
}
}
else
{
lean_object* v___x_239_; 
lean_dec_ref_known(v_a_204_, 1);
v___x_239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___lam__0(v_fvarId_227_, v___x_191_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___x_202_, v___y_181_);
lean_dec_ref_known(v___x_202_, 3);
v___y_193_ = v___x_239_;
goto v___jp_192_;
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_fvarId_227_);
lean_dec_ref_known(v_a_204_, 1);
lean_dec_ref_known(v___x_202_, 3);
v_a_240_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_228_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_228_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
default: 
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_248_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__5);
v___x_249_ = l_Lean_MessageData_ofExpr(v_a_204_);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___closed__7);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v___x_252_, v___y_178_, v___y_179_, v___x_202_, v___y_181_);
lean_dec_ref_known(v___x_202_, 3);
v___y_193_ = v___x_253_;
goto v___jp_192_;
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref_known(v___x_202_, 3);
v_a_254_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_203_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_203_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
v___jp_192_:
{
if (lean_obj_tag(v___y_193_) == 0)
{
size_t v___x_194_; size_t v___x_195_; 
lean_dec_ref_known(v___y_193_, 1);
v___x_194_ = ((size_t)1ULL);
v___x_195_ = lean_usize_add(v_i_172_, v___x_194_);
v_i_172_ = v___x_195_;
v_b_173_ = v___x_191_;
goto _start;
}
else
{
return v___y_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2___boxed(lean_object* v_as_262_, lean_object* v_sz_263_, lean_object* v_i_264_, lean_object* v_b_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
size_t v_sz_boxed_275_; size_t v_i_boxed_276_; lean_object* v_res_277_; 
v_sz_boxed_275_ = lean_unbox_usize(v_sz_263_);
lean_dec(v_sz_263_);
v_i_boxed_276_ = lean_unbox_usize(v_i_264_);
lean_dec(v_i_264_);
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v_as_262_, v_sz_boxed_275_, v_i_boxed_276_, v_b_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec_ref(v_as_262_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(lean_object* v___x_278_, size_t v_sz_279_, size_t v___x_280_, lean_object* v___x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__2(v___x_278_, v_sz_279_, v___x_280_, v___x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_291_, 0);
lean_dec(v_unused_299_);
v___x_293_ = v___x_291_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_dec(v___x_291_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_281_);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_281_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed(lean_object* v___x_300_, lean_object* v_sz_301_, lean_object* v___x_302_, lean_object* v___x_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
size_t v_sz_boxed_313_; size_t v___x_7402__boxed_314_; lean_object* v_res_315_; 
v_sz_boxed_313_ = lean_unbox_usize(v_sz_301_);
lean_dec(v_sz_301_);
v___x_7402__boxed_314_ = lean_unbox_usize(v___x_302_);
lean_dec(v___x_302_);
v_res_315_ = l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0(v___x_300_, v_sz_boxed_313_, v___x_7402__boxed_314_, v___x_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec_ref(v___x_300_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold(lean_object* v_stx_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; size_t v_sz_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___f_335_; lean_object* v___x_336_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = l_Lean_Syntax_getArg(v_stx_318_, v___x_328_);
v___x_330_ = l_Lean_Syntax_getArgs(v___x_329_);
lean_dec(v___x_329_);
v___x_331_ = lean_box(0);
v_sz_332_ = lean_array_size(v___x_330_);
v___x_333_ = lean_box_usize(v_sz_332_);
v___x_334_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalUnfold___boxed__const__1));
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalUnfold___lam__0___boxed), 13, 4);
lean_closure_set(v___f_335_, 0, v___x_330_);
lean_closure_set(v___f_335_, 1, v___x_333_);
lean_closure_set(v___f_335_, 2, v___x_334_);
lean_closure_set(v___f_335_, 3, v___x_331_);
v___x_336_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_335_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___boxed(lean_object* v_stx_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Elab_Tactic_Conv_evalUnfold(v_stx_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_stx_337_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(lean_object* v_00_u03b1_348_, lean_object* v_msg_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___redArg(v_msg_349_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1___boxed(lean_object* v_00_u03b1_360_, lean_object* v_msg_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalUnfold_spec__1(v_00_u03b1_360_, v_msg_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1(){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_392_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_393_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__5));
v___x_394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8));
v___x_395_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalUnfold___boxed), 10, 0);
v___x_396_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_392_, v___x_393_, v___x_394_, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___boxed(lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1();
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3(){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold__1___closed__8));
v___x_426_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___closed__6));
v___x_427_ = l_Lean_addBuiltinDeclarationRanges(v___x_425_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3___boxed(lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Elab_Tactic_Conv_Unfold_0__Lean_Elab_Tactic_Conv_evalUnfold___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange__3();
return v_res_429_;
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
