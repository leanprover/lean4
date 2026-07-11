// Lean compiler output
// Module: Lean.Elab.Tactic.Generalize
// Imports: public import Lean.Meta.Tactic.Generalize public import Lean.Elab.Binders public import Lean.Elab.Tactic.Location
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
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_generalizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_evalGeneralize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_evalGeneralize___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalGeneralize___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalGeneralize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalGeneralize___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_evalGeneralize___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalGeneralize___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalGeneralize___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalGeneralize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalGeneralize___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_evalGeneralize___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_evalGeneralize___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalGeneralize___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "generalize"};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(63, 25, 193, 30, 218, 249, 163, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalGeneralize"};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(213, 126, 48, 82, 104, 131, 103, 124)}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(40) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_11_ = lean_apply_9(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed(lean_object* v_x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(v_x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(lean_object* v_mvarId_23_, lean_object* v_x_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; 
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_34_, 0, v_x_24_);
lean_closure_set(v___f_34_, 1, v___y_25_);
lean_closure_set(v___f_34_, 2, v___y_26_);
lean_closure_set(v___f_34_, 3, v___y_27_);
lean_closure_set(v___f_34_, 4, v___y_28_);
v___x_35_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_23_, v___f_34_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_35_) == 0)
{
return v___x_35_;
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___boxed(lean_object* v_mvarId_44_, lean_object* v_x_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_mvarId_44_, v_x_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(lean_object* v_00_u03b1_56_, lean_object* v_mvarId_57_, lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_mvarId_57_, v_x_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___boxed(lean_object* v_00_u03b1_69_, lean_object* v_mvarId_70_, lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(v_00_u03b1_69_, v_mvarId_70_, v_x_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(lean_object* v_as_82_, size_t v_sz_83_, size_t v_i_84_, lean_object* v_b_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_usize_dec_lt(v_i_84_, v_sz_83_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v_b_85_);
return v___x_94_;
}
else
{
lean_object* v_array_95_; lean_object* v_start_96_; lean_object* v_stop_97_; uint8_t v___x_98_; 
v_array_95_ = lean_ctor_get(v_b_85_, 0);
v_start_96_ = lean_ctor_get(v_b_85_, 1);
v_stop_97_ = lean_ctor_get(v_b_85_, 2);
v___x_98_ = lean_nat_dec_lt(v_start_96_, v_stop_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v_b_85_);
return v___x_99_;
}
else
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_123_; 
lean_inc(v_stop_97_);
lean_inc(v_start_96_);
lean_inc_ref(v_array_95_);
v_isSharedCheck_123_ = !lean_is_exclusive(v_b_85_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; lean_object* v_unused_125_; lean_object* v_unused_126_; 
v_unused_124_ = lean_ctor_get(v_b_85_, 2);
lean_dec(v_unused_124_);
v_unused_125_ = lean_ctor_get(v_b_85_, 1);
lean_dec(v_unused_125_);
v_unused_126_ = lean_ctor_get(v_b_85_, 0);
lean_dec(v_unused_126_);
v___x_101_ = v_b_85_;
v_isShared_102_ = v_isSharedCheck_123_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_b_85_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_123_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_a_103_ = lean_array_uget_borrowed(v_as_82_, v_i_84_);
v___x_104_ = lean_array_fget_borrowed(v_array_95_, v_start_96_);
lean_inc(v_a_103_);
v___x_105_ = l_Lean_Expr_fvar___override(v_a_103_);
lean_inc(v___x_104_);
v___x_106_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_104_, v___x_105_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
lean_dec_ref_known(v___x_106_, 1);
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_nat_add(v_start_96_, v___x_107_);
lean_dec(v_start_96_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_108_);
v___x_110_ = v___x_101_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_array_95_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_stop_97_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
size_t v___x_111_; size_t v___x_112_; 
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_84_, v___x_111_);
v_i_84_ = v___x_112_;
v_b_85_ = v___x_110_;
goto _start;
}
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_del_object(v___x_101_);
lean_dec(v_stop_97_);
lean_dec(v_start_96_);
lean_dec_ref(v_array_95_);
v_a_115_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_106_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_106_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg___boxed(lean_object* v_as_127_, lean_object* v_sz_128_, lean_object* v_i_129_, lean_object* v_b_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
size_t v_sz_boxed_138_; size_t v_i_boxed_139_; lean_object* v_res_140_; 
v_sz_boxed_138_ = lean_unbox_usize(v_sz_128_);
lean_dec(v_sz_128_);
v_i_boxed_139_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_res_140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_127_, v_sz_boxed_138_, v_i_boxed_139_, v_b_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec_ref(v_as_127_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__0(lean_object* v_fst_141_, size_t v_sz_142_, size_t v___x_143_, lean_object* v___x_144_, lean_object* v_snd_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_fst_141_, v_sz_142_, v___x_143_, v___x_144_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec_ref_known(v___x_155_, 1);
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v_snd_145_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_157_, v___y_147_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_158_;
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec(v_snd_145_);
v_a_159_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_155_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_155_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__0___boxed(lean_object* v_fst_167_, lean_object* v_sz_168_, lean_object* v___x_169_, lean_object* v___x_170_, lean_object* v_snd_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
size_t v_sz_boxed_181_; size_t v___x_9316__boxed_182_; lean_object* v_res_183_; 
v_sz_boxed_181_ = lean_unbox_usize(v_sz_168_);
lean_dec(v_sz_168_);
v___x_9316__boxed_182_ = lean_unbox_usize(v___x_169_);
lean_dec(v___x_169_);
v_res_183_ = l_Lean_Elab_Tactic_evalGeneralize___lam__0(v_fst_167_, v_sz_boxed_181_, v___x_9316__boxed_182_, v___x_170_, v_snd_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec_ref(v_fst_167_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__1(lean_object* v_a_184_, lean_object* v_snd_185_, lean_object* v_hyps_186_, lean_object* v___x_187_, uint8_t v___x_188_, lean_object* v_fst_189_, lean_object* v_fst_190_, lean_object* v___x_191_, size_t v___x_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_MVarId_generalizeHyp(v_a_184_, v_snd_185_, v_hyps_186_, v___x_187_, v___x_188_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_snd_204_; lean_object* v_fst_205_; lean_object* v_snd_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; size_t v_sz_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___x_214_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_snd_204_ = lean_ctor_get(v_a_203_, 1);
lean_inc(v_snd_204_);
lean_dec(v_a_203_);
v_fst_205_ = lean_ctor_get(v_snd_204_, 0);
lean_inc(v_fst_205_);
v_snd_206_ = lean_ctor_get(v_snd_204_, 1);
lean_inc_n(v_snd_206_, 2);
lean_dec(v_snd_204_);
v___x_207_ = l_Array_append___redArg(v_fst_189_, v_fst_190_);
v___x_208_ = lean_array_get_size(v___x_207_);
v___x_209_ = l_Array_toSubarray___redArg(v___x_207_, v___x_191_, v___x_208_);
v_sz_210_ = lean_array_size(v_fst_205_);
v___x_211_ = lean_box_usize(v_sz_210_);
v___x_212_ = lean_box_usize(v___x_192_);
v___f_213_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lam__0___boxed), 14, 5);
lean_closure_set(v___f_213_, 0, v_fst_205_);
lean_closure_set(v___f_213_, 1, v___x_211_);
lean_closure_set(v___f_213_, 2, v___x_212_);
lean_closure_set(v___f_213_, 3, v___x_209_);
lean_closure_set(v___f_213_, 4, v_snd_206_);
v___x_214_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_snd_206_, v___f_213_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
return v___x_214_;
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v___x_191_);
lean_dec(v_fst_189_);
v_a_215_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_202_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_202_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed(lean_object** _args){
lean_object* v_a_223_ = _args[0];
lean_object* v_snd_224_ = _args[1];
lean_object* v_hyps_225_ = _args[2];
lean_object* v___x_226_ = _args[3];
lean_object* v___x_227_ = _args[4];
lean_object* v_fst_228_ = _args[5];
lean_object* v_fst_229_ = _args[6];
lean_object* v___x_230_ = _args[7];
lean_object* v___x_231_ = _args[8];
lean_object* v___y_232_ = _args[9];
lean_object* v___y_233_ = _args[10];
lean_object* v___y_234_ = _args[11];
lean_object* v___y_235_ = _args[12];
lean_object* v___y_236_ = _args[13];
lean_object* v___y_237_ = _args[14];
lean_object* v___y_238_ = _args[15];
lean_object* v___y_239_ = _args[16];
lean_object* v___y_240_ = _args[17];
_start:
{
uint8_t v___x_9381__boxed_241_; size_t v___x_9383__boxed_242_; lean_object* v_res_243_; 
v___x_9381__boxed_241_ = lean_unbox(v___x_227_);
v___x_9383__boxed_242_ = lean_unbox_usize(v___x_231_);
lean_dec(v___x_231_);
v_res_243_ = l_Lean_Elab_Tactic_evalGeneralize___lam__1(v_a_223_, v_snd_224_, v_hyps_225_, v___x_226_, v___x_9381__boxed_241_, v_fst_228_, v_fst_229_, v___x_230_, v___x_9383__boxed_242_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v_fst_229_);
lean_dec_ref(v_hyps_225_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(lean_object* v_as_244_, size_t v_sz_245_, size_t v_i_246_, lean_object* v_b_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = lean_usize_dec_lt(v_i_246_, v_sz_245_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_b_247_);
return v___x_258_;
}
else
{
lean_object* v_snd_259_; lean_object* v_fst_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_320_; 
v_snd_259_ = lean_ctor_get(v_b_247_, 1);
v_fst_260_ = lean_ctor_get(v_b_247_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_b_247_);
if (v_isSharedCheck_320_ == 0)
{
v___x_262_ = v_b_247_;
v_isShared_263_ = v_isSharedCheck_320_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_snd_259_);
lean_inc(v_fst_260_);
lean_dec(v_b_247_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_320_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_fst_264_; lean_object* v_snd_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_319_; 
v_fst_264_ = lean_ctor_get(v_snd_259_, 0);
v_snd_265_ = lean_ctor_get(v_snd_259_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_snd_259_);
if (v_isSharedCheck_319_ == 0)
{
v___x_267_ = v_snd_259_;
v_isShared_268_ = v_isSharedCheck_319_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_snd_265_);
lean_inc(v_fst_264_);
lean_dec(v_snd_259_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_319_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; lean_object* v_a_270_; lean_object* v_hName_x3f_272_; lean_object* v_hIdents_273_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v_a_270_ = lean_array_uget_borrowed(v_as_244_, v_i_246_);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = l_Lean_Syntax_getArg(v_a_270_, v___x_311_);
v___x_313_ = l_Lean_Syntax_isNone(v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = l_Lean_Syntax_getArg(v___x_312_, v___x_311_);
lean_dec(v___x_312_);
lean_inc(v___x_314_);
v___x_315_ = lean_array_push(v_fst_264_, v___x_314_);
v___x_316_ = l_Lean_Syntax_getId(v___x_314_);
lean_dec(v___x_314_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
v_hName_x3f_272_ = v___x_317_;
v_hIdents_273_ = v___x_315_;
v___y_274_ = v___y_248_;
v___y_275_ = v___y_249_;
v___y_276_ = v___y_250_;
v___y_277_ = v___y_251_;
v___y_278_ = v___y_252_;
v___y_279_ = v___y_253_;
v___y_280_ = v___y_254_;
v___y_281_ = v___y_255_;
goto v___jp_271_;
}
else
{
lean_object* v___x_318_; 
lean_dec(v___x_312_);
v___x_318_ = lean_box(0);
v_hName_x3f_272_ = v___x_318_;
v_hIdents_273_ = v_fst_264_;
v___y_274_ = v___y_248_;
v___y_275_ = v___y_249_;
v___y_276_ = v___y_250_;
v___y_277_ = v___y_251_;
v___y_278_ = v___y_252_;
v___y_279_ = v___y_253_;
v___y_280_ = v___y_254_;
v___y_281_ = v___y_255_;
goto v___jp_271_;
}
v___jp_271_:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; 
v___x_282_ = l_Lean_Syntax_getArg(v_a_270_, v___x_269_);
v___x_283_ = lean_box(0);
v___x_284_ = 0;
v___x_285_ = l_Lean_Elab_Tactic_elabTerm(v___x_282_, v___x_283_, v___x_284_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = lean_unsigned_to_nat(3u);
v___x_288_ = l_Lean_Syntax_getArg(v_a_270_, v___x_287_);
lean_inc(v___x_288_);
v___x_289_ = lean_array_push(v_fst_260_, v___x_288_);
v___x_290_ = l_Lean_Syntax_getId(v___x_288_);
lean_dec(v___x_288_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_292_, 0, v_a_286_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_ctor_set(v___x_292_, 2, v_hName_x3f_272_);
v___x_293_ = lean_array_push(v_snd_265_, v___x_292_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_293_);
lean_ctor_set(v___x_267_, 0, v_hIdents_273_);
v___x_295_ = v___x_267_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_hIdents_273_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_302_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_297_; 
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_295_);
lean_ctor_set(v___x_262_, 0, v___x_289_);
v___x_297_ = v___x_262_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_295_);
v___x_297_ = v_reuseFailAlloc_301_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
size_t v___x_298_; size_t v___x_299_; 
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_add(v_i_246_, v___x_298_);
v_i_246_ = v___x_299_;
v_b_247_ = v___x_297_;
goto _start;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_hIdents_273_);
lean_dec(v_hName_x3f_272_);
lean_del_object(v___x_267_);
lean_dec(v_snd_265_);
lean_del_object(v___x_262_);
lean_dec(v_fst_260_);
v_a_303_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_285_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_285_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0___boxed(lean_object* v_as_321_, lean_object* v_sz_322_, lean_object* v_i_323_, lean_object* v_b_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
size_t v_sz_boxed_334_; size_t v_i_boxed_335_; lean_object* v_res_336_; 
v_sz_boxed_334_ = lean_unbox_usize(v_sz_322_);
lean_dec(v_sz_322_);
v_i_boxed_335_ = lean_unbox_usize(v_i_323_);
lean_dec(v_i_323_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v_as_321_, v_sz_boxed_334_, v_i_boxed_335_, v_b_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec_ref(v_as_321_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(lean_object* v_as_337_, size_t v_sz_338_, size_t v_i_339_, lean_object* v_b_340_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_lt(v_i_339_, v_sz_338_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v_b_340_);
return v___x_343_;
}
else
{
lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_363_; 
v_snd_344_ = lean_ctor_get(v_b_340_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_b_340_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; 
v_unused_364_ = lean_ctor_get(v_b_340_, 0);
lean_dec(v_unused_364_);
v___x_346_ = v_b_340_;
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_dec(v_b_340_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v_a_350_; lean_object* v_a_357_; 
v___x_348_ = lean_box(0);
v_a_357_ = lean_array_uget_borrowed(v_as_337_, v_i_339_);
if (lean_obj_tag(v_a_357_) == 0)
{
v_a_350_ = v_snd_344_;
goto v___jp_349_;
}
else
{
lean_object* v_val_358_; uint8_t v___x_359_; uint8_t v___x_360_; 
v_val_358_ = lean_ctor_get(v_a_357_, 0);
v___x_359_ = l_Lean_LocalDecl_isImplementationDetail(v_val_358_);
v___x_360_ = lean_bool_not(v___x_359_);
if (v___x_360_ == 0)
{
v_a_350_ = v_snd_344_;
goto v___jp_349_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_inc(v_val_358_);
v___x_361_ = l_Lean_LocalDecl_toExpr(v_val_358_);
v___x_362_ = lean_array_push(v_snd_344_, v___x_361_);
v_a_350_ = v___x_362_;
goto v___jp_349_;
}
}
v___jp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_a_350_);
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_352_ = v___x_346_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_a_350_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
size_t v___x_353_; size_t v___x_354_; 
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_add(v_i_339_, v___x_353_);
v_i_339_ = v___x_354_;
v_b_340_ = v___x_352_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_as_365_, lean_object* v_sz_366_, lean_object* v_i_367_, lean_object* v_b_368_, lean_object* v___y_369_){
_start:
{
size_t v_sz_boxed_370_; size_t v_i_boxed_371_; lean_object* v_res_372_; 
v_sz_boxed_370_ = lean_unbox_usize(v_sz_366_);
lean_dec(v_sz_366_);
v_i_boxed_371_ = lean_unbox_usize(v_i_367_);
lean_dec(v_i_367_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_365_, v_sz_boxed_370_, v_i_boxed_371_, v_b_368_);
lean_dec_ref(v_as_365_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(lean_object* v_as_373_, size_t v_sz_374_, size_t v_i_375_, lean_object* v_b_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = lean_usize_dec_lt(v_i_375_, v_sz_374_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v_b_376_);
return v___x_387_;
}
else
{
lean_object* v_snd_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_407_; 
v_snd_388_ = lean_ctor_get(v_b_376_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_b_376_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v_b_376_, 0);
lean_dec(v_unused_408_);
v___x_390_ = v_b_376_;
v_isShared_391_ = v_isSharedCheck_407_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_snd_388_);
lean_dec(v_b_376_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_407_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v_a_394_; lean_object* v_a_401_; 
v___x_392_ = lean_box(0);
v_a_401_ = lean_array_uget_borrowed(v_as_373_, v_i_375_);
if (lean_obj_tag(v_a_401_) == 0)
{
v_a_394_ = v_snd_388_;
goto v___jp_393_;
}
else
{
lean_object* v_val_402_; uint8_t v___x_403_; uint8_t v___x_404_; 
v_val_402_ = lean_ctor_get(v_a_401_, 0);
v___x_403_ = l_Lean_LocalDecl_isImplementationDetail(v_val_402_);
v___x_404_ = lean_bool_not(v___x_403_);
if (v___x_404_ == 0)
{
v_a_394_ = v_snd_388_;
goto v___jp_393_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_inc(v_val_402_);
v___x_405_ = l_Lean_LocalDecl_toExpr(v_val_402_);
v___x_406_ = lean_array_push(v_snd_388_, v___x_405_);
v_a_394_ = v___x_406_;
goto v___jp_393_;
}
}
v___jp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v_a_394_);
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v_a_394_);
v___x_396_ = v_reuseFailAlloc_400_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_add(v_i_375_, v___x_397_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_373_, v_sz_374_, v___x_398_, v___x_396_);
return v___x_399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_as_409_, lean_object* v_sz_410_, lean_object* v_i_411_, lean_object* v_b_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
size_t v_sz_boxed_422_; size_t v_i_boxed_423_; lean_object* v_res_424_; 
v_sz_boxed_422_ = lean_unbox_usize(v_sz_410_);
lean_dec(v_sz_410_);
v_i_boxed_423_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_res_424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_as_409_, v_sz_boxed_422_, v_i_boxed_423_, v_b_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec_ref(v_as_409_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(lean_object* v_init_425_, lean_object* v_n_426_, lean_object* v_b_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
if (lean_obj_tag(v_n_426_) == 0)
{
lean_object* v_cs_437_; lean_object* v___x_438_; lean_object* v___x_439_; size_t v_sz_440_; size_t v___x_441_; lean_object* v___x_442_; 
v_cs_437_ = lean_ctor_get(v_n_426_, 0);
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_b_427_);
v_sz_440_ = lean_array_size(v_cs_437_);
v___x_441_ = ((size_t)0ULL);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_425_, v_cs_437_, v_sz_440_, v___x_441_, v___x_439_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_457_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_457_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_457_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_457_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_fst_447_; 
v_fst_447_ = lean_ctor_get(v_a_443_, 0);
if (lean_obj_tag(v_fst_447_) == 0)
{
lean_object* v_snd_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v_snd_448_ = lean_ctor_get(v_a_443_, 1);
lean_inc(v_snd_448_);
lean_dec(v_a_443_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v_snd_448_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_449_);
v___x_451_ = v___x_445_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
else
{
lean_object* v_val_453_; lean_object* v___x_455_; 
lean_inc_ref(v_fst_447_);
lean_dec(v_a_443_);
v_val_453_ = lean_ctor_get(v_fst_447_, 0);
lean_inc(v_val_453_);
lean_dec_ref_known(v_fst_447_, 1);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_val_453_);
v___x_455_ = v___x_445_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_val_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_442_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_442_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v_vs_466_; lean_object* v___x_467_; lean_object* v___x_468_; size_t v_sz_469_; size_t v___x_470_; lean_object* v___x_471_; 
v_vs_466_ = lean_ctor_get(v_n_426_, 0);
v___x_467_ = lean_box(0);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_b_427_);
v_sz_469_ = lean_array_size(v_vs_466_);
v___x_470_ = ((size_t)0ULL);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_vs_466_, v_sz_469_, v___x_470_, v___x_468_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_486_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_486_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_486_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_486_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v_fst_476_; 
v_fst_476_ = lean_ctor_get(v_a_472_, 0);
if (lean_obj_tag(v_fst_476_) == 0)
{
lean_object* v_snd_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v_snd_477_ = lean_ctor_get(v_a_472_, 1);
lean_inc(v_snd_477_);
lean_dec(v_a_472_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v_snd_477_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_478_);
v___x_480_ = v___x_474_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
lean_object* v_val_482_; lean_object* v___x_484_; 
lean_inc_ref(v_fst_476_);
lean_dec(v_a_472_);
v_val_482_ = lean_ctor_get(v_fst_476_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v_fst_476_, 1);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v_val_482_);
v___x_484_ = v___x_474_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_val_482_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_a_487_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_471_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_471_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(lean_object* v_init_495_, lean_object* v_as_496_, size_t v_sz_497_, size_t v_i_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_lt(v_i_498_, v_sz_497_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v_b_499_);
return v___x_510_;
}
else
{
lean_object* v_snd_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_545_; 
v_snd_511_ = lean_ctor_get(v_b_499_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_b_499_);
if (v_isSharedCheck_545_ == 0)
{
lean_object* v_unused_546_; 
v_unused_546_ = lean_ctor_get(v_b_499_, 0);
lean_dec(v_unused_546_);
v___x_513_ = v_b_499_;
v_isShared_514_ = v_isSharedCheck_545_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_snd_511_);
lean_dec(v_b_499_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_545_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_a_515_; lean_object* v___x_516_; 
v_a_515_ = lean_array_uget_borrowed(v_as_496_, v_i_498_);
lean_inc(v_snd_511_);
v___x_516_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_495_, v_a_515_, v_snd_511_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_536_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_536_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_536_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_536_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
if (lean_obj_tag(v_a_517_) == 0)
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_a_517_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_521_);
v___x_523_ = v___x_513_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_snd_511_);
v___x_523_ = v_reuseFailAlloc_527_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_523_);
v___x_525_ = v___x_519_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_del_object(v___x_519_);
lean_dec(v_snd_511_);
v_a_528_ = lean_ctor_get(v_a_517_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v_a_517_, 1);
v___x_529_ = lean_box(0);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_a_528_);
lean_ctor_set(v___x_513_, 0, v___x_529_);
v___x_531_ = v___x_513_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_a_528_);
v___x_531_ = v_reuseFailAlloc_535_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
size_t v___x_532_; size_t v___x_533_; 
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_498_, v___x_532_);
v_i_498_ = v___x_533_;
v_b_499_ = v___x_531_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_del_object(v___x_513_);
lean_dec(v_snd_511_);
v_a_537_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_516_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_516_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_init_547_, lean_object* v_as_548_, lean_object* v_sz_549_, lean_object* v_i_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
size_t v_sz_boxed_561_; size_t v_i_boxed_562_; lean_object* v_res_563_; 
v_sz_boxed_561_ = lean_unbox_usize(v_sz_549_);
lean_dec(v_sz_549_);
v_i_boxed_562_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_547_, v_as_548_, v_sz_boxed_561_, v_i_boxed_562_, v_b_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec_ref(v_as_548_);
lean_dec_ref(v_init_547_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4___boxed(lean_object* v_init_564_, lean_object* v_n_565_, lean_object* v_b_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_564_, v_n_565_, v_b_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_n_565_);
lean_dec_ref(v_init_564_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_as_577_, size_t v_sz_578_, size_t v_i_579_, lean_object* v_b_580_){
_start:
{
uint8_t v___x_582_; 
v___x_582_ = lean_usize_dec_lt(v_i_579_, v_sz_578_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v_b_580_);
return v___x_583_;
}
else
{
lean_object* v_snd_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_603_; 
v_snd_584_ = lean_ctor_get(v_b_580_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v_b_580_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v_b_580_, 0);
lean_dec(v_unused_604_);
v___x_586_ = v_b_580_;
v_isShared_587_ = v_isSharedCheck_603_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snd_584_);
lean_dec(v_b_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_603_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v_a_590_; lean_object* v_a_597_; 
v___x_588_ = lean_box(0);
v_a_597_ = lean_array_uget_borrowed(v_as_577_, v_i_579_);
if (lean_obj_tag(v_a_597_) == 0)
{
v_a_590_ = v_snd_584_;
goto v___jp_589_;
}
else
{
lean_object* v_val_598_; uint8_t v___x_599_; uint8_t v___x_600_; 
v_val_598_ = lean_ctor_get(v_a_597_, 0);
v___x_599_ = l_Lean_LocalDecl_isImplementationDetail(v_val_598_);
v___x_600_ = lean_bool_not(v___x_599_);
if (v___x_600_ == 0)
{
v_a_590_ = v_snd_584_;
goto v___jp_589_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_inc(v_val_598_);
v___x_601_ = l_Lean_LocalDecl_toExpr(v_val_598_);
v___x_602_ = lean_array_push(v_snd_584_, v___x_601_);
v_a_590_ = v___x_602_;
goto v___jp_589_;
}
}
v___jp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_a_590_);
lean_ctor_set(v___x_586_, 0, v___x_588_);
v___x_592_ = v___x_586_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_a_590_);
v___x_592_ = v_reuseFailAlloc_596_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
size_t v___x_593_; size_t v___x_594_; 
v___x_593_ = ((size_t)1ULL);
v___x_594_ = lean_usize_add(v_i_579_, v___x_593_);
v_i_579_ = v___x_594_;
v_b_580_ = v___x_592_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_as_605_, lean_object* v_sz_606_, lean_object* v_i_607_, lean_object* v_b_608_, lean_object* v___y_609_){
_start:
{
size_t v_sz_boxed_610_; size_t v_i_boxed_611_; lean_object* v_res_612_; 
v_sz_boxed_610_ = lean_unbox_usize(v_sz_606_);
lean_dec(v_sz_606_);
v_i_boxed_611_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_605_, v_sz_boxed_610_, v_i_boxed_611_, v_b_608_);
lean_dec_ref(v_as_605_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(lean_object* v_as_613_, size_t v_sz_614_, size_t v_i_615_, lean_object* v_b_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_615_, v_sz_614_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v_b_616_);
return v___x_627_;
}
else
{
lean_object* v_snd_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_647_; 
v_snd_628_ = lean_ctor_get(v_b_616_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_b_616_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v_b_616_, 0);
lean_dec(v_unused_648_);
v___x_630_ = v_b_616_;
v_isShared_631_ = v_isSharedCheck_647_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_snd_628_);
lean_dec(v_b_616_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_647_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v_a_634_; lean_object* v_a_641_; 
v___x_632_ = lean_box(0);
v_a_641_ = lean_array_uget_borrowed(v_as_613_, v_i_615_);
if (lean_obj_tag(v_a_641_) == 0)
{
v_a_634_ = v_snd_628_;
goto v___jp_633_;
}
else
{
lean_object* v_val_642_; uint8_t v___x_643_; uint8_t v___x_644_; 
v_val_642_ = lean_ctor_get(v_a_641_, 0);
v___x_643_ = l_Lean_LocalDecl_isImplementationDetail(v_val_642_);
v___x_644_ = lean_bool_not(v___x_643_);
if (v___x_644_ == 0)
{
v_a_634_ = v_snd_628_;
goto v___jp_633_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_inc(v_val_642_);
v___x_645_ = l_Lean_LocalDecl_toExpr(v_val_642_);
v___x_646_ = lean_array_push(v_snd_628_, v___x_645_);
v_a_634_ = v___x_646_;
goto v___jp_633_;
}
}
v___jp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v_a_634_);
lean_ctor_set(v___x_630_, 0, v___x_632_);
v___x_636_ = v___x_630_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_a_634_);
v___x_636_ = v_reuseFailAlloc_640_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_i_615_, v___x_637_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_613_, v_sz_614_, v___x_638_, v___x_636_);
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5___boxed(lean_object* v_as_649_, lean_object* v_sz_650_, lean_object* v_i_651_, lean_object* v_b_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_662_ = lean_unbox_usize(v_sz_650_);
lean_dec(v_sz_650_);
v_i_boxed_663_ = lean_unbox_usize(v_i_651_);
lean_dec(v_i_651_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_as_649_, v_sz_boxed_662_, v_i_boxed_663_, v_b_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec_ref(v_as_649_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(lean_object* v_t_665_, lean_object* v_init_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_root_676_; lean_object* v_tail_677_; lean_object* v___x_678_; 
v_root_676_ = lean_ctor_get(v_t_665_, 0);
v_tail_677_ = lean_ctor_get(v_t_665_, 1);
lean_inc_ref(v_init_666_);
v___x_678_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_666_, v_root_676_, v_init_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec_ref(v_init_666_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_715_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_715_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_715_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_715_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
if (lean_obj_tag(v_a_679_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; 
v_a_683_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v_a_679_, 1);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v_a_683_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_689_; size_t v_sz_690_; size_t v___x_691_; lean_object* v___x_692_; 
lean_del_object(v___x_681_);
v_a_687_ = lean_ctor_get(v_a_679_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v_a_679_, 1);
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_a_687_);
v_sz_690_ = lean_array_size(v_tail_677_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_tail_677_, v_sz_690_, v___x_691_, v___x_689_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_706_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_706_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_697_; 
v_fst_697_ = lean_ctor_get(v_a_693_, 0);
if (lean_obj_tag(v_fst_697_) == 0)
{
lean_object* v_snd_698_; lean_object* v___x_700_; 
v_snd_698_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_snd_698_);
lean_dec(v_a_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_snd_698_);
v___x_700_ = v___x_695_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_snd_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
lean_object* v_val_702_; lean_object* v___x_704_; 
lean_inc_ref(v_fst_697_);
lean_dec(v_a_693_);
v_val_702_ = lean_ctor_get(v_fst_697_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v_fst_697_, 1);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_val_702_);
v___x_704_ = v___x_695_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_val_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_692_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_692_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
v_a_716_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_678_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_678_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3___boxed(lean_object* v_t_724_, lean_object* v_init_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_t_724_, v_init_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec_ref(v_t_724_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_lctx_747_; lean_object* v_decls_748_; lean_object* v_hs_749_; lean_object* v___x_750_; 
v_lctx_747_ = lean_ctor_get(v___y_742_, 2);
v_decls_748_ = lean_ctor_get(v_lctx_747_, 1);
v_hs_749_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0));
v___x_750_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_decls_748_, v_hs_749_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___boxed(lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(size_t v_sz_761_, size_t v_i_762_, lean_object* v_bs_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_lt(v_i_762_, v_sz_761_);
if (v___x_764_ == 0)
{
return v_bs_763_;
}
else
{
lean_object* v_v_765_; lean_object* v___x_766_; lean_object* v_bs_x27_767_; lean_object* v___x_768_; size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v_v_765_ = lean_array_uget(v_bs_763_, v_i_762_);
v___x_766_ = lean_unsigned_to_nat(0u);
v_bs_x27_767_ = lean_array_uset(v_bs_763_, v_i_762_, v___x_766_);
v___x_768_ = l_Lean_Expr_fvarId_x21(v_v_765_);
lean_dec(v_v_765_);
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_add(v_i_762_, v___x_769_);
v___x_771_ = lean_array_uset(v_bs_x27_767_, v_i_762_, v___x_768_);
v_i_762_ = v___x_770_;
v_bs_763_ = v___x_771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4___boxed(lean_object* v_sz_773_, lean_object* v_i_774_, lean_object* v_bs_775_){
_start:
{
size_t v_sz_boxed_776_; size_t v_i_boxed_777_; lean_object* v_res_778_; 
v_sz_boxed_776_ = lean_unbox_usize(v_sz_773_);
lean_dec(v_sz_773_);
v_i_boxed_777_ = lean_unbox_usize(v_i_774_);
lean_dec(v_i_774_);
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_boxed_776_, v_i_boxed_777_, v_bs_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__2(lean_object* v___x_779_, size_t v_sz_780_, size_t v___x_781_, lean_object* v___x_782_, lean_object* v___x_783_, lean_object* v_stx_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v___x_779_, v_sz_780_, v___x_781_, v___x_782_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v_snd_796_; lean_object* v_fst_797_; lean_object* v_fst_798_; lean_object* v_snd_799_; lean_object* v_hyps_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v_snd_796_ = lean_ctor_get(v_a_795_, 1);
lean_inc(v_snd_796_);
v_fst_797_ = lean_ctor_get(v_a_795_, 0);
lean_inc(v_fst_797_);
lean_dec(v_a_795_);
v_fst_798_ = lean_ctor_get(v_snd_796_, 0);
lean_inc(v_fst_798_);
v_snd_799_ = lean_ctor_get(v_snd_796_, 1);
lean_inc(v_snd_799_);
lean_dec(v_snd_796_);
v___x_826_ = lean_unsigned_to_nat(2u);
v___x_827_ = l_Lean_Syntax_getArg(v_stx_784_, v___x_826_);
v___x_828_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_827_);
lean_dec(v___x_827_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; size_t v_sz_831_; lean_object* v___x_832_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v_sz_831_ = lean_array_size(v_a_830_);
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_831_, v___x_781_, v_a_830_);
v_hyps_801_ = v___x_832_;
v___y_802_ = v___y_785_;
v___y_803_ = v___y_786_;
v___y_804_ = v___y_787_;
v___y_805_ = v___y_788_;
v___y_806_ = v___y_789_;
v___y_807_ = v___y_790_;
v___y_808_ = v___y_791_;
v___y_809_ = v___y_792_;
goto v___jp_800_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_snd_799_);
lean_dec(v_fst_798_);
lean_dec(v_fst_797_);
lean_dec(v___x_783_);
v_a_833_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_829_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_hypotheses_841_; lean_object* v___x_842_; 
v_hypotheses_841_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_hypotheses_841_);
lean_dec_ref_known(v___x_828_, 1);
v___x_842_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_841_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v_hyps_801_ = v_a_843_;
v___y_802_ = v___y_785_;
v___y_803_ = v___y_786_;
v___y_804_ = v___y_787_;
v___y_805_ = v___y_788_;
v___y_806_ = v___y_789_;
v___y_807_ = v___y_790_;
v___y_808_ = v___y_791_;
v___y_809_ = v___y_792_;
goto v___jp_800_;
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_snd_799_);
lean_dec(v_fst_798_);
lean_dec(v_fst_797_);
lean_dec(v___x_783_);
v_a_844_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
v___jp_800_:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_803_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___f_816_; lean_object* v___x_817_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc_n(v_a_811_, 2);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = lean_box(0);
v___x_813_ = 3;
v___x_814_ = lean_box(v___x_813_);
v___x_815_ = lean_box_usize(v___x_781_);
v___f_816_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed), 18, 9);
lean_closure_set(v___f_816_, 0, v_a_811_);
lean_closure_set(v___f_816_, 1, v_snd_799_);
lean_closure_set(v___f_816_, 2, v_hyps_801_);
lean_closure_set(v___f_816_, 3, v___x_812_);
lean_closure_set(v___f_816_, 4, v___x_814_);
lean_closure_set(v___f_816_, 5, v_fst_797_);
lean_closure_set(v___f_816_, 6, v_fst_798_);
lean_closure_set(v___f_816_, 7, v___x_783_);
lean_closure_set(v___f_816_, 8, v___x_815_);
v___x_817_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_a_811_, v___f_816_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
return v___x_817_;
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref(v_hyps_801_);
lean_dec(v_snd_799_);
lean_dec(v_fst_798_);
lean_dec(v_fst_797_);
lean_dec(v___x_783_);
v_a_818_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_810_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_810_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v___x_783_);
v_a_852_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_794_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_794_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed(lean_object* v___x_860_, lean_object* v_sz_861_, lean_object* v___x_862_, lean_object* v___x_863_, lean_object* v___x_864_, lean_object* v_stx_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
size_t v_sz_boxed_875_; size_t v___x_10221__boxed_876_; lean_object* v_res_877_; 
v_sz_boxed_875_ = lean_unbox_usize(v_sz_861_);
lean_dec(v_sz_861_);
v___x_10221__boxed_876_ = lean_unbox_usize(v___x_862_);
lean_dec(v___x_862_);
v_res_877_ = l_Lean_Elab_Tactic_evalGeneralize___lam__2(v___x_860_, v_sz_boxed_875_, v___x_10221__boxed_876_, v___x_863_, v___x_864_, v_stx_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v_stx_865_);
lean_dec_ref(v___x_860_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize(lean_object* v_stx_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; size_t v_sz_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___f_905_; lean_object* v___x_906_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = l_Lean_Syntax_getArg(v_stx_887_, v___x_898_);
v___x_900_ = l_Lean_Syntax_getSepArgs(v___x_899_);
lean_dec(v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_Elab_Tactic_evalGeneralize___closed__2));
v_sz_902_ = lean_array_size(v___x_900_);
v___x_903_ = lean_box_usize(v_sz_902_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1));
v___f_905_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed), 15, 6);
lean_closure_set(v___f_905_, 0, v___x_900_);
lean_closure_set(v___f_905_, 1, v___x_903_);
lean_closure_set(v___f_905_, 2, v___x_904_);
lean_closure_set(v___f_905_, 3, v___x_901_);
lean_closure_set(v___f_905_, 4, v___x_897_);
lean_closure_set(v___f_905_, 5, v_stx_887_);
v___x_906_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_905_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___boxed(lean_object* v_stx_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Elab_Tactic_evalGeneralize(v_stx_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(lean_object* v_as_918_, size_t v_sz_919_, size_t v_i_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_918_, v_sz_919_, v_i_920_, v_b_921_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___boxed(lean_object* v_as_932_, lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
size_t v_sz_boxed_945_; size_t v_i_boxed_946_; lean_object* v_res_947_; 
v_sz_boxed_945_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_946_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(v_as_932_, v_sz_boxed_945_, v_i_boxed_946_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v_as_932_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(lean_object* v_as_948_, size_t v_sz_949_, size_t v_i_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_948_, v_sz_949_, v_i_950_, v_b_951_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___boxed(lean_object* v_as_962_, lean_object* v_sz_963_, lean_object* v_i_964_, lean_object* v_b_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
size_t v_sz_boxed_975_; size_t v_i_boxed_976_; lean_object* v_res_977_; 
v_sz_boxed_975_ = lean_unbox_usize(v_sz_963_);
lean_dec(v_sz_963_);
v_i_boxed_976_ = lean_unbox_usize(v_i_964_);
lean_dec(v_i_964_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(v_as_962_, v_sz_boxed_975_, v_i_boxed_976_, v_b_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_as_962_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_as_978_, size_t v_sz_979_, size_t v_i_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_978_, v_sz_979_, v_i_980_, v_b_981_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_as_992_, lean_object* v_sz_993_, lean_object* v_i_994_, lean_object* v_b_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
size_t v_sz_boxed_1005_; size_t v_i_boxed_1006_; lean_object* v_res_1007_; 
v_sz_boxed_1005_ = lean_unbox_usize(v_sz_993_);
lean_dec(v_sz_993_);
v_i_boxed_1006_ = lean_unbox_usize(v_i_994_);
lean_dec(v_i_994_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(v_as_992_, v_sz_boxed_1005_, v_i_boxed_1006_, v_b_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec_ref(v_as_992_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1(){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1025_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1026_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4));
v___x_1027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7));
v___x_1028_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___boxed), 10, 0);
v___x_1029_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1025_, v___x_1026_, v___x_1027_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___boxed(lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3(){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7));
v___x_1059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6));
v___x_1060_ = l_Lean_addBuiltinDeclarationRanges(v___x_1058_, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___boxed(lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
return v_res_1062_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Generalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Generalize(builtin);
}
#ifdef __cplusplus
}
#endif
