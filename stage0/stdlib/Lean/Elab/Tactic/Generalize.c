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
lean_dec_ref(v___x_106_);
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
lean_dec_ref(v___x_155_);
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
size_t v_sz_boxed_181_; size_t v___x_9298__boxed_182_; lean_object* v_res_183_; 
v_sz_boxed_181_ = lean_unbox_usize(v_sz_168_);
lean_dec(v_sz_168_);
v___x_9298__boxed_182_ = lean_unbox_usize(v___x_169_);
lean_dec(v___x_169_);
v_res_183_ = l_Lean_Elab_Tactic_evalGeneralize___lam__0(v_fst_167_, v_sz_boxed_181_, v___x_9298__boxed_182_, v___x_170_, v_snd_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
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
lean_dec_ref(v___x_202_);
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
uint8_t v___x_9363__boxed_241_; size_t v___x_9365__boxed_242_; lean_object* v_res_243_; 
v___x_9363__boxed_241_ = lean_unbox(v___x_227_);
v___x_9365__boxed_242_ = lean_unbox_usize(v___x_231_);
lean_dec(v___x_231_);
v_res_243_ = l_Lean_Elab_Tactic_evalGeneralize___lam__1(v_a_223_, v_snd_224_, v_hyps_225_, v___x_226_, v___x_9363__boxed_241_, v_fst_228_, v_fst_229_, v___x_230_, v___x_9365__boxed_242_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
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
lean_dec_ref(v___x_285_);
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
lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_362_; 
v_snd_344_ = lean_ctor_get(v_b_340_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_b_340_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v_b_340_, 0);
lean_dec(v_unused_363_);
v___x_346_ = v_b_340_;
v_isShared_347_ = v_isSharedCheck_362_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_dec(v_b_340_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_362_;
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
lean_object* v_val_358_; uint8_t v___x_359_; 
v_val_358_ = lean_ctor_get(v_a_357_, 0);
v___x_359_ = l_Lean_LocalDecl_isImplementationDetail(v_val_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_inc(v_val_358_);
v___x_360_ = l_Lean_LocalDecl_toExpr(v_val_358_);
v___x_361_ = lean_array_push(v_snd_344_, v___x_360_);
v_a_350_ = v___x_361_;
goto v___jp_349_;
}
else
{
v_a_350_ = v_snd_344_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_as_364_, lean_object* v_sz_365_, lean_object* v_i_366_, lean_object* v_b_367_, lean_object* v___y_368_){
_start:
{
size_t v_sz_boxed_369_; size_t v_i_boxed_370_; lean_object* v_res_371_; 
v_sz_boxed_369_ = lean_unbox_usize(v_sz_365_);
lean_dec(v_sz_365_);
v_i_boxed_370_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_364_, v_sz_boxed_369_, v_i_boxed_370_, v_b_367_);
lean_dec_ref(v_as_364_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(lean_object* v_as_372_, size_t v_sz_373_, size_t v_i_374_, lean_object* v_b_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_lt(v_i_374_, v_sz_373_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_b_375_);
return v___x_386_;
}
else
{
lean_object* v_snd_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_405_; 
v_snd_387_ = lean_ctor_get(v_b_375_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_b_375_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v_b_375_, 0);
lean_dec(v_unused_406_);
v___x_389_ = v_b_375_;
v_isShared_390_ = v_isSharedCheck_405_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snd_387_);
lean_dec(v_b_375_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_405_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v_a_393_; lean_object* v_a_400_; 
v___x_391_ = lean_box(0);
v_a_400_ = lean_array_uget_borrowed(v_as_372_, v_i_374_);
if (lean_obj_tag(v_a_400_) == 0)
{
v_a_393_ = v_snd_387_;
goto v___jp_392_;
}
else
{
lean_object* v_val_401_; uint8_t v___x_402_; 
v_val_401_ = lean_ctor_get(v_a_400_, 0);
v___x_402_ = l_Lean_LocalDecl_isImplementationDetail(v_val_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_inc(v_val_401_);
v___x_403_ = l_Lean_LocalDecl_toExpr(v_val_401_);
v___x_404_ = lean_array_push(v_snd_387_, v___x_403_);
v_a_393_ = v___x_404_;
goto v___jp_392_;
}
else
{
v_a_393_ = v_snd_387_;
goto v___jp_392_;
}
}
v___jp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v_a_393_);
lean_ctor_set(v___x_389_, 0, v___x_391_);
v___x_395_ = v___x_389_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_a_393_);
v___x_395_ = v_reuseFailAlloc_399_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_add(v_i_374_, v___x_396_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_372_, v_sz_373_, v___x_397_, v___x_395_);
return v___x_398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_as_407_, lean_object* v_sz_408_, lean_object* v_i_409_, lean_object* v_b_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
size_t v_sz_boxed_420_; size_t v_i_boxed_421_; lean_object* v_res_422_; 
v_sz_boxed_420_ = lean_unbox_usize(v_sz_408_);
lean_dec(v_sz_408_);
v_i_boxed_421_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_as_407_, v_sz_boxed_420_, v_i_boxed_421_, v_b_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec_ref(v_as_407_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(lean_object* v_init_423_, lean_object* v_n_424_, lean_object* v_b_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
if (lean_obj_tag(v_n_424_) == 0)
{
lean_object* v_cs_435_; lean_object* v___x_436_; lean_object* v___x_437_; size_t v_sz_438_; size_t v___x_439_; lean_object* v___x_440_; 
v_cs_435_ = lean_ctor_get(v_n_424_, 0);
v___x_436_ = lean_box(0);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v_b_425_);
v_sz_438_ = lean_array_size(v_cs_435_);
v___x_439_ = ((size_t)0ULL);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_423_, v_cs_435_, v_sz_438_, v___x_439_, v___x_437_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_455_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_455_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_455_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_455_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_fst_445_; 
v_fst_445_ = lean_ctor_get(v_a_441_, 0);
if (lean_obj_tag(v_fst_445_) == 0)
{
lean_object* v_snd_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v_snd_446_ = lean_ctor_get(v_a_441_, 1);
lean_inc(v_snd_446_);
lean_dec(v_a_441_);
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_snd_446_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_447_);
v___x_449_ = v___x_443_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
lean_object* v_val_451_; lean_object* v___x_453_; 
lean_inc_ref(v_fst_445_);
lean_dec(v_a_441_);
v_val_451_ = lean_ctor_get(v_fst_445_, 0);
lean_inc(v_val_451_);
lean_dec_ref(v_fst_445_);
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_val_451_);
v___x_453_ = v___x_443_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_val_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_440_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_440_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_vs_464_; lean_object* v___x_465_; lean_object* v___x_466_; size_t v_sz_467_; size_t v___x_468_; lean_object* v___x_469_; 
v_vs_464_ = lean_ctor_get(v_n_424_, 0);
v___x_465_ = lean_box(0);
v___x_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_b_425_);
v_sz_467_ = lean_array_size(v_vs_464_);
v___x_468_ = ((size_t)0ULL);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_vs_464_, v_sz_467_, v___x_468_, v___x_466_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_484_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_484_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_484_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_484_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_fst_474_; 
v_fst_474_ = lean_ctor_get(v_a_470_, 0);
if (lean_obj_tag(v_fst_474_) == 0)
{
lean_object* v_snd_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v_snd_475_ = lean_ctor_get(v_a_470_, 1);
lean_inc(v_snd_475_);
lean_dec(v_a_470_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v_snd_475_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_476_);
v___x_478_ = v___x_472_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
lean_object* v_val_480_; lean_object* v___x_482_; 
lean_inc_ref(v_fst_474_);
lean_dec(v_a_470_);
v_val_480_ = lean_ctor_get(v_fst_474_, 0);
lean_inc(v_val_480_);
lean_dec_ref(v_fst_474_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v_val_480_);
v___x_482_ = v___x_472_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_val_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_a_485_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_469_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_469_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(lean_object* v_init_493_, lean_object* v_as_494_, size_t v_sz_495_, size_t v_i_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_496_, v_sz_495_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_b_497_);
return v___x_508_;
}
else
{
lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_543_; 
v_snd_509_ = lean_ctor_get(v_b_497_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v_b_497_);
if (v_isSharedCheck_543_ == 0)
{
lean_object* v_unused_544_; 
v_unused_544_ = lean_ctor_get(v_b_497_, 0);
lean_dec(v_unused_544_);
v___x_511_ = v_b_497_;
v_isShared_512_ = v_isSharedCheck_543_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_dec(v_b_497_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_543_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_513_ = lean_array_uget_borrowed(v_as_494_, v_i_496_);
lean_inc(v_snd_509_);
v___x_514_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_493_, v_a_513_, v_snd_509_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_534_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_534_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_534_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_534_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
if (lean_obj_tag(v_a_515_) == 0)
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v_a_515_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_519_);
v___x_521_ = v___x_511_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_snd_509_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_521_);
v___x_523_ = v___x_517_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
lean_del_object(v___x_517_);
lean_dec(v_snd_509_);
v_a_526_ = lean_ctor_get(v_a_515_, 0);
lean_inc(v_a_526_);
lean_dec_ref(v_a_515_);
v___x_527_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_a_526_);
lean_ctor_set(v___x_511_, 0, v___x_527_);
v___x_529_ = v___x_511_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_a_526_);
v___x_529_ = v_reuseFailAlloc_533_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
size_t v___x_530_; size_t v___x_531_; 
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_496_, v___x_530_);
v_i_496_ = v___x_531_;
v_b_497_ = v___x_529_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_del_object(v___x_511_);
lean_dec(v_snd_509_);
v_a_535_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_514_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_514_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_init_545_, lean_object* v_as_546_, lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_b_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
size_t v_sz_boxed_559_; size_t v_i_boxed_560_; lean_object* v_res_561_; 
v_sz_boxed_559_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_560_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_545_, v_as_546_, v_sz_boxed_559_, v_i_boxed_560_, v_b_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_as_546_);
lean_dec_ref(v_init_545_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4___boxed(lean_object* v_init_562_, lean_object* v_n_563_, lean_object* v_b_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_562_, v_n_563_, v_b_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec_ref(v_n_563_);
lean_dec_ref(v_init_562_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_as_575_, size_t v_sz_576_, size_t v_i_577_, lean_object* v_b_578_){
_start:
{
uint8_t v___x_580_; 
v___x_580_ = lean_usize_dec_lt(v_i_577_, v_sz_576_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v_b_578_);
return v___x_581_;
}
else
{
lean_object* v_snd_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_600_; 
v_snd_582_ = lean_ctor_get(v_b_578_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_b_578_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; 
v_unused_601_ = lean_ctor_get(v_b_578_, 0);
lean_dec(v_unused_601_);
v___x_584_ = v_b_578_;
v_isShared_585_ = v_isSharedCheck_600_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_snd_582_);
lean_dec(v_b_578_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_600_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v_a_588_; lean_object* v_a_595_; 
v___x_586_ = lean_box(0);
v_a_595_ = lean_array_uget_borrowed(v_as_575_, v_i_577_);
if (lean_obj_tag(v_a_595_) == 0)
{
v_a_588_ = v_snd_582_;
goto v___jp_587_;
}
else
{
lean_object* v_val_596_; uint8_t v___x_597_; 
v_val_596_ = lean_ctor_get(v_a_595_, 0);
v___x_597_ = l_Lean_LocalDecl_isImplementationDetail(v_val_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_inc(v_val_596_);
v___x_598_ = l_Lean_LocalDecl_toExpr(v_val_596_);
v___x_599_ = lean_array_push(v_snd_582_, v___x_598_);
v_a_588_ = v___x_599_;
goto v___jp_587_;
}
else
{
v_a_588_ = v_snd_582_;
goto v___jp_587_;
}
}
v___jp_587_:
{
lean_object* v___x_590_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 1, v_a_588_);
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_590_ = v___x_584_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_588_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
size_t v___x_591_; size_t v___x_592_; 
v___x_591_ = ((size_t)1ULL);
v___x_592_ = lean_usize_add(v_i_577_, v___x_591_);
v_i_577_ = v___x_592_;
v_b_578_ = v___x_590_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_as_602_, lean_object* v_sz_603_, lean_object* v_i_604_, lean_object* v_b_605_, lean_object* v___y_606_){
_start:
{
size_t v_sz_boxed_607_; size_t v_i_boxed_608_; lean_object* v_res_609_; 
v_sz_boxed_607_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v_i_boxed_608_ = lean_unbox_usize(v_i_604_);
lean_dec(v_i_604_);
v_res_609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_602_, v_sz_boxed_607_, v_i_boxed_608_, v_b_605_);
lean_dec_ref(v_as_602_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(lean_object* v_as_610_, size_t v_sz_611_, size_t v_i_612_, lean_object* v_b_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
uint8_t v___x_623_; 
v___x_623_ = lean_usize_dec_lt(v_i_612_, v_sz_611_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_b_613_);
return v___x_624_;
}
else
{
lean_object* v_snd_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_643_; 
v_snd_625_ = lean_ctor_get(v_b_613_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_b_613_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v_b_613_, 0);
lean_dec(v_unused_644_);
v___x_627_ = v_b_613_;
v_isShared_628_ = v_isSharedCheck_643_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_snd_625_);
lean_dec(v_b_613_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_643_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v_a_631_; lean_object* v_a_638_; 
v___x_629_ = lean_box(0);
v_a_638_ = lean_array_uget_borrowed(v_as_610_, v_i_612_);
if (lean_obj_tag(v_a_638_) == 0)
{
v_a_631_ = v_snd_625_;
goto v___jp_630_;
}
else
{
lean_object* v_val_639_; uint8_t v___x_640_; 
v_val_639_ = lean_ctor_get(v_a_638_, 0);
v___x_640_ = l_Lean_LocalDecl_isImplementationDetail(v_val_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_inc(v_val_639_);
v___x_641_ = l_Lean_LocalDecl_toExpr(v_val_639_);
v___x_642_ = lean_array_push(v_snd_625_, v___x_641_);
v_a_631_ = v___x_642_;
goto v___jp_630_;
}
else
{
v_a_631_ = v_snd_625_;
goto v___jp_630_;
}
}
v___jp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_a_631_);
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_633_ = v___x_627_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_a_631_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_add(v_i_612_, v___x_634_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_610_, v_sz_611_, v___x_635_, v___x_633_);
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5___boxed(lean_object* v_as_645_, lean_object* v_sz_646_, lean_object* v_i_647_, lean_object* v_b_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
size_t v_sz_boxed_658_; size_t v_i_boxed_659_; lean_object* v_res_660_; 
v_sz_boxed_658_ = lean_unbox_usize(v_sz_646_);
lean_dec(v_sz_646_);
v_i_boxed_659_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_as_645_, v_sz_boxed_658_, v_i_boxed_659_, v_b_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v_as_645_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(lean_object* v_t_661_, lean_object* v_init_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_root_672_; lean_object* v_tail_673_; lean_object* v___x_674_; 
v_root_672_ = lean_ctor_get(v_t_661_, 0);
v_tail_673_ = lean_ctor_get(v_t_661_, 1);
lean_inc_ref(v_init_662_);
v___x_674_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_662_, v_root_672_, v_init_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec_ref(v_init_662_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_711_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_711_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_711_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_711_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
if (lean_obj_tag(v_a_675_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; 
v_a_679_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_a_679_);
lean_dec_ref(v_a_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v_a_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_684_; lean_object* v___x_685_; size_t v_sz_686_; size_t v___x_687_; lean_object* v___x_688_; 
lean_del_object(v___x_677_);
v_a_683_ = lean_ctor_get(v_a_675_, 0);
lean_inc(v_a_683_);
lean_dec_ref(v_a_675_);
v___x_684_ = lean_box(0);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v_a_683_);
v_sz_686_ = lean_array_size(v_tail_673_);
v___x_687_ = ((size_t)0ULL);
v___x_688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_tail_673_, v_sz_686_, v___x_687_, v___x_685_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_702_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_702_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_702_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_702_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_fst_693_; 
v_fst_693_ = lean_ctor_get(v_a_689_, 0);
if (lean_obj_tag(v_fst_693_) == 0)
{
lean_object* v_snd_694_; lean_object* v___x_696_; 
v_snd_694_ = lean_ctor_get(v_a_689_, 1);
lean_inc(v_snd_694_);
lean_dec(v_a_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v_snd_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_snd_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v_val_698_; lean_object* v___x_700_; 
lean_inc_ref(v_fst_693_);
lean_dec(v_a_689_);
v_val_698_ = lean_ctor_get(v_fst_693_, 0);
lean_inc(v_val_698_);
lean_dec_ref(v_fst_693_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v_val_698_);
v___x_700_ = v___x_691_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_val_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_688_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_688_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v_a_712_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_674_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_674_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3___boxed(lean_object* v_t_720_, lean_object* v_init_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_t_720_, v_init_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec_ref(v_t_720_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_lctx_743_; lean_object* v_decls_744_; lean_object* v_hs_745_; lean_object* v___x_746_; 
v_lctx_743_ = lean_ctor_get(v___y_738_, 2);
v_decls_744_ = lean_ctor_get(v_lctx_743_, 1);
v_hs_745_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0));
v___x_746_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_decls_744_, v_hs_745_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___boxed(lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(size_t v_sz_757_, size_t v_i_758_, lean_object* v_bs_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_760_ == 0)
{
return v_bs_759_;
}
else
{
lean_object* v_v_761_; lean_object* v___x_762_; lean_object* v_bs_x27_763_; lean_object* v___x_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v_v_761_ = lean_array_uget(v_bs_759_, v_i_758_);
v___x_762_ = lean_unsigned_to_nat(0u);
v_bs_x27_763_ = lean_array_uset(v_bs_759_, v_i_758_, v___x_762_);
v___x_764_ = l_Lean_Expr_fvarId_x21(v_v_761_);
lean_dec(v_v_761_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_758_, v___x_765_);
v___x_767_ = lean_array_uset(v_bs_x27_763_, v_i_758_, v___x_764_);
v_i_758_ = v___x_766_;
v_bs_759_ = v___x_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4___boxed(lean_object* v_sz_769_, lean_object* v_i_770_, lean_object* v_bs_771_){
_start:
{
size_t v_sz_boxed_772_; size_t v_i_boxed_773_; lean_object* v_res_774_; 
v_sz_boxed_772_ = lean_unbox_usize(v_sz_769_);
lean_dec(v_sz_769_);
v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_boxed_772_, v_i_boxed_773_, v_bs_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__2(lean_object* v___x_775_, size_t v_sz_776_, size_t v___x_777_, lean_object* v___x_778_, lean_object* v___x_779_, lean_object* v_stx_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v___x_775_, v_sz_776_, v___x_777_, v___x_778_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v_snd_792_; lean_object* v_fst_793_; lean_object* v_fst_794_; lean_object* v_snd_795_; lean_object* v_hyps_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref(v___x_790_);
v_snd_792_ = lean_ctor_get(v_a_791_, 1);
lean_inc(v_snd_792_);
v_fst_793_ = lean_ctor_get(v_a_791_, 0);
lean_inc(v_fst_793_);
lean_dec(v_a_791_);
v_fst_794_ = lean_ctor_get(v_snd_792_, 0);
lean_inc(v_fst_794_);
v_snd_795_ = lean_ctor_get(v_snd_792_, 1);
lean_inc(v_snd_795_);
lean_dec(v_snd_792_);
v___x_822_ = lean_unsigned_to_nat(2u);
v___x_823_ = l_Lean_Syntax_getArg(v_stx_780_, v___x_822_);
v___x_824_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_823_);
lean_dec(v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; size_t v_sz_827_; lean_object* v___x_828_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref(v___x_825_);
v_sz_827_ = lean_array_size(v_a_826_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_827_, v___x_777_, v_a_826_);
v_hyps_797_ = v___x_828_;
v___y_798_ = v___y_781_;
v___y_799_ = v___y_782_;
v___y_800_ = v___y_783_;
v___y_801_ = v___y_784_;
v___y_802_ = v___y_785_;
v___y_803_ = v___y_786_;
v___y_804_ = v___y_787_;
v___y_805_ = v___y_788_;
goto v___jp_796_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_dec(v_fst_793_);
lean_dec(v___x_779_);
v_a_829_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_825_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_hypotheses_837_; lean_object* v___x_838_; 
v_hypotheses_837_ = lean_ctor_get(v___x_824_, 0);
lean_inc_ref(v_hypotheses_837_);
lean_dec_ref(v___x_824_);
v___x_838_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_837_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
v_hyps_797_ = v_a_839_;
v___y_798_ = v___y_781_;
v___y_799_ = v___y_782_;
v___y_800_ = v___y_783_;
v___y_801_ = v___y_784_;
v___y_802_ = v___y_785_;
v___y_803_ = v___y_786_;
v___y_804_ = v___y_787_;
v___y_805_ = v___y_788_;
goto v___jp_796_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_dec(v_fst_793_);
lean_dec(v___x_779_);
v_a_840_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_838_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
v___jp_796_:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_799_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___x_813_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc_n(v_a_807_, 2);
lean_dec_ref(v___x_806_);
v___x_808_ = lean_box(0);
v___x_809_ = 3;
v___x_810_ = lean_box(v___x_809_);
v___x_811_ = lean_box_usize(v___x_777_);
v___f_812_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed), 18, 9);
lean_closure_set(v___f_812_, 0, v_a_807_);
lean_closure_set(v___f_812_, 1, v_snd_795_);
lean_closure_set(v___f_812_, 2, v_hyps_797_);
lean_closure_set(v___f_812_, 3, v___x_808_);
lean_closure_set(v___f_812_, 4, v___x_810_);
lean_closure_set(v___f_812_, 5, v_fst_793_);
lean_closure_set(v___f_812_, 6, v_fst_794_);
lean_closure_set(v___f_812_, 7, v___x_779_);
lean_closure_set(v___f_812_, 8, v___x_811_);
v___x_813_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_a_807_, v___f_812_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
return v___x_813_;
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_hyps_797_);
lean_dec(v_snd_795_);
lean_dec(v_fst_794_);
lean_dec(v_fst_793_);
lean_dec(v___x_779_);
v_a_814_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_806_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_806_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v___x_779_);
v_a_848_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_790_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_790_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed(lean_object* v___x_856_, lean_object* v_sz_857_, lean_object* v___x_858_, lean_object* v___x_859_, lean_object* v___x_860_, lean_object* v_stx_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
size_t v_sz_boxed_871_; size_t v___x_10195__boxed_872_; lean_object* v_res_873_; 
v_sz_boxed_871_ = lean_unbox_usize(v_sz_857_);
lean_dec(v_sz_857_);
v___x_10195__boxed_872_ = lean_unbox_usize(v___x_858_);
lean_dec(v___x_858_);
v_res_873_ = l_Lean_Elab_Tactic_evalGeneralize___lam__2(v___x_856_, v_sz_boxed_871_, v___x_10195__boxed_872_, v___x_859_, v___x_860_, v_stx_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v_stx_861_);
lean_dec_ref(v___x_856_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize(lean_object* v_stx_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; size_t v_sz_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = l_Lean_Syntax_getArg(v_stx_883_, v___x_894_);
v___x_896_ = l_Lean_Syntax_getSepArgs(v___x_895_);
lean_dec(v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Elab_Tactic_evalGeneralize___closed__2));
v_sz_898_ = lean_array_size(v___x_896_);
v___x_899_ = lean_box_usize(v_sz_898_);
v___x_900_ = ((lean_object*)(l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1));
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed), 15, 6);
lean_closure_set(v___f_901_, 0, v___x_896_);
lean_closure_set(v___f_901_, 1, v___x_899_);
lean_closure_set(v___f_901_, 2, v___x_900_);
lean_closure_set(v___f_901_, 3, v___x_897_);
lean_closure_set(v___f_901_, 4, v___x_893_);
lean_closure_set(v___f_901_, 5, v_stx_883_);
v___x_902_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_901_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___boxed(lean_object* v_stx_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_Elab_Tactic_evalGeneralize(v_stx_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(lean_object* v_as_914_, size_t v_sz_915_, size_t v_i_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_914_, v_sz_915_, v_i_916_, v_b_917_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___boxed(lean_object* v_as_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_942_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(v_as_928_, v_sz_boxed_941_, v_i_boxed_942_, v_b_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_as_928_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(lean_object* v_as_944_, size_t v_sz_945_, size_t v_i_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_944_, v_sz_945_, v_i_946_, v_b_947_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___boxed(lean_object* v_as_958_, lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
size_t v_sz_boxed_971_; size_t v_i_boxed_972_; lean_object* v_res_973_; 
v_sz_boxed_971_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_972_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(v_as_958_, v_sz_boxed_971_, v_i_boxed_972_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_as_958_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_as_974_, size_t v_sz_975_, size_t v_i_976_, lean_object* v_b_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_974_, v_sz_975_, v_i_976_, v_b_977_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_as_988_, lean_object* v_sz_989_, lean_object* v_i_990_, lean_object* v_b_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
size_t v_sz_boxed_1001_; size_t v_i_boxed_1002_; lean_object* v_res_1003_; 
v_sz_boxed_1001_ = lean_unbox_usize(v_sz_989_);
lean_dec(v_sz_989_);
v_i_boxed_1002_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(v_as_988_, v_sz_boxed_1001_, v_i_boxed_1002_, v_b_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_as_988_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1(){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1021_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4));
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7));
v___x_1024_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___boxed), 10, 0);
v___x_1025_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1021_, v___x_1022_, v___x_1023_, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___boxed(lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3(){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7));
v___x_1055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6));
v___x_1056_ = l_Lean_addBuiltinDeclarationRanges(v___x_1054_, v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___boxed(lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
return v_res_1058_;
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
