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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v_res_12_;
v_res_12_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed(lean_object* v_x_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0(v_x_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_23_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(lean_object* v_mvarId_24_, lean_object* v_x_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___f_35_; lean_object* v___x_36_; 
lean_inc(v___y_29_);
lean_inc_ref(v___y_28_);
lean_inc(v___y_27_);
lean_inc_ref(v___y_26_);
v___f_35_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_35_, 0, v_x_25_);
lean_closure_set(v___f_35_, 1, v___y_26_);
lean_closure_set(v___f_35_, 2, v___y_27_);
lean_closure_set(v___f_35_, 3, v___y_28_);
lean_closure_set(v___f_35_, 4, v___y_29_);
v___x_36_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_24_, v___f_35_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
if (lean_obj_tag(v___x_36_) == 0)
{
return v___x_36_;
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_36_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_24_ = stack[0].m_obj;
lean_object* v_x_25_ = stack[1].m_obj;
lean_object* v___y_26_ = stack[2].m_obj;
lean_object* v___y_27_ = stack[3].m_obj;
lean_object* v___y_28_ = stack[4].m_obj;
lean_object* v___y_29_ = stack[5].m_obj;
lean_object* v___y_30_ = stack[6].m_obj;
lean_object* v___y_31_ = stack[7].m_obj;
lean_object* v___y_32_ = stack[8].m_obj;
lean_object* v___y_33_ = stack[9].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_mvarId_24_, v_x_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg___boxed(lean_object* v_mvarId_46_, lean_object* v_x_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_mvarId_46_, v_x_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
return v_res_57_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(lean_object* v_00_u03b1_58_, lean_object* v_mvarId_59_, lean_object* v_x_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_mvarId_59_, v_x_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
return v___x_70_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_59_ = stack[1].m_obj;
lean_object* v_x_60_ = stack[2].m_obj;
lean_object* v___y_61_ = stack[3].m_obj;
lean_object* v___y_62_ = stack[4].m_obj;
lean_object* v___y_63_ = stack[5].m_obj;
lean_object* v___y_64_ = stack[6].m_obj;
lean_object* v___y_65_ = stack[7].m_obj;
lean_object* v___y_66_ = stack[8].m_obj;
lean_object* v___y_67_ = stack[9].m_obj;
lean_object* v___y_68_ = stack[10].m_obj;
lean_object* v_res_71_;
v_res_71_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(lean_box(0), v_mvarId_59_, v_x_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___boxed(lean_object* v_00_u03b1_72_, lean_object* v_mvarId_73_, lean_object* v_x_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2(v_00_u03b1_72_, v_mvarId_73_, v_x_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
return v_res_84_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(lean_object* v_as_85_, size_t v_sz_86_, size_t v_i_87_, lean_object* v_b_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_usize_dec_lt(v_i_87_, v_sz_86_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v_b_88_);
return v___x_97_;
}
else
{
lean_object* v_array_98_; lean_object* v_start_99_; lean_object* v_stop_100_; uint8_t v___x_101_; 
v_array_98_ = lean_ctor_get(v_b_88_, 0);
v_start_99_ = lean_ctor_get(v_b_88_, 1);
v_stop_100_ = lean_ctor_get(v_b_88_, 2);
v___x_101_ = lean_nat_dec_lt(v_start_99_, v_stop_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v_b_88_);
return v___x_102_;
}
else
{
lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_126_; 
lean_inc(v_stop_100_);
lean_inc(v_start_99_);
lean_inc_ref(v_array_98_);
v_isSharedCheck_126_ = !lean_is_exclusive(v_b_88_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; lean_object* v_unused_128_; lean_object* v_unused_129_; 
v_unused_127_ = lean_ctor_get(v_b_88_, 2);
lean_dec(v_unused_127_);
v_unused_128_ = lean_ctor_get(v_b_88_, 1);
lean_dec(v_unused_128_);
v_unused_129_ = lean_ctor_get(v_b_88_, 0);
lean_dec(v_unused_129_);
v___x_104_ = v_b_88_;
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
else
{
lean_dec(v_b_88_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_a_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v_a_106_ = lean_array_uget_borrowed(v_as_85_, v_i_87_);
v___x_107_ = lean_array_fget(v_array_98_, v_start_99_);
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_start_99_, v___x_108_);
lean_dec(v_start_99_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_109_);
v___x_111_ = v___x_104_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_array_98_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_stop_100_);
v___x_111_ = v_reuseFailAlloc_125_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_inc(v_a_106_);
v___x_112_ = l_Lean_Expr_fvar___override(v_a_106_);
v___x_113_ = l_Lean_Elab_Term_addLocalVarInfo(v___x_107_, v___x_112_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_113_) == 0)
{
size_t v___x_114_; size_t v___x_115_; 
lean_dec_ref_known(v___x_113_, 1);
v___x_114_ = ((size_t)1ULL);
v___x_115_ = lean_usize_add(v_i_87_, v___x_114_);
v_i_87_ = v___x_115_;
v_b_88_ = v___x_111_;
goto _start;
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
lean_dec_ref(v___x_111_);
v_a_117_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_113_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_113_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_85_ = stack[0].m_obj;
size_t v_sz_86_ = stack[1].m_num;
size_t v_i_87_ = stack[2].m_num;
lean_object* v_b_88_ = stack[3].m_obj;
lean_object* v___y_89_ = stack[4].m_obj;
lean_object* v___y_90_ = stack[5].m_obj;
lean_object* v___y_91_ = stack[6].m_obj;
lean_object* v___y_92_ = stack[7].m_obj;
lean_object* v___y_93_ = stack[8].m_obj;
lean_object* v___y_94_ = stack[9].m_obj;
lean_object* v_res_130_;
v_res_130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_85_, v_sz_86_, v_i_87_, v_b_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg___boxed(lean_object* v_as_131_, lean_object* v_sz_132_, lean_object* v_i_133_, lean_object* v_b_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
size_t v_sz_boxed_142_; size_t v_i_boxed_143_; lean_object* v_res_144_; 
v_sz_boxed_142_ = lean_unbox_usize(v_sz_132_);
lean_dec(v_sz_132_);
v_i_boxed_143_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_131_, v_sz_boxed_142_, v_i_boxed_143_, v_b_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec_ref(v_as_131_);
return v_res_144_;
}
}
lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__0(lean_object* v_fst_145_, size_t v_sz_146_, size_t v___x_147_, lean_object* v___x_148_, lean_object* v_snd_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_fst_145_, v_sz_146_, v___x_147_, v___x_148_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec_ref_known(v___x_159_, 1);
v___x_160_ = lean_box(0);
v___x_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_161_, 0, v_snd_149_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_161_, v___y_151_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
return v___x_162_;
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_dec(v_snd_149_);
v_a_163_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_159_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_159_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalGeneralize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_145_ = stack[0].m_obj;
size_t v_sz_146_ = stack[1].m_num;
size_t v___x_147_ = stack[2].m_num;
lean_object* v___x_148_ = stack[3].m_obj;
lean_object* v_snd_149_ = stack[4].m_obj;
lean_object* v___y_150_ = stack[5].m_obj;
lean_object* v___y_151_ = stack[6].m_obj;
lean_object* v___y_152_ = stack[7].m_obj;
lean_object* v___y_153_ = stack[8].m_obj;
lean_object* v___y_154_ = stack[9].m_obj;
lean_object* v___y_155_ = stack[10].m_obj;
lean_object* v___y_156_ = stack[11].m_obj;
lean_object* v___y_157_ = stack[12].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Lean_Elab_Tactic_evalGeneralize___lam__0(v_fst_145_, v_sz_146_, v___x_147_, v___x_148_, v_snd_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__0___boxed(lean_object* v_fst_172_, lean_object* v_sz_173_, lean_object* v___x_174_, lean_object* v___x_175_, lean_object* v_snd_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
size_t v_sz_boxed_186_; size_t v___x_9346__boxed_187_; lean_object* v_res_188_; 
v_sz_boxed_186_ = lean_unbox_usize(v_sz_173_);
lean_dec(v_sz_173_);
v___x_9346__boxed_187_ = lean_unbox_usize(v___x_174_);
lean_dec(v___x_174_);
v_res_188_ = l_Lean_Elab_Tactic_evalGeneralize___lam__0(v_fst_172_, v_sz_boxed_186_, v___x_9346__boxed_187_, v___x_175_, v_snd_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec_ref(v_fst_172_);
return v_res_188_;
}
}
lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__1(lean_object* v_a_189_, lean_object* v_snd_190_, lean_object* v_hyps_191_, lean_object* v___x_192_, uint8_t v___x_193_, lean_object* v_fst_194_, lean_object* v_fst_195_, lean_object* v___x_196_, size_t v___x_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_MVarId_generalizeHyp(v_a_189_, v_snd_190_, v_hyps_191_, v___x_192_, v___x_193_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_snd_209_; lean_object* v_fst_210_; lean_object* v_snd_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; size_t v_sz_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___f_218_; lean_object* v___x_219_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v_snd_209_ = lean_ctor_get(v_a_208_, 1);
lean_inc(v_snd_209_);
lean_dec(v_a_208_);
v_fst_210_ = lean_ctor_get(v_snd_209_, 0);
lean_inc(v_fst_210_);
v_snd_211_ = lean_ctor_get(v_snd_209_, 1);
lean_inc_n(v_snd_211_, 2);
lean_dec(v_snd_209_);
v___x_212_ = l_Array_append___redArg(v_fst_194_, v_fst_195_);
v___x_213_ = lean_array_get_size(v___x_212_);
v___x_214_ = l_Array_toSubarray___redArg(v___x_212_, v___x_196_, v___x_213_);
v_sz_215_ = lean_array_size(v_fst_210_);
v___x_216_ = lean_box_usize(v_sz_215_);
v___x_217_ = lean_box_usize(v___x_197_);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lam__0___boxed), 14, 5);
lean_closure_set(v___f_218_, 0, v_fst_210_);
lean_closure_set(v___f_218_, 1, v___x_216_);
lean_closure_set(v___f_218_, 2, v___x_217_);
lean_closure_set(v___f_218_, 3, v___x_214_);
lean_closure_set(v___f_218_, 4, v_snd_211_);
v___x_219_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_snd_211_, v___f_218_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
return v___x_219_;
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v___x_196_);
lean_dec(v_fst_194_);
v_a_220_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_207_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_207_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalGeneralize___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_189_ = stack[0].m_obj;
lean_object* v_snd_190_ = stack[1].m_obj;
lean_object* v_hyps_191_ = stack[2].m_obj;
lean_object* v___x_192_ = stack[3].m_obj;
uint8_t v___x_193_ = stack[4].m_num;
lean_object* v_fst_194_ = stack[5].m_obj;
lean_object* v_fst_195_ = stack[6].m_obj;
lean_object* v___x_196_ = stack[7].m_obj;
size_t v___x_197_ = stack[8].m_num;
lean_object* v___y_198_ = stack[9].m_obj;
lean_object* v___y_199_ = stack[10].m_obj;
lean_object* v___y_200_ = stack[11].m_obj;
lean_object* v___y_201_ = stack[12].m_obj;
lean_object* v___y_202_ = stack[13].m_obj;
lean_object* v___y_203_ = stack[14].m_obj;
lean_object* v___y_204_ = stack[15].m_obj;
lean_object* v___y_205_ = stack[16].m_obj;
lean_object* v_res_228_;
v_res_228_ = l_Lean_Elab_Tactic_evalGeneralize___lam__1(v_a_189_, v_snd_190_, v_hyps_191_, v___x_192_, v___x_193_, v_fst_194_, v_fst_195_, v___x_196_, v___x_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed(lean_object** _args){
lean_object* v_a_229_ = _args[0];
lean_object* v_snd_230_ = _args[1];
lean_object* v_hyps_231_ = _args[2];
lean_object* v___x_232_ = _args[3];
lean_object* v___x_233_ = _args[4];
lean_object* v_fst_234_ = _args[5];
lean_object* v_fst_235_ = _args[6];
lean_object* v___x_236_ = _args[7];
lean_object* v___x_237_ = _args[8];
lean_object* v___y_238_ = _args[9];
lean_object* v___y_239_ = _args[10];
lean_object* v___y_240_ = _args[11];
lean_object* v___y_241_ = _args[12];
lean_object* v___y_242_ = _args[13];
lean_object* v___y_243_ = _args[14];
lean_object* v___y_244_ = _args[15];
lean_object* v___y_245_ = _args[16];
lean_object* v___y_246_ = _args[17];
_start:
{
uint8_t v___x_9449__boxed_247_; size_t v___x_9451__boxed_248_; lean_object* v_res_249_; 
v___x_9449__boxed_247_ = lean_unbox(v___x_233_);
v___x_9451__boxed_248_ = lean_unbox_usize(v___x_237_);
lean_dec(v___x_237_);
v_res_249_ = l_Lean_Elab_Tactic_evalGeneralize___lam__1(v_a_229_, v_snd_230_, v_hyps_231_, v___x_232_, v___x_9449__boxed_247_, v_fst_234_, v_fst_235_, v___x_236_, v___x_9451__boxed_248_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v_fst_235_);
lean_dec_ref(v_hyps_231_);
return v_res_249_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(lean_object* v_as_250_, size_t v_sz_251_, size_t v_i_252_, lean_object* v_b_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = lean_usize_dec_lt(v_i_252_, v_sz_251_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v_b_253_);
return v___x_264_;
}
else
{
lean_object* v_snd_265_; lean_object* v_fst_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_326_; 
v_snd_265_ = lean_ctor_get(v_b_253_, 1);
v_fst_266_ = lean_ctor_get(v_b_253_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v_b_253_);
if (v_isSharedCheck_326_ == 0)
{
v___x_268_ = v_b_253_;
v_isShared_269_ = v_isSharedCheck_326_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_snd_265_);
lean_inc(v_fst_266_);
lean_dec(v_b_253_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_326_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_fst_270_; lean_object* v_snd_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_325_; 
v_fst_270_ = lean_ctor_get(v_snd_265_, 0);
v_snd_271_ = lean_ctor_get(v_snd_265_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_snd_265_);
if (v_isSharedCheck_325_ == 0)
{
v___x_273_ = v_snd_265_;
v_isShared_274_ = v_isSharedCheck_325_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_snd_271_);
lean_inc(v_fst_270_);
lean_dec(v_snd_265_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_325_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v_a_276_; lean_object* v_hName_x3f_278_; lean_object* v_hIdents_279_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v_a_276_ = lean_array_uget_borrowed(v_as_250_, v_i_252_);
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = l_Lean_Syntax_getArg(v_a_276_, v___x_317_);
v___x_319_ = l_Lean_Syntax_isNone(v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_320_ = l_Lean_Syntax_getArg(v___x_318_, v___x_317_);
lean_dec(v___x_318_);
lean_inc(v___x_320_);
v___x_321_ = lean_array_push(v_fst_270_, v___x_320_);
v___x_322_ = l_Lean_Syntax_getId(v___x_320_);
lean_dec(v___x_320_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
v_hName_x3f_278_ = v___x_323_;
v_hIdents_279_ = v___x_321_;
v___y_280_ = v___y_254_;
v___y_281_ = v___y_255_;
v___y_282_ = v___y_256_;
v___y_283_ = v___y_257_;
v___y_284_ = v___y_258_;
v___y_285_ = v___y_259_;
v___y_286_ = v___y_260_;
v___y_287_ = v___y_261_;
goto v___jp_277_;
}
else
{
lean_object* v___x_324_; 
lean_dec(v___x_318_);
v___x_324_ = lean_box(0);
v_hName_x3f_278_ = v___x_324_;
v_hIdents_279_ = v_fst_270_;
v___y_280_ = v___y_254_;
v___y_281_ = v___y_255_;
v___y_282_ = v___y_256_;
v___y_283_ = v___y_257_;
v___y_284_ = v___y_258_;
v___y_285_ = v___y_259_;
v___y_286_ = v___y_260_;
v___y_287_ = v___y_261_;
goto v___jp_277_;
}
v___jp_277_:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; 
v___x_288_ = l_Lean_Syntax_getArg(v_a_276_, v___x_275_);
v___x_289_ = lean_box(0);
v___x_290_ = 0;
v___x_291_ = l_Lean_Elab_Tactic_elabTerm(v___x_288_, v___x_289_, v___x_290_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v___x_291_, 1);
v___x_293_ = lean_unsigned_to_nat(3u);
v___x_294_ = l_Lean_Syntax_getArg(v_a_276_, v___x_293_);
lean_inc(v___x_294_);
v___x_295_ = lean_array_push(v_fst_266_, v___x_294_);
v___x_296_ = l_Lean_Syntax_getId(v___x_294_);
lean_dec(v___x_294_);
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v_a_292_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_ctor_set(v___x_298_, 2, v_hName_x3f_278_);
v___x_299_ = lean_array_push(v_snd_271_, v___x_298_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_299_);
lean_ctor_set(v___x_273_, 0, v_hIdents_279_);
v___x_301_ = v___x_273_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_hIdents_279_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_299_);
v___x_301_ = v_reuseFailAlloc_308_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_303_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v___x_301_);
lean_ctor_set(v___x_268_, 0, v___x_295_);
v___x_303_ = v___x_268_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
size_t v___x_304_; size_t v___x_305_; 
v___x_304_ = ((size_t)1ULL);
v___x_305_ = lean_usize_add(v_i_252_, v___x_304_);
v_i_252_ = v___x_305_;
v_b_253_ = v___x_303_;
goto _start;
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v_hIdents_279_);
lean_dec(v_hName_x3f_278_);
lean_del_object(v___x_273_);
lean_dec(v_snd_271_);
lean_del_object(v___x_268_);
lean_dec(v_fst_266_);
v_a_309_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_291_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_291_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_250_ = stack[0].m_obj;
size_t v_sz_251_ = stack[1].m_num;
size_t v_i_252_ = stack[2].m_num;
lean_object* v_b_253_ = stack[3].m_obj;
lean_object* v___y_254_ = stack[4].m_obj;
lean_object* v___y_255_ = stack[5].m_obj;
lean_object* v___y_256_ = stack[6].m_obj;
lean_object* v___y_257_ = stack[7].m_obj;
lean_object* v___y_258_ = stack[8].m_obj;
lean_object* v___y_259_ = stack[9].m_obj;
lean_object* v___y_260_ = stack[10].m_obj;
lean_object* v___y_261_ = stack[11].m_obj;
lean_object* v_res_327_;
v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v_as_250_, v_sz_251_, v_i_252_, v_b_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0___boxed(lean_object* v_as_328_, lean_object* v_sz_329_, lean_object* v_i_330_, lean_object* v_b_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
size_t v_sz_boxed_341_; size_t v_i_boxed_342_; lean_object* v_res_343_; 
v_sz_boxed_341_ = lean_unbox_usize(v_sz_329_);
lean_dec(v_sz_329_);
v_i_boxed_342_ = lean_unbox_usize(v_i_330_);
lean_dec(v_i_330_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v_as_328_, v_sz_boxed_341_, v_i_boxed_342_, v_b_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec_ref(v_as_328_);
return v_res_343_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(lean_object* v_as_344_, size_t v_sz_345_, size_t v_i_346_, lean_object* v_b_347_){
_start:
{
uint8_t v___x_349_; 
v___x_349_ = lean_usize_dec_lt(v_i_346_, v_sz_345_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v_b_347_);
return v___x_350_;
}
else
{
lean_object* v_snd_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_369_; 
v_snd_351_ = lean_ctor_get(v_b_347_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v_b_347_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v_b_347_, 0);
lean_dec(v_unused_370_);
v___x_353_ = v_b_347_;
v_isShared_354_ = v_isSharedCheck_369_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_snd_351_);
lean_dec(v_b_347_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_369_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v_a_357_; lean_object* v_a_364_; 
v___x_355_ = lean_box(0);
v_a_364_ = lean_array_uget_borrowed(v_as_344_, v_i_346_);
if (lean_obj_tag(v_a_364_) == 0)
{
v_a_357_ = v_snd_351_;
goto v___jp_356_;
}
else
{
lean_object* v_val_365_; uint8_t v___x_366_; 
v_val_365_ = lean_ctor_get(v_a_364_, 0);
v___x_366_ = l_Lean_LocalDecl_isImplementationDetail(v_val_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_inc(v_val_365_);
v___x_367_ = l_Lean_LocalDecl_toExpr(v_val_365_);
v___x_368_ = lean_array_push(v_snd_351_, v___x_367_);
v_a_357_ = v___x_368_;
goto v___jp_356_;
}
else
{
v_a_357_ = v_snd_351_;
goto v___jp_356_;
}
}
v___jp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v_a_357_);
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_359_ = v___x_353_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_a_357_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
size_t v___x_360_; size_t v___x_361_; 
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_346_, v___x_360_);
v_i_346_ = v___x_361_;
v_b_347_ = v___x_359_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_344_ = stack[0].m_obj;
size_t v_sz_345_ = stack[1].m_num;
size_t v_i_346_ = stack[2].m_num;
lean_object* v_b_347_ = stack[3].m_obj;
lean_object* v_res_371_;
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_344_, v_sz_345_, v_i_346_, v_b_347_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg___boxed(lean_object* v_as_372_, lean_object* v_sz_373_, lean_object* v_i_374_, lean_object* v_b_375_, lean_object* v___y_376_){
_start:
{
size_t v_sz_boxed_377_; size_t v_i_boxed_378_; lean_object* v_res_379_; 
v_sz_boxed_377_ = lean_unbox_usize(v_sz_373_);
lean_dec(v_sz_373_);
v_i_boxed_378_ = lean_unbox_usize(v_i_374_);
lean_dec(v_i_374_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_372_, v_sz_boxed_377_, v_i_boxed_378_, v_b_375_);
lean_dec_ref(v_as_372_);
return v_res_379_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(lean_object* v_as_380_, size_t v_sz_381_, size_t v_i_382_, lean_object* v_b_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
uint8_t v___x_393_; 
v___x_393_ = lean_usize_dec_lt(v_i_382_, v_sz_381_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v_b_383_);
return v___x_394_;
}
else
{
lean_object* v_snd_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_413_; 
v_snd_395_ = lean_ctor_get(v_b_383_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_b_383_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v_b_383_, 0);
lean_dec(v_unused_414_);
v___x_397_ = v_b_383_;
v_isShared_398_ = v_isSharedCheck_413_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_snd_395_);
lean_dec(v_b_383_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_413_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v_a_401_; lean_object* v_a_408_; 
v___x_399_ = lean_box(0);
v_a_408_ = lean_array_uget_borrowed(v_as_380_, v_i_382_);
if (lean_obj_tag(v_a_408_) == 0)
{
v_a_401_ = v_snd_395_;
goto v___jp_400_;
}
else
{
lean_object* v_val_409_; uint8_t v___x_410_; 
v_val_409_ = lean_ctor_get(v_a_408_, 0);
v___x_410_ = l_Lean_LocalDecl_isImplementationDetail(v_val_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_inc(v_val_409_);
v___x_411_ = l_Lean_LocalDecl_toExpr(v_val_409_);
v___x_412_ = lean_array_push(v_snd_395_, v___x_411_);
v_a_401_ = v___x_412_;
goto v___jp_400_;
}
else
{
v_a_401_ = v_snd_395_;
goto v___jp_400_;
}
}
v___jp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v_a_401_);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_403_ = v___x_397_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_a_401_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; 
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_382_, v___x_404_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_380_, v_sz_381_, v___x_405_, v___x_403_);
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_380_ = stack[0].m_obj;
size_t v_sz_381_ = stack[1].m_num;
size_t v_i_382_ = stack[2].m_num;
lean_object* v_b_383_ = stack[3].m_obj;
lean_object* v___y_384_ = stack[4].m_obj;
lean_object* v___y_385_ = stack[5].m_obj;
lean_object* v___y_386_ = stack[6].m_obj;
lean_object* v___y_387_ = stack[7].m_obj;
lean_object* v___y_388_ = stack[8].m_obj;
lean_object* v___y_389_ = stack[9].m_obj;
lean_object* v___y_390_ = stack[10].m_obj;
lean_object* v___y_391_ = stack[11].m_obj;
lean_object* v_res_415_;
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_as_380_, v_sz_381_, v_i_382_, v_b_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7___boxed(lean_object* v_as_416_, lean_object* v_sz_417_, lean_object* v_i_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
size_t v_sz_boxed_429_; size_t v_i_boxed_430_; lean_object* v_res_431_; 
v_sz_boxed_429_ = lean_unbox_usize(v_sz_417_);
lean_dec(v_sz_417_);
v_i_boxed_430_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_as_416_, v_sz_boxed_429_, v_i_boxed_430_, v_b_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec_ref(v_as_416_);
return v_res_431_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(lean_object* v_init_432_, lean_object* v_n_433_, lean_object* v_b_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
if (lean_obj_tag(v_n_433_) == 0)
{
lean_object* v_cs_444_; lean_object* v___x_445_; lean_object* v___x_446_; size_t v_sz_447_; size_t v___x_448_; lean_object* v___x_449_; 
v_cs_444_ = lean_ctor_get(v_n_433_, 0);
v___x_445_ = lean_box(0);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v_b_434_);
v_sz_447_ = lean_array_size(v_cs_444_);
v___x_448_ = ((size_t)0ULL);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_432_, v_cs_444_, v_sz_447_, v___x_448_, v___x_446_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_464_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_464_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_464_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_464_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_fst_454_; 
v_fst_454_ = lean_ctor_get(v_a_450_, 0);
if (lean_obj_tag(v_fst_454_) == 0)
{
lean_object* v_snd_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v_snd_455_ = lean_ctor_get(v_a_450_, 1);
lean_inc(v_snd_455_);
lean_dec(v_a_450_);
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v_snd_455_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_456_);
v___x_458_ = v___x_452_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v_val_460_; lean_object* v___x_462_; 
lean_inc_ref(v_fst_454_);
lean_dec(v_a_450_);
v_val_460_ = lean_ctor_get(v_fst_454_, 0);
lean_inc(v_val_460_);
lean_dec_ref_known(v_fst_454_, 1);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_val_460_);
v___x_462_ = v___x_452_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_val_460_);
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
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_449_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_449_);
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
else
{
lean_object* v_vs_473_; lean_object* v___x_474_; lean_object* v___x_475_; size_t v_sz_476_; size_t v___x_477_; lean_object* v___x_478_; 
v_vs_473_ = lean_ctor_get(v_n_433_, 0);
v___x_474_ = lean_box(0);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
lean_ctor_set(v___x_475_, 1, v_b_434_);
v_sz_476_ = lean_array_size(v_vs_473_);
v___x_477_ = ((size_t)0ULL);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7(v_vs_473_, v_sz_476_, v___x_477_, v___x_475_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_493_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_493_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_fst_483_; 
v_fst_483_ = lean_ctor_get(v_a_479_, 0);
if (lean_obj_tag(v_fst_483_) == 0)
{
lean_object* v_snd_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v_snd_484_ = lean_ctor_get(v_a_479_, 1);
lean_inc(v_snd_484_);
lean_dec(v_a_479_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v_snd_484_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_485_);
v___x_487_ = v___x_481_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v_val_489_; lean_object* v___x_491_; 
lean_inc_ref(v_fst_483_);
lean_dec(v_a_479_);
v_val_489_ = lean_ctor_get(v_fst_483_, 0);
lean_inc(v_val_489_);
lean_dec_ref_known(v_fst_483_, 1);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v_val_489_);
v___x_491_ = v___x_481_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_val_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_a_494_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_478_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_478_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_432_ = stack[0].m_obj;
lean_object* v_n_433_ = stack[1].m_obj;
lean_object* v_b_434_ = stack[2].m_obj;
lean_object* v___y_435_ = stack[3].m_obj;
lean_object* v___y_436_ = stack[4].m_obj;
lean_object* v___y_437_ = stack[5].m_obj;
lean_object* v___y_438_ = stack[6].m_obj;
lean_object* v___y_439_ = stack[7].m_obj;
lean_object* v___y_440_ = stack[8].m_obj;
lean_object* v___y_441_ = stack[9].m_obj;
lean_object* v___y_442_ = stack[10].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_432_, v_n_433_, v_b_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
stack->m_obj
 = v_res_502_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(lean_object* v_init_503_, lean_object* v_as_504_, size_t v_sz_505_, size_t v_i_506_, lean_object* v_b_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_usize_dec_lt(v_i_506_, v_sz_505_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_b_507_);
return v___x_518_;
}
else
{
lean_object* v_snd_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_553_; 
v_snd_519_ = lean_ctor_get(v_b_507_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_b_507_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_b_507_, 0);
lean_dec(v_unused_554_);
v___x_521_ = v_b_507_;
v_isShared_522_ = v_isSharedCheck_553_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snd_519_);
lean_dec(v_b_507_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_553_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v_a_524_; lean_object* v___x_525_; 
v___x_523_ = lean_box(0);
v_a_524_ = lean_array_uget_borrowed(v_as_504_, v_i_506_);
lean_inc(v_snd_519_);
v___x_525_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_503_, v_a_524_, v_snd_519_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_544_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_544_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_544_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_544_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
if (lean_obj_tag(v_a_526_) == 0)
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_a_526_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_530_);
v___x_532_ = v___x_521_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_snd_519_);
v___x_532_ = v_reuseFailAlloc_536_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_532_);
v___x_534_ = v___x_528_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; 
lean_del_object(v___x_528_);
lean_dec(v_snd_519_);
v_a_537_ = lean_ctor_get(v_a_526_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v_a_526_, 1);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_a_537_);
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_539_ = v___x_521_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_a_537_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
size_t v___x_540_; size_t v___x_541_; 
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_add(v_i_506_, v___x_540_);
v_i_506_ = v___x_541_;
v_b_507_ = v___x_539_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_del_object(v___x_521_);
lean_dec(v_snd_519_);
v_a_545_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_525_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_525_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_503_ = stack[0].m_obj;
lean_object* v_as_504_ = stack[1].m_obj;
size_t v_sz_505_ = stack[2].m_num;
size_t v_i_506_ = stack[3].m_num;
lean_object* v_b_507_ = stack[4].m_obj;
lean_object* v___y_508_ = stack[5].m_obj;
lean_object* v___y_509_ = stack[6].m_obj;
lean_object* v___y_510_ = stack[7].m_obj;
lean_object* v___y_511_ = stack[8].m_obj;
lean_object* v___y_512_ = stack[9].m_obj;
lean_object* v___y_513_ = stack[10].m_obj;
lean_object* v___y_514_ = stack[11].m_obj;
lean_object* v___y_515_ = stack[12].m_obj;
lean_object* v_res_555_;
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_503_, v_as_504_, v_sz_505_, v_i_506_, v_b_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_init_556_, lean_object* v_as_557_, lean_object* v_sz_558_, lean_object* v_i_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
size_t v_sz_boxed_570_; size_t v_i_boxed_571_; lean_object* v_res_572_; 
v_sz_boxed_570_ = lean_unbox_usize(v_sz_558_);
lean_dec(v_sz_558_);
v_i_boxed_571_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_res_572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__6(v_init_556_, v_as_557_, v_sz_boxed_570_, v_i_boxed_571_, v_b_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v_as_557_);
lean_dec_ref(v_init_556_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4___boxed(lean_object* v_init_573_, lean_object* v_n_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_573_, v_n_574_, v_b_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v_n_574_);
lean_dec_ref(v_init_573_);
return v_res_585_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(lean_object* v_as_586_, size_t v_sz_587_, size_t v_i_588_, lean_object* v_b_589_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_lt(v_i_588_, v_sz_587_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_b_589_);
return v___x_592_;
}
else
{
lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_611_; 
v_snd_593_ = lean_ctor_get(v_b_589_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_b_589_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v_b_589_, 0);
lean_dec(v_unused_612_);
v___x_595_ = v_b_589_;
v_isShared_596_ = v_isSharedCheck_611_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_dec(v_b_589_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_611_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_a_599_; lean_object* v_a_606_; 
v___x_597_ = lean_box(0);
v_a_606_ = lean_array_uget_borrowed(v_as_586_, v_i_588_);
if (lean_obj_tag(v_a_606_) == 0)
{
v_a_599_ = v_snd_593_;
goto v___jp_598_;
}
else
{
lean_object* v_val_607_; uint8_t v___x_608_; 
v_val_607_ = lean_ctor_get(v_a_606_, 0);
v___x_608_ = l_Lean_LocalDecl_isImplementationDetail(v_val_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
lean_inc(v_val_607_);
v___x_609_ = l_Lean_LocalDecl_toExpr(v_val_607_);
v___x_610_ = lean_array_push(v_snd_593_, v___x_609_);
v_a_599_ = v___x_610_;
goto v___jp_598_;
}
else
{
v_a_599_ = v_snd_593_;
goto v___jp_598_;
}
}
v___jp_598_:
{
lean_object* v___x_601_; 
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v_a_599_);
lean_ctor_set(v___x_595_, 0, v___x_597_);
v___x_601_ = v___x_595_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_599_);
v___x_601_ = v_reuseFailAlloc_605_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
size_t v___x_602_; size_t v___x_603_; 
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_588_, v___x_602_);
v_i_588_ = v___x_603_;
v_b_589_ = v___x_601_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_586_ = stack[0].m_obj;
size_t v_sz_587_ = stack[1].m_num;
size_t v_i_588_ = stack[2].m_num;
lean_object* v_b_589_ = stack[3].m_obj;
lean_object* v_res_613_;
v_res_613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_586_, v_sz_587_, v_i_588_, v_b_589_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_as_614_, lean_object* v_sz_615_, lean_object* v_i_616_, lean_object* v_b_617_, lean_object* v___y_618_){
_start:
{
size_t v_sz_boxed_619_; size_t v_i_boxed_620_; lean_object* v_res_621_; 
v_sz_boxed_619_ = lean_unbox_usize(v_sz_615_);
lean_dec(v_sz_615_);
v_i_boxed_620_ = lean_unbox_usize(v_i_616_);
lean_dec(v_i_616_);
v_res_621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_614_, v_sz_boxed_619_, v_i_boxed_620_, v_b_617_);
lean_dec_ref(v_as_614_);
return v_res_621_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(lean_object* v_as_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_b_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v_b_625_);
return v___x_636_;
}
else
{
lean_object* v_snd_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_655_; 
v_snd_637_ = lean_ctor_get(v_b_625_, 1);
v_isSharedCheck_655_ = !lean_is_exclusive(v_b_625_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v_b_625_, 0);
lean_dec(v_unused_656_);
v___x_639_ = v_b_625_;
v_isShared_640_ = v_isSharedCheck_655_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_snd_637_);
lean_dec(v_b_625_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_655_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v_a_643_; lean_object* v_a_650_; 
v___x_641_ = lean_box(0);
v_a_650_ = lean_array_uget_borrowed(v_as_622_, v_i_624_);
if (lean_obj_tag(v_a_650_) == 0)
{
v_a_643_ = v_snd_637_;
goto v___jp_642_;
}
else
{
lean_object* v_val_651_; uint8_t v___x_652_; 
v_val_651_ = lean_ctor_get(v_a_650_, 0);
v___x_652_ = l_Lean_LocalDecl_isImplementationDetail(v_val_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc(v_val_651_);
v___x_653_ = l_Lean_LocalDecl_toExpr(v_val_651_);
v___x_654_ = lean_array_push(v_snd_637_, v___x_653_);
v_a_643_ = v___x_654_;
goto v___jp_642_;
}
else
{
v_a_643_ = v_snd_637_;
goto v___jp_642_;
}
}
v___jp_642_:
{
lean_object* v___x_645_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 1, v_a_643_);
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_645_ = v___x_639_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_a_643_);
v___x_645_ = v_reuseFailAlloc_649_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_624_, v___x_646_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_622_, v_sz_623_, v___x_647_, v___x_645_);
return v___x_648_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_622_ = stack[0].m_obj;
size_t v_sz_623_ = stack[1].m_num;
size_t v_i_624_ = stack[2].m_num;
lean_object* v_b_625_ = stack[3].m_obj;
lean_object* v___y_626_ = stack[4].m_obj;
lean_object* v___y_627_ = stack[5].m_obj;
lean_object* v___y_628_ = stack[6].m_obj;
lean_object* v___y_629_ = stack[7].m_obj;
lean_object* v___y_630_ = stack[8].m_obj;
lean_object* v___y_631_ = stack[9].m_obj;
lean_object* v___y_632_ = stack[10].m_obj;
lean_object* v___y_633_ = stack[11].m_obj;
lean_object* v_res_657_;
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_as_622_, v_sz_623_, v_i_624_, v_b_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5___boxed(lean_object* v_as_658_, lean_object* v_sz_659_, lean_object* v_i_660_, lean_object* v_b_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_659_);
lean_dec(v_sz_659_);
v_i_boxed_672_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_as_658_, v_sz_boxed_671_, v_i_boxed_672_, v_b_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v_as_658_);
return v_res_673_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(lean_object* v_t_674_, lean_object* v_init_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_root_685_; lean_object* v_tail_686_; lean_object* v___x_687_; 
v_root_685_ = lean_ctor_get(v_t_674_, 0);
v_tail_686_ = lean_ctor_get(v_t_674_, 1);
lean_inc_ref(v_init_675_);
v___x_687_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4(v_init_675_, v_root_685_, v_init_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec_ref(v_init_675_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_724_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_724_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_724_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_724_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_a_688_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; 
v_a_692_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v_a_688_, 1);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_a_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_697_; lean_object* v___x_698_; size_t v_sz_699_; size_t v___x_700_; lean_object* v___x_701_; 
lean_del_object(v___x_690_);
v_a_696_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v_a_688_, 1);
v___x_697_ = lean_box(0);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_a_696_);
v_sz_699_ = lean_array_size(v_tail_686_);
v___x_700_ = ((size_t)0ULL);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5(v_tail_686_, v_sz_699_, v___x_700_, v___x_698_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_715_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_715_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_715_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_715_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_fst_706_; 
v_fst_706_ = lean_ctor_get(v_a_702_, 0);
if (lean_obj_tag(v_fst_706_) == 0)
{
lean_object* v_snd_707_; lean_object* v___x_709_; 
v_snd_707_ = lean_ctor_get(v_a_702_, 1);
lean_inc(v_snd_707_);
lean_dec(v_a_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v_snd_707_);
v___x_709_ = v___x_704_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_snd_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
else
{
lean_object* v_val_711_; lean_object* v___x_713_; 
lean_inc_ref(v_fst_706_);
lean_dec(v_a_702_);
v_val_711_ = lean_ctor_get(v_fst_706_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v_fst_706_, 1);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v_val_711_);
v___x_713_ = v___x_704_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_val_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
v_a_716_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_701_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_701_);
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
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_725_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_687_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_687_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_674_ = stack[0].m_obj;
lean_object* v_init_675_ = stack[1].m_obj;
lean_object* v___y_676_ = stack[2].m_obj;
lean_object* v___y_677_ = stack[3].m_obj;
lean_object* v___y_678_ = stack[4].m_obj;
lean_object* v___y_679_ = stack[5].m_obj;
lean_object* v___y_680_ = stack[6].m_obj;
lean_object* v___y_681_ = stack[7].m_obj;
lean_object* v___y_682_ = stack[8].m_obj;
lean_object* v___y_683_ = stack[9].m_obj;
lean_object* v_res_733_;
v_res_733_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_t_674_, v_init_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3___boxed(lean_object* v_t_734_, lean_object* v_init_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_t_734_, v_init_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_t_734_);
return v_res_745_;
}
}
lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_lctx_757_; lean_object* v_decls_758_; lean_object* v_hs_759_; lean_object* v___x_760_; 
v_lctx_757_ = lean_ctor_get(v___y_752_, 2);
v_decls_758_ = lean_ctor_get(v_lctx_757_, 1);
v_hs_759_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___closed__0));
v___x_760_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3(v_decls_758_, v_hs_759_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
return v___x_760_;
}
}
LEAN_EXPORT void l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_748_ = stack[0].m_obj;
lean_object* v___y_749_ = stack[1].m_obj;
lean_object* v___y_750_ = stack[2].m_obj;
lean_object* v___y_751_ = stack[3].m_obj;
lean_object* v___y_752_ = stack[4].m_obj;
lean_object* v___y_753_ = stack[5].m_obj;
lean_object* v___y_754_ = stack[6].m_obj;
lean_object* v___y_755_ = stack[7].m_obj;
lean_object* v_res_761_;
v_res_761_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3___boxed(lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_771_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(size_t v_sz_772_, size_t v_i_773_, lean_object* v_bs_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_lt(v_i_773_, v_sz_772_);
if (v___x_775_ == 0)
{
return v_bs_774_;
}
else
{
lean_object* v_v_776_; lean_object* v___x_777_; lean_object* v_bs_x27_778_; lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v_v_776_ = lean_array_uget(v_bs_774_, v_i_773_);
v___x_777_ = lean_unsigned_to_nat(0u);
v_bs_x27_778_ = lean_array_uset(v_bs_774_, v_i_773_, v___x_777_);
v___x_779_ = l_Lean_Expr_fvarId_x21(v_v_776_);
lean_dec(v_v_776_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_i_773_, v___x_780_);
v___x_782_ = lean_array_uset(v_bs_x27_778_, v_i_773_, v___x_779_);
v_i_773_ = v___x_781_;
v_bs_774_ = v___x_782_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_772_ = stack[0].m_num;
size_t v_i_773_ = stack[1].m_num;
lean_object* v_bs_774_ = stack[2].m_obj;
lean_object* v_res_784_;
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_772_, v_i_773_, v_bs_774_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4___boxed(lean_object* v_sz_785_, lean_object* v_i_786_, lean_object* v_bs_787_){
_start:
{
size_t v_sz_boxed_788_; size_t v_i_boxed_789_; lean_object* v_res_790_; 
v_sz_boxed_788_ = lean_unbox_usize(v_sz_785_);
lean_dec(v_sz_785_);
v_i_boxed_789_ = lean_unbox_usize(v_i_786_);
lean_dec(v_i_786_);
v_res_790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_boxed_788_, v_i_boxed_789_, v_bs_787_);
return v_res_790_;
}
}
lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__2(lean_object* v___x_791_, size_t v_sz_792_, size_t v___x_793_, lean_object* v___x_794_, lean_object* v___x_795_, lean_object* v_stx_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__0(v___x_791_, v_sz_792_, v___x_793_, v___x_794_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_snd_808_; lean_object* v_fst_809_; lean_object* v_fst_810_; lean_object* v_snd_811_; lean_object* v_hyps_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v_snd_808_ = lean_ctor_get(v_a_807_, 1);
lean_inc(v_snd_808_);
v_fst_809_ = lean_ctor_get(v_a_807_, 0);
lean_inc(v_fst_809_);
lean_dec(v_a_807_);
v_fst_810_ = lean_ctor_get(v_snd_808_, 0);
lean_inc(v_fst_810_);
v_snd_811_ = lean_ctor_get(v_snd_808_, 1);
lean_inc(v_snd_811_);
lean_dec(v_snd_808_);
v___x_838_ = lean_unsigned_to_nat(2u);
v___x_839_ = l_Lean_Syntax_getArg(v_stx_796_, v___x_838_);
v___x_840_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_839_);
lean_dec(v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3(v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; size_t v_sz_843_; lean_object* v___x_844_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v_sz_843_ = lean_array_size(v_a_842_);
v___x_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_evalGeneralize_spec__4(v_sz_843_, v___x_793_, v_a_842_);
v_hyps_813_ = v___x_844_;
v___y_814_ = v___y_797_;
v___y_815_ = v___y_798_;
v___y_816_ = v___y_799_;
v___y_817_ = v___y_800_;
v___y_818_ = v___y_801_;
v___y_819_ = v___y_802_;
v___y_820_ = v___y_803_;
v___y_821_ = v___y_804_;
goto v___jp_812_;
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
lean_dec(v_snd_811_);
lean_dec(v_fst_810_);
lean_dec(v_fst_809_);
lean_dec(v___x_795_);
v_a_845_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_841_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_841_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v_hypotheses_853_; lean_object* v___x_854_; 
v_hypotheses_853_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref(v_hypotheses_853_);
lean_dec_ref_known(v___x_840_, 1);
v___x_854_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_853_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v_hyps_813_ = v_a_855_;
v___y_814_ = v___y_797_;
v___y_815_ = v___y_798_;
v___y_816_ = v___y_799_;
v___y_817_ = v___y_800_;
v___y_818_ = v___y_801_;
v___y_819_ = v___y_802_;
v___y_820_ = v___y_803_;
v___y_821_ = v___y_804_;
goto v___jp_812_;
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_snd_811_);
lean_dec(v_fst_810_);
lean_dec(v_fst_809_);
lean_dec(v___x_795_);
v_a_856_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_854_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
v___jp_812_:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_815_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___f_828_; lean_object* v___x_829_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc_n(v_a_823_, 2);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = lean_box(0);
v___x_825_ = 3;
v___x_826_ = lean_box(v___x_825_);
v___x_827_ = lean_box_usize(v___x_793_);
v___f_828_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lam__1___boxed), 18, 9);
lean_closure_set(v___f_828_, 0, v_a_823_);
lean_closure_set(v___f_828_, 1, v_snd_811_);
lean_closure_set(v___f_828_, 2, v_hyps_813_);
lean_closure_set(v___f_828_, 3, v___x_824_);
lean_closure_set(v___f_828_, 4, v___x_826_);
lean_closure_set(v___f_828_, 5, v_fst_809_);
lean_closure_set(v___f_828_, 6, v_fst_810_);
lean_closure_set(v___f_828_, 7, v___x_795_);
lean_closure_set(v___f_828_, 8, v___x_827_);
v___x_829_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalGeneralize_spec__2___redArg(v_a_823_, v___f_828_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
return v___x_829_;
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v_hyps_813_);
lean_dec(v_snd_811_);
lean_dec(v_fst_810_);
lean_dec(v_fst_809_);
lean_dec(v___x_795_);
v_a_830_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_822_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_822_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec(v___x_795_);
v_a_864_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_806_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_806_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalGeneralize___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_791_ = stack[0].m_obj;
size_t v_sz_792_ = stack[1].m_num;
size_t v___x_793_ = stack[2].m_num;
lean_object* v___x_794_ = stack[3].m_obj;
lean_object* v___x_795_ = stack[4].m_obj;
lean_object* v_stx_796_ = stack[5].m_obj;
lean_object* v___y_797_ = stack[6].m_obj;
lean_object* v___y_798_ = stack[7].m_obj;
lean_object* v___y_799_ = stack[8].m_obj;
lean_object* v___y_800_ = stack[9].m_obj;
lean_object* v___y_801_ = stack[10].m_obj;
lean_object* v___y_802_ = stack[11].m_obj;
lean_object* v___y_803_ = stack[12].m_obj;
lean_object* v___y_804_ = stack[13].m_obj;
lean_object* v_res_872_;
v_res_872_ = l_Lean_Elab_Tactic_evalGeneralize___lam__2(v___x_791_, v_sz_792_, v___x_793_, v___x_794_, v___x_795_, v_stx_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed(lean_object* v___x_873_, lean_object* v_sz_874_, lean_object* v___x_875_, lean_object* v___x_876_, lean_object* v___x_877_, lean_object* v_stx_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
size_t v_sz_boxed_888_; size_t v___x_10736__boxed_889_; lean_object* v_res_890_; 
v_sz_boxed_888_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v___x_10736__boxed_889_ = lean_unbox_usize(v___x_875_);
lean_dec(v___x_875_);
v_res_890_ = l_Lean_Elab_Tactic_evalGeneralize___lam__2(v___x_873_, v_sz_boxed_888_, v___x_10736__boxed_889_, v___x_876_, v___x_877_, v_stx_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v_stx_878_);
lean_dec_ref(v___x_873_);
return v_res_890_;
}
}
lean_object* l_Lean_Elab_Tactic_evalGeneralize(lean_object* v_stx_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; size_t v_sz_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___f_918_; lean_object* v___x_919_; 
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = l_Lean_Syntax_getArg(v_stx_900_, v___x_911_);
v___x_913_ = l_Lean_Syntax_getSepArgs(v___x_912_);
lean_dec(v___x_912_);
v___x_914_ = ((lean_object*)(l_Lean_Elab_Tactic_evalGeneralize___closed__2));
v_sz_915_ = lean_array_size(v___x_913_);
v___x_916_ = lean_box_usize(v_sz_915_);
v___x_917_ = ((lean_object*)(l_Lean_Elab_Tactic_evalGeneralize___boxed__const__1));
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___lam__2___boxed), 15, 6);
lean_closure_set(v___f_918_, 0, v___x_913_);
lean_closure_set(v___f_918_, 1, v___x_916_);
lean_closure_set(v___f_918_, 2, v___x_917_);
lean_closure_set(v___f_918_, 3, v___x_914_);
lean_closure_set(v___f_918_, 4, v___x_910_);
lean_closure_set(v___f_918_, 5, v_stx_900_);
v___x_919_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_918_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_919_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalGeneralize_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_900_ = stack[0].m_obj;
lean_object* v_a_901_ = stack[1].m_obj;
lean_object* v_a_902_ = stack[2].m_obj;
lean_object* v_a_903_ = stack[3].m_obj;
lean_object* v_a_904_ = stack[4].m_obj;
lean_object* v_a_905_ = stack[5].m_obj;
lean_object* v_a_906_ = stack[6].m_obj;
lean_object* v_a_907_ = stack[7].m_obj;
lean_object* v_a_908_ = stack[8].m_obj;
lean_object* v_res_920_;
v_res_920_ = l_Lean_Elab_Tactic_evalGeneralize(v_stx_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGeneralize___boxed(lean_object* v_stx_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Elab_Tactic_evalGeneralize(v_stx_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_931_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(lean_object* v_as_932_, size_t v_sz_933_, size_t v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___redArg(v_as_932_, v_sz_933_, v_i_934_, v_b_935_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_945_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_932_ = stack[0].m_obj;
size_t v_sz_933_ = stack[1].m_num;
size_t v_i_934_ = stack[2].m_num;
lean_object* v_b_935_ = stack[3].m_obj;
lean_object* v___y_936_ = stack[4].m_obj;
lean_object* v___y_937_ = stack[5].m_obj;
lean_object* v___y_938_ = stack[6].m_obj;
lean_object* v___y_939_ = stack[7].m_obj;
lean_object* v___y_940_ = stack[8].m_obj;
lean_object* v___y_941_ = stack[9].m_obj;
lean_object* v___y_942_ = stack[10].m_obj;
lean_object* v___y_943_ = stack[11].m_obj;
lean_object* v_res_946_;
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(v_as_932_, v_sz_933_, v_i_934_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
stack->m_obj
 = v_res_946_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1___boxed(lean_object* v_as_947_, lean_object* v_sz_948_, lean_object* v_i_949_, lean_object* v_b_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_948_);
lean_dec(v_sz_948_);
v_i_boxed_961_ = lean_unbox_usize(v_i_949_);
lean_dec(v_i_949_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalGeneralize_spec__1(v_as_947_, v_sz_boxed_960_, v_i_boxed_961_, v_b_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec_ref(v_as_947_);
return v_res_962_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(lean_object* v_as_963_, size_t v_sz_964_, size_t v_i_965_, lean_object* v_b_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___redArg(v_as_963_, v_sz_964_, v_i_965_, v_b_966_);
return v___x_976_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_963_ = stack[0].m_obj;
size_t v_sz_964_ = stack[1].m_num;
size_t v_i_965_ = stack[2].m_num;
lean_object* v_b_966_ = stack[3].m_obj;
lean_object* v___y_967_ = stack[4].m_obj;
lean_object* v___y_968_ = stack[5].m_obj;
lean_object* v___y_969_ = stack[6].m_obj;
lean_object* v___y_970_ = stack[7].m_obj;
lean_object* v___y_971_ = stack[8].m_obj;
lean_object* v___y_972_ = stack[9].m_obj;
lean_object* v___y_973_ = stack[10].m_obj;
lean_object* v___y_974_ = stack[11].m_obj;
lean_object* v_res_977_;
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(v_as_963_, v_sz_964_, v_i_965_, v_b_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9___boxed(lean_object* v_as_978_, lean_object* v_sz_979_, lean_object* v_i_980_, lean_object* v_b_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
size_t v_sz_boxed_991_; size_t v_i_boxed_992_; lean_object* v_res_993_; 
v_sz_boxed_991_ = lean_unbox_usize(v_sz_979_);
lean_dec(v_sz_979_);
v_i_boxed_992_ = lean_unbox_usize(v_i_980_);
lean_dec(v_i_980_);
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__5_spec__9(v_as_978_, v_sz_boxed_991_, v_i_boxed_992_, v_b_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec_ref(v_as_978_);
return v_res_993_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(lean_object* v_as_994_, size_t v_sz_995_, size_t v_i_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___redArg(v_as_994_, v_sz_995_, v_i_996_, v_b_997_);
return v___x_1007_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_994_ = stack[0].m_obj;
size_t v_sz_995_ = stack[1].m_num;
size_t v_i_996_ = stack[2].m_num;
lean_object* v_b_997_ = stack[3].m_obj;
lean_object* v___y_998_ = stack[4].m_obj;
lean_object* v___y_999_ = stack[5].m_obj;
lean_object* v___y_1000_ = stack[6].m_obj;
lean_object* v___y_1001_ = stack[7].m_obj;
lean_object* v___y_1002_ = stack[8].m_obj;
lean_object* v___y_1003_ = stack[9].m_obj;
lean_object* v___y_1004_ = stack[10].m_obj;
lean_object* v___y_1005_ = stack[11].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(v_as_994_, v_sz_995_, v_i_996_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* v_as_1009_, lean_object* v_sz_1010_, lean_object* v_i_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
size_t v_sz_boxed_1022_; size_t v_i_boxed_1023_; lean_object* v_res_1024_; 
v_sz_boxed_1022_ = lean_unbox_usize(v_sz_1010_);
lean_dec(v_sz_1010_);
v_i_boxed_1023_ = lean_unbox_usize(v_i_1011_);
lean_dec(v_i_1011_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Elab_Tactic_evalGeneralize_spec__3_spec__3_spec__4_spec__7_spec__8(v_as_1009_, v_sz_boxed_1022_, v_i_boxed_1023_, v_b_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec_ref(v_as_1009_);
return v_res_1024_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1(){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1042_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1043_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__4));
v___x_1044_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7));
v___x_1045_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGeneralize___boxed), 10, 0);
v___x_1046_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1042_, v___x_1043_, v___x_1044_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1047_;
v_res_1047_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
stack->m_obj
 = v_res_1047_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___boxed(lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1();
return v_res_1049_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3(){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize__1___closed__7));
v___x_1077_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___closed__6));
v___x_1078_ = l_Lean_addBuiltinDeclarationRanges(v___x_1076_, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1079_;
v_res_1079_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
stack->m_obj
 = v_res_1079_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3___boxed(lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Lean_Elab_Tactic_Generalize_0__Lean_Elab_Tactic_evalGeneralize___regBuiltin_Lean_Elab_Tactic_evalGeneralize_declRange__3();
return v_res_1081_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Generalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
