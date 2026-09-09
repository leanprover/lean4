// Lean compiler output
// Module: Lean.Elab.Tactic.Classical
// Imports: public import Lean.Elab.Tactic.Basic
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_Meta_instanceExtension;
lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasMissing(lean_object*);
lean_object* l_Lean_Meta_addInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addBuiltinIncrementalElab(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "propDecidable"};
static const lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 239, 88, 215, 135, 192, 113, 64)}};
static const lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addInstance___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_classical___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_classical___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_classical___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_evalClassical___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalTactic___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalClassical___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "classical"};
static const lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(29, 138, 254, 133, 236, 159, 90, 21)}};
static const lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalClassical"};
static const lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 86, 92, 131, 125, 72, 228, 49)}};
static const lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v_fst_2_; 
v_fst_2_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_fst_2_);
return v_fst_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__0___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Tactic_classical___redArg___lam__0(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__1(lean_object* v___x_5_, lean_object* v_x_6_){
_start:
{
lean_inc(v___x_5_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed(lean_object* v___x_7_, lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_Tactic_classical___redArg___lam__1(v___x_7_, v_x_8_);
lean_dec(v_x_8_);
lean_dec(v___x_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__2(lean_object* v_toFunctor_10_, lean_object* v___x_11_, lean_object* v_modifyEnv_12_, lean_object* v_inst_13_, lean_object* v_t_14_, lean_object* v___f_15_, lean_object* v_____r_16_){
_start:
{
lean_object* v_map_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___f_20_; lean_object* v_y_21_; lean_object* v___x_22_; 
v_map_17_ = lean_ctor_get(v_toFunctor_10_, 0);
lean_inc(v_map_17_);
lean_dec_ref(v_toFunctor_10_);
v___x_18_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope), 5, 4);
lean_closure_set(v___x_18_, 0, lean_box(0));
lean_closure_set(v___x_18_, 1, lean_box(0));
lean_closure_set(v___x_18_, 2, lean_box(0));
lean_closure_set(v___x_18_, 3, v___x_11_);
v___x_19_ = lean_apply_1(v_modifyEnv_12_, v___x_18_);
v___f_20_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_classical___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_20_, 0, v___x_19_);
v_y_21_ = lean_apply_4(v_inst_13_, lean_box(0), lean_box(0), v_t_14_, v___f_20_);
v___x_22_ = lean_apply_4(v_map_17_, lean_box(0), lean_box(0), v___f_15_, v_y_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg___lam__3(lean_object* v_inst_33_, lean_object* v_toBind_34_, lean_object* v___f_35_, lean_object* v_____r_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = ((lean_object*)(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__3));
v___x_38_ = lean_apply_2(v_inst_33_, lean_box(0), v___x_37_);
v___x_39_ = lean_apply_4(v_toBind_34_, lean_box(0), lean_box(0), v___x_38_, v___f_35_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___redArg___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = l_Lean_Meta_instanceExtension;
v___x_42_ = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope), 5, 4);
lean_closure_set(v___x_42_, 0, lean_box(0));
lean_closure_set(v___x_42_, 1, lean_box(0));
lean_closure_set(v___x_42_, 2, lean_box(0));
lean_closure_set(v___x_42_, 3, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___redArg(lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_t_47_){
_start:
{
lean_object* v_toApplicative_48_; lean_object* v_toBind_49_; lean_object* v_modifyEnv_50_; lean_object* v_toFunctor_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; 
v_toApplicative_48_ = lean_ctor_get(v_inst_43_, 0);
lean_inc_ref(v_toApplicative_48_);
v_toBind_49_ = lean_ctor_get(v_inst_43_, 1);
lean_inc_n(v_toBind_49_, 2);
lean_dec_ref(v_inst_43_);
v_modifyEnv_50_ = lean_ctor_get(v_inst_44_, 1);
lean_inc_n(v_modifyEnv_50_, 2);
lean_dec_ref(v_inst_44_);
v_toFunctor_51_ = lean_ctor_get(v_toApplicative_48_, 0);
lean_inc_ref(v_toFunctor_51_);
lean_dec_ref(v_toApplicative_48_);
v___f_52_ = ((lean_object*)(l_Lean_Elab_Tactic_classical___redArg___closed__0));
v___x_53_ = l_Lean_Meta_instanceExtension;
v___x_54_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___redArg___closed__1, &l_Lean_Elab_Tactic_classical___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_classical___redArg___closed__1);
v___x_55_ = lean_apply_1(v_modifyEnv_50_, v___x_54_);
v___f_56_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_classical___redArg___lam__2), 7, 6);
lean_closure_set(v___f_56_, 0, v_toFunctor_51_);
lean_closure_set(v___f_56_, 1, v___x_53_);
lean_closure_set(v___f_56_, 2, v_modifyEnv_50_);
lean_closure_set(v___f_56_, 3, v_inst_45_);
lean_closure_set(v___f_56_, 4, v_t_47_);
lean_closure_set(v___f_56_, 5, v___f_52_);
v___f_57_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_classical___redArg___lam__3), 4, 3);
lean_closure_set(v___f_57_, 0, v_inst_46_);
lean_closure_set(v___f_57_, 1, v_toBind_49_);
lean_closure_set(v___f_57_, 2, v___f_56_);
v___x_58_ = lean_apply_4(v_toBind_49_, lean_box(0), lean_box(0), v___x_55_, v___f_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical(lean_object* v_m_59_, lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_t_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Elab_Tactic_classical___redArg(v_inst_61_, v_inst_62_, v_inst_63_, v_inst_64_, v_t_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(lean_object* v___y_67_, lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v___y_70_, lean_object* v___x_71_, lean_object* v_a_x3f_72_){
_start:
{
lean_object* v___x_74_; lean_object* v_env_75_; lean_object* v_nextMacroScope_76_; lean_object* v_ngen_77_; lean_object* v_auxDeclNGen_78_; lean_object* v_traceState_79_; lean_object* v_messages_80_; lean_object* v_infoState_81_; lean_object* v_snapshotTasks_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_107_; 
v___x_74_ = lean_st_ref_take(v___y_67_);
v_env_75_ = lean_ctor_get(v___x_74_, 0);
v_nextMacroScope_76_ = lean_ctor_get(v___x_74_, 1);
v_ngen_77_ = lean_ctor_get(v___x_74_, 2);
v_auxDeclNGen_78_ = lean_ctor_get(v___x_74_, 3);
v_traceState_79_ = lean_ctor_get(v___x_74_, 4);
v_messages_80_ = lean_ctor_get(v___x_74_, 6);
v_infoState_81_ = lean_ctor_get(v___x_74_, 7);
v_snapshotTasks_82_ = lean_ctor_get(v___x_74_, 8);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v___x_74_, 5);
lean_dec(v_unused_108_);
v___x_84_ = v___x_74_;
v_isShared_85_ = v_isSharedCheck_107_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_snapshotTasks_82_);
lean_inc(v_infoState_81_);
lean_inc(v_messages_80_);
lean_inc(v_traceState_79_);
lean_inc(v_auxDeclNGen_78_);
lean_inc(v_ngen_77_);
lean_inc(v_nextMacroScope_76_);
lean_inc(v_env_75_);
lean_dec(v___x_74_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_107_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = l_Lean_ScopedEnvExtension_popScope___redArg(v___x_68_, v_env_75_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 5, v___x_69_);
lean_ctor_set(v___x_84_, 0, v___x_86_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_nextMacroScope_76_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v_ngen_77_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v_auxDeclNGen_78_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_traceState_79_);
lean_ctor_set(v_reuseFailAlloc_106_, 5, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_106_, 6, v_messages_80_);
lean_ctor_set(v_reuseFailAlloc_106_, 7, v_infoState_81_);
lean_ctor_set(v_reuseFailAlloc_106_, 8, v_snapshotTasks_82_);
v___x_88_ = v_reuseFailAlloc_106_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_mctx_91_; lean_object* v_zetaDeltaFVarIds_92_; lean_object* v_postponed_93_; lean_object* v_diag_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_104_; 
v___x_89_ = lean_st_ref_put(v___y_67_, v___x_88_);
v___x_90_ = lean_st_ref_take(v___y_70_);
v_mctx_91_ = lean_ctor_get(v___x_90_, 0);
v_zetaDeltaFVarIds_92_ = lean_ctor_get(v___x_90_, 2);
v_postponed_93_ = lean_ctor_get(v___x_90_, 3);
v_diag_94_ = lean_ctor_get(v___x_90_, 4);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_90_, 1);
lean_dec(v_unused_105_);
v___x_96_ = v___x_90_;
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_diag_94_);
lean_inc(v_postponed_93_);
lean_inc(v_zetaDeltaFVarIds_92_);
lean_inc(v_mctx_91_);
lean_dec(v___x_90_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___x_71_);
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_mctx_91_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_zetaDeltaFVarIds_92_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v_postponed_93_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v_diag_94_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_st_ref_put(v___y_70_, v___x_99_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0___boxed(lean_object* v___y_109_, lean_object* v___x_110_, lean_object* v___x_111_, lean_object* v___y_112_, lean_object* v___x_113_, lean_object* v_a_x3f_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_109_, v___x_110_, v___x_111_, v___y_112_, v___x_113_, v_a_x3f_114_);
lean_dec(v_a_x3f_114_);
lean_dec(v___y_112_);
lean_dec(v___y_109_);
return v_res_116_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
v___x_123_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
lean_ctor_set(v___x_123_, 2, v___x_122_);
lean_ctor_set(v___x_123_, 3, v___x_122_);
lean_ctor_set(v___x_123_, 4, v___x_122_);
lean_ctor_set(v___x_123_, 5, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(lean_object* v_t_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; lean_object* v_env_135_; lean_object* v_nextMacroScope_136_; lean_object* v_ngen_137_; lean_object* v_auxDeclNGen_138_; lean_object* v_traceState_139_; lean_object* v_messages_140_; lean_object* v_infoState_141_; lean_object* v_snapshotTasks_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_209_; 
v___x_134_ = lean_st_ref_take(v___y_132_);
v_env_135_ = lean_ctor_get(v___x_134_, 0);
v_nextMacroScope_136_ = lean_ctor_get(v___x_134_, 1);
v_ngen_137_ = lean_ctor_get(v___x_134_, 2);
v_auxDeclNGen_138_ = lean_ctor_get(v___x_134_, 3);
v_traceState_139_ = lean_ctor_get(v___x_134_, 4);
v_messages_140_ = lean_ctor_get(v___x_134_, 6);
v_infoState_141_ = lean_ctor_get(v___x_134_, 7);
v_snapshotTasks_142_ = lean_ctor_get(v___x_134_, 8);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_134_, 5);
lean_dec(v_unused_210_);
v___x_144_ = v___x_134_;
v_isShared_145_ = v_isSharedCheck_209_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_snapshotTasks_142_);
lean_inc(v_infoState_141_);
lean_inc(v_messages_140_);
lean_inc(v_traceState_139_);
lean_inc(v_auxDeclNGen_138_);
lean_inc(v_ngen_137_);
lean_inc(v_nextMacroScope_136_);
lean_inc(v_env_135_);
lean_dec(v___x_134_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_209_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_150_; 
v___x_146_ = l_Lean_Meta_instanceExtension;
v___x_147_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v___x_146_, v_env_135_);
v___x_148_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 5, v___x_148_);
lean_ctor_set(v___x_144_, 0, v___x_147_);
v___x_150_ = v___x_144_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_nextMacroScope_136_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_ngen_137_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_auxDeclNGen_138_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_traceState_139_);
lean_ctor_set(v_reuseFailAlloc_208_, 5, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_208_, 6, v_messages_140_);
lean_ctor_set(v_reuseFailAlloc_208_, 7, v_infoState_141_);
lean_ctor_set(v_reuseFailAlloc_208_, 8, v_snapshotTasks_142_);
v___x_150_ = v_reuseFailAlloc_208_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v_mctx_153_; lean_object* v_zetaDeltaFVarIds_154_; lean_object* v_postponed_155_; lean_object* v_diag_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_206_; 
v___x_151_ = lean_st_ref_put(v___y_132_, v___x_150_);
v___x_152_ = lean_st_ref_take(v___y_130_);
v_mctx_153_ = lean_ctor_get(v___x_152_, 0);
v_zetaDeltaFVarIds_154_ = lean_ctor_get(v___x_152_, 2);
v_postponed_155_ = lean_ctor_get(v___x_152_, 3);
v_diag_156_ = lean_ctor_get(v___x_152_, 4);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v___x_152_, 1);
lean_dec(v_unused_207_);
v___x_158_ = v___x_152_;
v_isShared_159_ = v_isSharedCheck_206_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_diag_156_);
lean_inc(v_postponed_155_);
lean_inc(v_zetaDeltaFVarIds_154_);
lean_inc(v_mctx_153_);
lean_dec(v___x_152_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_206_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_mctx_153_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_160_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_zetaDeltaFVarIds_154_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_postponed_155_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_diag_156_);
v___x_162_ = v_reuseFailAlloc_205_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_163_ = lean_st_ref_put(v___y_130_, v___x_162_);
v___x_164_ = ((lean_object*)(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2));
v___x_165_ = 1;
v___x_166_ = lean_unsigned_to_nat(10u);
v___x_167_ = l_Lean_Meta_addInstance(v___x_164_, v___x_165_, v___x_166_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_r_168_; 
lean_dec_ref_known(v___x_167_, 1);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
v_r_168_ = lean_apply_9(v_t_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
if (lean_obj_tag(v_r_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_185_; 
v_a_169_ = lean_ctor_get(v_r_168_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v_r_168_);
if (v_isSharedCheck_185_ == 0)
{
v___x_171_ = v_r_168_;
v_isShared_172_ = v_isSharedCheck_185_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v_r_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_185_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
lean_inc(v_a_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set_tag(v___x_171_, 1);
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_184_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v___x_175_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_132_, v___x_146_, v___x_148_, v___y_130_, v___x_160_, v___x_174_);
lean_dec_ref(v___x_174_);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v___x_175_, 0);
lean_dec(v_unused_183_);
v___x_177_ = v___x_175_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_dec(v___x_175_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v_a_169_);
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_169_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
v_a_186_ = lean_ctor_get(v_r_168_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v_r_168_, 1);
v___x_187_ = lean_box(0);
v___x_188_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_132_, v___x_146_, v___x_148_, v___y_130_, v___x_160_, v___x_187_);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v___x_188_, 0);
lean_dec(v_unused_196_);
v___x_190_ = v___x_188_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_dec(v___x_188_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 1);
lean_ctor_set(v___x_190_, 0, v_a_186_);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_186_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_t_124_);
v_a_197_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_167_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_167_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___boxed(lean_object* v_t_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v_t_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(lean_object* v_00_u03b1_222_, lean_object* v_t_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v_t_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___boxed(lean_object* v_00_u03b1_234_, lean_object* v_t_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(v_00_u03b1_234_, v_t_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(lean_object* v_stx_246_, lean_object* v_act_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
uint8_t v_suppressElabErrors_257_; 
v_suppressElabErrors_257_ = lean_ctor_get_uint8(v___y_254_, sizeof(void*)*10 + 1);
if (v_suppressElabErrors_257_ == 0)
{
lean_object* v_toCold_258_; lean_object* v_options_259_; lean_object* v_currRecDepth_260_; lean_object* v_maxRecDepth_261_; lean_object* v_currNamespace_262_; lean_object* v_openDecls_263_; lean_object* v_initHeartbeats_264_; lean_object* v_maxHeartbeats_265_; lean_object* v_currMacroScope_266_; uint8_t v_diag_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_toCold_258_ = lean_ctor_get(v___y_254_, 0);
v_options_259_ = lean_ctor_get(v___y_254_, 1);
v_currRecDepth_260_ = lean_ctor_get(v___y_254_, 2);
v_maxRecDepth_261_ = lean_ctor_get(v___y_254_, 3);
v_currNamespace_262_ = lean_ctor_get(v___y_254_, 5);
v_openDecls_263_ = lean_ctor_get(v___y_254_, 6);
v_initHeartbeats_264_ = lean_ctor_get(v___y_254_, 7);
v_maxHeartbeats_265_ = lean_ctor_get(v___y_254_, 8);
v_currMacroScope_266_ = lean_ctor_get(v___y_254_, 9);
v_diag_267_ = lean_ctor_get_uint8(v___y_254_, sizeof(void*)*10);
lean_inc(v_currMacroScope_266_);
lean_inc(v_maxHeartbeats_265_);
lean_inc(v_initHeartbeats_264_);
lean_inc(v_openDecls_263_);
lean_inc(v_currNamespace_262_);
lean_inc(v_maxRecDepth_261_);
lean_inc(v_currRecDepth_260_);
lean_inc_ref(v_options_259_);
lean_inc_ref(v_toCold_258_);
v___x_268_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_268_, 0, v_toCold_258_);
lean_ctor_set(v___x_268_, 1, v_options_259_);
lean_ctor_set(v___x_268_, 2, v_currRecDepth_260_);
lean_ctor_set(v___x_268_, 3, v_maxRecDepth_261_);
lean_ctor_set(v___x_268_, 4, v_stx_246_);
lean_ctor_set(v___x_268_, 5, v_currNamespace_262_);
lean_ctor_set(v___x_268_, 6, v_openDecls_263_);
lean_ctor_set(v___x_268_, 7, v_initHeartbeats_264_);
lean_ctor_set(v___x_268_, 8, v_maxHeartbeats_265_);
lean_ctor_set(v___x_268_, 9, v_currMacroScope_266_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*10, v_diag_267_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*10 + 1, v_suppressElabErrors_257_);
lean_inc(v___y_255_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
v___x_269_ = lean_apply_9(v_act_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___x_268_, v___y_255_, lean_box(0));
return v___x_269_;
}
else
{
lean_object* v_toCold_270_; lean_object* v_options_271_; lean_object* v_currRecDepth_272_; lean_object* v_maxRecDepth_273_; lean_object* v_currNamespace_274_; lean_object* v_openDecls_275_; lean_object* v_initHeartbeats_276_; lean_object* v_maxHeartbeats_277_; lean_object* v_currMacroScope_278_; uint8_t v_diag_279_; uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_toCold_270_ = lean_ctor_get(v___y_254_, 0);
v_options_271_ = lean_ctor_get(v___y_254_, 1);
v_currRecDepth_272_ = lean_ctor_get(v___y_254_, 2);
v_maxRecDepth_273_ = lean_ctor_get(v___y_254_, 3);
v_currNamespace_274_ = lean_ctor_get(v___y_254_, 5);
v_openDecls_275_ = lean_ctor_get(v___y_254_, 6);
v_initHeartbeats_276_ = lean_ctor_get(v___y_254_, 7);
v_maxHeartbeats_277_ = lean_ctor_get(v___y_254_, 8);
v_currMacroScope_278_ = lean_ctor_get(v___y_254_, 9);
v_diag_279_ = lean_ctor_get_uint8(v___y_254_, sizeof(void*)*10);
v___x_280_ = l_Lean_Syntax_hasMissing(v_stx_246_);
lean_inc(v_currMacroScope_278_);
lean_inc(v_maxHeartbeats_277_);
lean_inc(v_initHeartbeats_276_);
lean_inc(v_openDecls_275_);
lean_inc(v_currNamespace_274_);
lean_inc(v_maxRecDepth_273_);
lean_inc(v_currRecDepth_272_);
lean_inc_ref(v_options_271_);
lean_inc_ref(v_toCold_270_);
v___x_281_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_281_, 0, v_toCold_270_);
lean_ctor_set(v___x_281_, 1, v_options_271_);
lean_ctor_set(v___x_281_, 2, v_currRecDepth_272_);
lean_ctor_set(v___x_281_, 3, v_maxRecDepth_273_);
lean_ctor_set(v___x_281_, 4, v_stx_246_);
lean_ctor_set(v___x_281_, 5, v_currNamespace_274_);
lean_ctor_set(v___x_281_, 6, v_openDecls_275_);
lean_ctor_set(v___x_281_, 7, v_initHeartbeats_276_);
lean_ctor_set(v___x_281_, 8, v_maxHeartbeats_277_);
lean_ctor_set(v___x_281_, 9, v_currMacroScope_278_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*10, v_diag_279_);
lean_ctor_set_uint8(v___x_281_, sizeof(void*)*10 + 1, v___x_280_);
lean_inc(v___y_255_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
v___x_282_ = lean_apply_9(v_act_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___x_281_, v___y_255_, lean_box(0));
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_stx_283_, lean_object* v_act_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_283_, v_act_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(lean_object* v_act_295_, lean_object* v_snd_296_, lean_object* v_____r_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_inc(v_snd_296_);
v___x_307_ = lean_apply_1(v_act_295_, v_snd_296_);
v___x_308_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_snd_296_, v___x_307_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_act_309_, lean_object* v_snd_310_, lean_object* v_____r_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_309_, v_snd_310_, v_____r_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(lean_object* v_val_322_, lean_object* v___x_323_, lean_object* v___f_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_tacSnap_x3f_338_; 
v_tacSnap_x3f_338_ = lean_ctor_get(v___y_327_, 6);
if (lean_obj_tag(v_tacSnap_x3f_338_) == 0)
{
goto v___jp_334_;
}
else
{
lean_object* v_val_339_; lean_object* v_old_x3f_340_; 
v_val_339_ = lean_ctor_get(v_tacSnap_x3f_338_, 0);
v_old_x3f_340_ = lean_ctor_get(v_val_339_, 0);
if (lean_obj_tag(v_old_x3f_340_) == 0)
{
goto v___jp_334_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec_ref(v___x_323_);
lean_dec_ref(v_val_322_);
v___x_341_ = lean_box(0);
v___x_342_ = lean_apply_10(v___f_324_, v___x_341_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, lean_box(0));
return v___x_342_;
}
}
v___jp_334_:
{
lean_object* v_val_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_val_335_ = lean_ctor_get(v_val_322_, 1);
lean_inc(v_val_335_);
lean_dec_ref(v_val_322_);
v___x_336_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_323_, v_val_335_);
v___x_337_ = lean_apply_10(v___f_324_, v___x_336_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, lean_box(0));
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_val_343_, lean_object* v___x_344_, lean_object* v___f_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_343_, v___x_344_, v___f_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(lean_object* v_split_357_, lean_object* v_act_358_, lean_object* v_stx_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___y_370_; uint8_t v___y_371_; uint8_t v___y_372_; lean_object* v___y_373_; uint8_t v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; uint8_t v___y_377_; uint8_t v___y_378_; uint8_t v___y_379_; uint8_t v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; uint8_t v___y_383_; lean_object* v___y_384_; uint8_t v___y_385_; lean_object* v___y_386_; uint8_t v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v_new_393_; lean_object* v___y_394_; uint8_t v___y_395_; uint8_t v___y_396_; lean_object* v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; uint8_t v___y_401_; uint8_t v___y_402_; uint8_t v___y_403_; uint8_t v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; uint8_t v___y_407_; uint8_t v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; uint8_t v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___x_416_; lean_object* v_fst_417_; lean_object* v_snd_418_; lean_object* v_options_419_; lean_object* v_declName_x3f_420_; lean_object* v_macroStack_421_; uint8_t v_mayPostpone_422_; uint8_t v_errToSorry_423_; lean_object* v_autoBoundImplicitContext_424_; lean_object* v_autoBoundImplicitForbidden_425_; lean_object* v_sectionVars_426_; lean_object* v_sectionFVars_427_; uint8_t v_implicitLambda_428_; uint8_t v_heedElabAsElim_429_; uint8_t v_isNoncomputableSection_430_; uint8_t v_isMetaSection_431_; uint8_t v_ignoreTCFailures_432_; uint8_t v_inPattern_433_; lean_object* v_tacSnap_x3f_434_; uint8_t v_saveRecAppSyntax_435_; uint8_t v_holesAsSyntheticOpaque_436_; uint8_t v_checkDeprecated_437_; lean_object* v_fixedTermElabs_438_; lean_object* v___y_440_; lean_object* v___f_461_; 
lean_inc_ref(v_split_357_);
v___x_416_ = lean_apply_1(v_split_357_, v_stx_359_);
v_fst_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_fst_417_);
v_snd_418_ = lean_ctor_get(v___x_416_, 1);
lean_inc_n(v_snd_418_, 2);
lean_dec_ref(v___x_416_);
v_options_419_ = lean_ctor_get(v___y_366_, 1);
v_declName_x3f_420_ = lean_ctor_get(v___y_362_, 0);
v_macroStack_421_ = lean_ctor_get(v___y_362_, 1);
v_mayPostpone_422_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8);
v_errToSorry_423_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_424_ = lean_ctor_get(v___y_362_, 2);
v_autoBoundImplicitForbidden_425_ = lean_ctor_get(v___y_362_, 3);
v_sectionVars_426_ = lean_ctor_get(v___y_362_, 4);
v_sectionFVars_427_ = lean_ctor_get(v___y_362_, 5);
v_implicitLambda_428_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 2);
v_heedElabAsElim_429_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_430_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 4);
v_isMetaSection_431_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_432_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 6);
v_inPattern_433_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_434_ = lean_ctor_get(v___y_362_, 6);
v_saveRecAppSyntax_435_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_436_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 9);
v_checkDeprecated_437_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 10);
v_fixedTermElabs_438_ = lean_ctor_get(v___y_362_, 7);
lean_inc_ref(v_act_358_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_461_, 0, v_act_358_);
lean_closure_set(v___f_461_, 1, v_snd_418_);
if (lean_obj_tag(v_tacSnap_x3f_434_) == 0)
{
lean_dec_ref(v___f_461_);
goto v___jp_462_;
}
else
{
lean_object* v_val_465_; lean_object* v_old_x3f_466_; 
v_val_465_ = lean_ctor_get(v_tacSnap_x3f_434_, 0);
v_old_x3f_466_ = lean_ctor_get(v_val_465_, 0);
if (lean_obj_tag(v_old_x3f_466_) == 1)
{
lean_object* v_val_467_; lean_object* v___x_468_; lean_object* v___f_469_; 
lean_dec(v_snd_418_);
lean_dec_ref(v_act_358_);
v_val_467_ = lean_ctor_get(v_old_x3f_466_, 0);
v___x_468_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___closed__0));
lean_inc(v_val_467_);
v___f_469_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_469_, 0, v_val_467_);
lean_closure_set(v___f_469_, 1, v___x_468_);
lean_closure_set(v___f_469_, 2, v___f_461_);
v___y_440_ = v___f_469_;
goto v___jp_439_;
}
else
{
lean_dec_ref(v___f_461_);
goto v___jp_462_;
}
}
v___jp_369_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc_ref(v___y_373_);
lean_inc(v___y_382_);
lean_inc(v___y_375_);
lean_inc_ref(v___y_381_);
lean_inc(v___y_384_);
lean_inc(v___y_386_);
lean_inc(v___y_370_);
v___x_390_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_390_, 0, v___y_370_);
lean_ctor_set(v___x_390_, 1, v___y_386_);
lean_ctor_set(v___x_390_, 2, v___y_384_);
lean_ctor_set(v___x_390_, 3, v___y_381_);
lean_ctor_set(v___x_390_, 4, v___y_375_);
lean_ctor_set(v___x_390_, 5, v___y_382_);
lean_ctor_set(v___x_390_, 6, v___y_389_);
lean_ctor_set(v___x_390_, 7, v___y_373_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8, v___y_374_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 1, v___y_387_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 2, v___y_383_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 3, v___y_371_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 4, v___y_385_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 5, v___y_379_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 6, v___y_372_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 7, v___y_378_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 8, v___y_377_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 9, v___y_376_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*8 + 10, v___y_380_);
lean_inc(v___y_367_);
lean_inc_ref(v___y_366_);
lean_inc(v___y_365_);
lean_inc_ref(v___y_364_);
lean_inc(v___y_363_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_360_);
v___x_391_ = lean_apply_9(v___y_388_, v___y_360_, v___y_361_, v___x_390_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, lean_box(0));
return v___x_391_;
}
v___jp_392_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___y_413_);
lean_ctor_set(v___x_414_, 1, v_new_393_);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
v___y_370_ = v___y_394_;
v___y_371_ = v___y_395_;
v___y_372_ = v___y_396_;
v___y_373_ = v___y_397_;
v___y_374_ = v___y_398_;
v___y_375_ = v___y_399_;
v___y_376_ = v___y_400_;
v___y_377_ = v___y_401_;
v___y_378_ = v___y_402_;
v___y_379_ = v___y_403_;
v___y_380_ = v___y_404_;
v___y_381_ = v___y_405_;
v___y_382_ = v___y_406_;
v___y_383_ = v___y_407_;
v___y_384_ = v___y_409_;
v___y_385_ = v___y_408_;
v___y_386_ = v___y_410_;
v___y_387_ = v___y_411_;
v___y_388_ = v___y_412_;
v___y_389_ = v___x_415_;
goto v___jp_369_;
}
v___jp_439_:
{
if (lean_obj_tag(v_tacSnap_x3f_434_) == 0)
{
lean_dec(v_fst_417_);
lean_dec_ref(v_split_357_);
v___y_370_ = v_declName_x3f_420_;
v___y_371_ = v_heedElabAsElim_429_;
v___y_372_ = v_ignoreTCFailures_432_;
v___y_373_ = v_fixedTermElabs_438_;
v___y_374_ = v_mayPostpone_422_;
v___y_375_ = v_sectionVars_426_;
v___y_376_ = v_holesAsSyntheticOpaque_436_;
v___y_377_ = v_saveRecAppSyntax_435_;
v___y_378_ = v_inPattern_433_;
v___y_379_ = v_isMetaSection_431_;
v___y_380_ = v_checkDeprecated_437_;
v___y_381_ = v_autoBoundImplicitForbidden_425_;
v___y_382_ = v_sectionFVars_427_;
v___y_383_ = v_implicitLambda_428_;
v___y_384_ = v_autoBoundImplicitContext_424_;
v___y_385_ = v_isNoncomputableSection_430_;
v___y_386_ = v_macroStack_421_;
v___y_387_ = v_errToSorry_423_;
v___y_388_ = v___y_440_;
v___y_389_ = v_tacSnap_x3f_434_;
goto v___jp_369_;
}
else
{
lean_object* v_val_441_; lean_object* v_old_x3f_442_; 
v_val_441_ = lean_ctor_get(v_tacSnap_x3f_434_, 0);
v_old_x3f_442_ = lean_ctor_get(v_val_441_, 0);
if (lean_obj_tag(v_old_x3f_442_) == 0)
{
lean_object* v_new_443_; 
lean_dec(v_fst_417_);
lean_dec_ref(v_split_357_);
v_new_443_ = lean_ctor_get(v_val_441_, 1);
lean_inc(v_new_443_);
v_new_393_ = v_new_443_;
v___y_394_ = v_declName_x3f_420_;
v___y_395_ = v_heedElabAsElim_429_;
v___y_396_ = v_ignoreTCFailures_432_;
v___y_397_ = v_fixedTermElabs_438_;
v___y_398_ = v_mayPostpone_422_;
v___y_399_ = v_sectionVars_426_;
v___y_400_ = v_holesAsSyntheticOpaque_436_;
v___y_401_ = v_saveRecAppSyntax_435_;
v___y_402_ = v_inPattern_433_;
v___y_403_ = v_isMetaSection_431_;
v___y_404_ = v_checkDeprecated_437_;
v___y_405_ = v_autoBoundImplicitForbidden_425_;
v___y_406_ = v_sectionFVars_427_;
v___y_407_ = v_implicitLambda_428_;
v___y_408_ = v_isNoncomputableSection_430_;
v___y_409_ = v_autoBoundImplicitContext_424_;
v___y_410_ = v_macroStack_421_;
v___y_411_ = v_errToSorry_423_;
v___y_412_ = v___y_440_;
v___y_413_ = v_old_x3f_442_;
goto v___jp_392_;
}
else
{
lean_object* v_val_444_; lean_object* v_new_445_; lean_object* v_stx_446_; lean_object* v_val_447_; lean_object* v___x_448_; lean_object* v_fst_449_; lean_object* v_snd_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_460_; 
v_val_444_ = lean_ctor_get(v_old_x3f_442_, 0);
v_new_445_ = lean_ctor_get(v_val_441_, 1);
v_stx_446_ = lean_ctor_get(v_val_444_, 0);
v_val_447_ = lean_ctor_get(v_val_444_, 1);
lean_inc(v_stx_446_);
v___x_448_ = lean_apply_1(v_split_357_, v_stx_446_);
v_fst_449_ = lean_ctor_get(v___x_448_, 0);
v_snd_450_ = lean_ctor_get(v___x_448_, 1);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_460_ == 0)
{
v___x_452_ = v___x_448_;
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snd_450_);
lean_inc(v_fst_449_);
lean_dec(v___x_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v___x_454_; 
v___x_454_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_options_419_, v_fst_417_, v_fst_449_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_del_object(v___x_452_);
lean_dec(v_snd_450_);
v___x_455_ = lean_box(0);
lean_inc(v_new_445_);
v_new_393_ = v_new_445_;
v___y_394_ = v_declName_x3f_420_;
v___y_395_ = v_heedElabAsElim_429_;
v___y_396_ = v_ignoreTCFailures_432_;
v___y_397_ = v_fixedTermElabs_438_;
v___y_398_ = v_mayPostpone_422_;
v___y_399_ = v_sectionVars_426_;
v___y_400_ = v_holesAsSyntheticOpaque_436_;
v___y_401_ = v_saveRecAppSyntax_435_;
v___y_402_ = v_inPattern_433_;
v___y_403_ = v_isMetaSection_431_;
v___y_404_ = v_checkDeprecated_437_;
v___y_405_ = v_autoBoundImplicitForbidden_425_;
v___y_406_ = v_sectionFVars_427_;
v___y_407_ = v_implicitLambda_428_;
v___y_408_ = v_isNoncomputableSection_430_;
v___y_409_ = v_autoBoundImplicitContext_424_;
v___y_410_ = v_macroStack_421_;
v___y_411_ = v_errToSorry_423_;
v___y_412_ = v___y_440_;
v___y_413_ = v___x_455_;
goto v___jp_392_;
}
else
{
lean_object* v___x_457_; 
lean_inc(v_val_447_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v_val_447_);
lean_ctor_set(v___x_452_, 0, v_snd_450_);
v___x_457_ = v___x_452_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_snd_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_val_447_);
v___x_457_ = v_reuseFailAlloc_459_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_inc(v_new_445_);
v_new_393_ = v_new_445_;
v___y_394_ = v_declName_x3f_420_;
v___y_395_ = v_heedElabAsElim_429_;
v___y_396_ = v_ignoreTCFailures_432_;
v___y_397_ = v_fixedTermElabs_438_;
v___y_398_ = v_mayPostpone_422_;
v___y_399_ = v_sectionVars_426_;
v___y_400_ = v_holesAsSyntheticOpaque_436_;
v___y_401_ = v_saveRecAppSyntax_435_;
v___y_402_ = v_inPattern_433_;
v___y_403_ = v_isMetaSection_431_;
v___y_404_ = v_checkDeprecated_437_;
v___y_405_ = v_autoBoundImplicitForbidden_425_;
v___y_406_ = v_sectionFVars_427_;
v___y_407_ = v_implicitLambda_428_;
v___y_408_ = v_isNoncomputableSection_430_;
v___y_409_ = v_autoBoundImplicitContext_424_;
v___y_410_ = v_macroStack_421_;
v___y_411_ = v_errToSorry_423_;
v___y_412_ = v___y_440_;
v___y_413_ = v___x_458_;
goto v___jp_392_;
}
}
}
}
}
}
v___jp_462_:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___x_464_, 0, v_act_358_);
lean_closure_set(v___x_464_, 1, v_snd_418_);
lean_closure_set(v___x_464_, 2, v___x_463_);
v___y_440_ = v___x_464_;
goto v___jp_439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(lean_object* v_split_470_, lean_object* v_act_471_, lean_object* v_stx_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_470_, v_act_471_, v_stx_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(lean_object* v_argIdx_486_, lean_object* v_stx_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_488_ = l_Lean_Syntax_getArgs(v_stx_487_);
v___x_489_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_486_);
v___x_490_ = l_Array_toSubarray___redArg(v___x_488_, v___x_489_, v_argIdx_486_);
v___x_491_ = l_Subarray_copy___redArg(v___x_490_);
v___x_492_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1));
v___x_493_ = lean_box(2);
v___x_494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_491_);
v___x_495_ = l_Lean_Syntax_getArg(v_stx_487_, v_argIdx_486_);
lean_dec(v_argIdx_486_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(lean_object* v_argIdx_497_, lean_object* v_stx_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(v_argIdx_497_, v_stx_498_);
lean_dec(v_stx_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(lean_object* v_argIdx_500_, lean_object* v_act_501_, lean_object* v_stx_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___f_512_; lean_object* v___x_513_; 
v___f_512_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_512_, 0, v_argIdx_500_);
v___x_513_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v___f_512_, v_act_501_, v_stx_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(lean_object* v_argIdx_514_, lean_object* v_act_515_, lean_object* v_stx_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_514_, v_act_515_, v_stx_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(lean_object* v_00_u03b1_527_, lean_object* v_argIdx_528_, lean_object* v_act_529_, lean_object* v_stx_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_528_, v_act_529_, v_stx_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(lean_object* v_00_u03b1_541_, lean_object* v_argIdx_542_, lean_object* v_act_543_, lean_object* v_stx_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(v_00_u03b1_541_, v_argIdx_542_, v_act_543_, v_stx_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; lean_object* v_env_560_; lean_object* v___x_561_; lean_object* v_mctx_562_; lean_object* v_options_563_; lean_object* v_currNamespace_564_; lean_object* v_openDecls_565_; lean_object* v___x_566_; lean_object* v_ngen_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_559_ = lean_st_ref_get(v___y_557_);
v_env_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc_ref(v_env_560_);
lean_dec(v___x_559_);
v___x_561_ = lean_st_ref_get(v___y_555_);
v_mctx_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_mctx_562_);
lean_dec(v___x_561_);
v_options_563_ = lean_ctor_get(v___y_556_, 1);
v_currNamespace_564_ = lean_ctor_get(v___y_556_, 5);
v_openDecls_565_ = lean_ctor_get(v___y_556_, 6);
v___x_566_ = lean_st_ref_get(v___y_557_);
v_ngen_567_ = lean_ctor_get(v___x_566_, 2);
lean_inc_ref(v_ngen_567_);
lean_dec(v___x_566_);
v___x_568_ = lean_box(0);
v___x_569_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_565_);
lean_inc(v_currNamespace_564_);
lean_inc_ref(v_options_563_);
v___x_570_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_570_, 0, v_env_560_);
lean_ctor_set(v___x_570_, 1, v___x_568_);
lean_ctor_set(v___x_570_, 2, v___x_569_);
lean_ctor_set(v___x_570_, 3, v_mctx_562_);
lean_ctor_set(v___x_570_, 4, v_options_563_);
lean_ctor_set(v___x_570_, 5, v_currNamespace_564_);
lean_ctor_set(v___x_570_, 6, v_openDecls_565_);
lean_ctor_set(v___x_570_, 7, v_ngen_567_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; lean_object* v_toCold_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_612_; 
v___x_586_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_582_, v___y_583_, v___y_584_);
v_toCold_587_ = lean_ctor_get(v___y_583_, 0);
v_a_588_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_612_ == 0)
{
v___x_590_ = v___x_586_;
v_isShared_591_ = v_isSharedCheck_612_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_612_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_fileMap_592_; lean_object* v_env_593_; lean_object* v_mctx_594_; lean_object* v_options_595_; lean_object* v_currNamespace_596_; lean_object* v_openDecls_597_; lean_object* v_ngen_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_609_; 
v_fileMap_592_ = lean_ctor_get(v_toCold_587_, 1);
v_env_593_ = lean_ctor_get(v_a_588_, 0);
v_mctx_594_ = lean_ctor_get(v_a_588_, 3);
v_options_595_ = lean_ctor_get(v_a_588_, 4);
v_currNamespace_596_ = lean_ctor_get(v_a_588_, 5);
v_openDecls_597_ = lean_ctor_get(v_a_588_, 6);
v_ngen_598_ = lean_ctor_get(v_a_588_, 7);
v_isSharedCheck_609_ = !lean_is_exclusive(v_a_588_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; lean_object* v_unused_611_; 
v_unused_610_ = lean_ctor_get(v_a_588_, 2);
lean_dec(v_unused_610_);
v_unused_611_ = lean_ctor_get(v_a_588_, 1);
lean_dec(v_unused_611_);
v___x_600_ = v_a_588_;
v_isShared_601_ = v_isSharedCheck_609_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_ngen_598_);
lean_inc(v_openDecls_597_);
lean_inc(v_currNamespace_596_);
lean_inc(v_options_595_);
lean_inc(v_mctx_594_);
lean_inc(v_env_593_);
lean_dec(v_a_588_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_609_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
lean_inc_ref(v_fileMap_592_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 2, v_fileMap_592_);
lean_ctor_set(v___x_600_, 1, v___x_602_);
v___x_604_ = v___x_600_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_env_593_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_fileMap_592_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_mctx_594_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_options_595_);
lean_ctor_set(v_reuseFailAlloc_608_, 5, v_currNamespace_596_);
lean_ctor_set(v_reuseFailAlloc_608_, 6, v_openDecls_597_);
lean_ctor_set(v_reuseFailAlloc_608_, 7, v_ngen_598_);
v___x_604_ = v_reuseFailAlloc_608_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_604_);
v___x_606_ = v___x_590_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2___boxed(lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_642_; 
v___x_632_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_642_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_a_633_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_638_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed(lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_652_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(32u);
v___x_654_ = lean_mk_empty_array_with_capacity(v___x_653_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = ((size_t)5ULL);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_unsigned_to_nat(32u);
v___x_659_ = lean_mk_empty_array_with_capacity(v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0);
v___x_661_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
lean_ctor_set(v___x_661_, 2, v___x_657_);
lean_ctor_set(v___x_661_, 3, v___x_657_);
lean_ctor_set_usize(v___x_661_, 4, v___x_656_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; lean_object* v_infoState_665_; lean_object* v_trees_666_; lean_object* v___x_667_; lean_object* v_infoState_668_; lean_object* v_env_669_; lean_object* v_nextMacroScope_670_; lean_object* v_ngen_671_; lean_object* v_auxDeclNGen_672_; lean_object* v_traceState_673_; lean_object* v_cache_674_; lean_object* v_messages_675_; lean_object* v_snapshotTasks_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_697_; 
v___x_664_ = lean_st_ref_get(v___y_662_);
v_infoState_665_ = lean_ctor_get(v___x_664_, 7);
lean_inc_ref(v_infoState_665_);
lean_dec(v___x_664_);
v_trees_666_ = lean_ctor_get(v_infoState_665_, 2);
lean_inc_ref(v_trees_666_);
lean_dec_ref(v_infoState_665_);
v___x_667_ = lean_st_ref_take(v___y_662_);
v_infoState_668_ = lean_ctor_get(v___x_667_, 7);
v_env_669_ = lean_ctor_get(v___x_667_, 0);
v_nextMacroScope_670_ = lean_ctor_get(v___x_667_, 1);
v_ngen_671_ = lean_ctor_get(v___x_667_, 2);
v_auxDeclNGen_672_ = lean_ctor_get(v___x_667_, 3);
v_traceState_673_ = lean_ctor_get(v___x_667_, 4);
v_cache_674_ = lean_ctor_get(v___x_667_, 5);
v_messages_675_ = lean_ctor_get(v___x_667_, 6);
v_snapshotTasks_676_ = lean_ctor_get(v___x_667_, 8);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_697_ == 0)
{
v___x_678_ = v___x_667_;
v_isShared_679_ = v_isSharedCheck_697_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snapshotTasks_676_);
lean_inc(v_infoState_668_);
lean_inc(v_messages_675_);
lean_inc(v_cache_674_);
lean_inc(v_traceState_673_);
lean_inc(v_auxDeclNGen_672_);
lean_inc(v_ngen_671_);
lean_inc(v_nextMacroScope_670_);
lean_inc(v_env_669_);
lean_dec(v___x_667_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_697_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
uint8_t v_enabled_680_; lean_object* v_assignment_681_; lean_object* v_lazyAssignment_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_695_; 
v_enabled_680_ = lean_ctor_get_uint8(v_infoState_668_, sizeof(void*)*3);
v_assignment_681_ = lean_ctor_get(v_infoState_668_, 0);
v_lazyAssignment_682_ = lean_ctor_get(v_infoState_668_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_infoState_668_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_infoState_668_, 2);
lean_dec(v_unused_696_);
v___x_684_ = v_infoState_668_;
v_isShared_685_ = v_isSharedCheck_695_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_lazyAssignment_682_);
lean_inc(v_assignment_681_);
lean_dec(v_infoState_668_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_695_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 2, v___x_686_);
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_assignment_681_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_lazyAssignment_682_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v___x_686_);
lean_ctor_set_uint8(v_reuseFailAlloc_694_, sizeof(void*)*3, v_enabled_680_);
v___x_688_ = v_reuseFailAlloc_694_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 7, v___x_688_);
v___x_690_ = v___x_678_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_env_669_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_nextMacroScope_670_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_ngen_671_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_auxDeclNGen_672_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_traceState_673_);
lean_ctor_set(v_reuseFailAlloc_693_, 5, v_cache_674_);
lean_ctor_set(v_reuseFailAlloc_693_, 6, v_messages_675_);
lean_ctor_set(v_reuseFailAlloc_693_, 7, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_693_, 8, v_snapshotTasks_676_);
v___x_690_ = v_reuseFailAlloc_693_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_st_ref_put(v___y_662_, v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_trees_666_);
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_698_);
lean_dec(v___y_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(lean_object* v___x_701_, lean_object* v_ctx_x3f_702_, size_t v_sz_703_, size_t v_i_704_, lean_object* v_bs_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_lt(v_i_704_, v_sz_703_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v_ctx_x3f_702_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_bs_705_);
return v___x_716_;
}
else
{
lean_object* v_assignment_717_; lean_object* v___x_718_; 
v_assignment_717_ = lean_ctor_get(v___x_701_, 0);
lean_inc_ref(v_ctx_x3f_702_);
lean_inc(v___y_713_);
lean_inc_ref(v___y_712_);
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
v___x_718_ = lean_apply_9(v_ctx_x3f_702_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, lean_box(0));
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v_v_720_; lean_object* v___x_721_; lean_object* v_bs_x27_722_; lean_object* v_a_724_; lean_object* v_tree_729_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v_v_720_ = lean_array_uget(v_bs_705_, v_i_704_);
v___x_721_ = lean_unsigned_to_nat(0u);
v_bs_x27_722_ = lean_array_uset(v_bs_705_, v_i_704_, v___x_721_);
v_tree_729_ = l_Lean_Elab_InfoTree_substitute(v_v_720_, v_assignment_717_);
if (lean_obj_tag(v_a_719_) == 0)
{
v_a_724_ = v_tree_729_;
goto v___jp_723_;
}
else
{
lean_object* v_val_730_; lean_object* v___x_731_; 
v_val_730_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v_a_719_, 1);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v_val_730_);
lean_ctor_set(v___x_731_, 1, v_tree_729_);
v_a_724_ = v___x_731_;
goto v___jp_723_;
}
v___jp_723_:
{
size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_704_, v___x_725_);
v___x_727_ = lean_array_uset(v_bs_x27_722_, v_i_704_, v_a_724_);
v_i_704_ = v___x_726_;
v_bs_705_ = v___x_727_;
goto _start;
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_bs_705_);
lean_dec_ref(v_ctx_x3f_702_);
v_a_732_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_718_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_718_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v___x_740_, lean_object* v_ctx_x3f_741_, lean_object* v_sz_742_, lean_object* v_i_743_, lean_object* v_bs_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
size_t v_sz_boxed_754_; size_t v_i_boxed_755_; lean_object* v_res_756_; 
v_sz_boxed_754_ = lean_unbox_usize(v_sz_742_);
lean_dec(v_sz_742_);
v_i_boxed_755_ = lean_unbox_usize(v_i_743_);
lean_dec(v_i_743_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_740_, v_ctx_x3f_741_, v_sz_boxed_754_, v_i_boxed_755_, v_bs_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v___x_740_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(lean_object* v___x_757_, lean_object* v_ctx_x3f_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
if (lean_obj_tag(v_x_759_) == 0)
{
lean_object* v_cs_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_795_; 
v_cs_769_ = lean_ctor_get(v_x_759_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_795_ == 0)
{
v___x_771_ = v_x_759_;
v_isShared_772_ = v_isSharedCheck_795_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_cs_769_);
lean_dec(v_x_759_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_795_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
size_t v_sz_773_; size_t v___x_774_; lean_object* v___x_775_; 
v_sz_773_ = lean_array_size(v_cs_769_);
v___x_774_ = ((size_t)0ULL);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_757_, v_ctx_x3f_758_, v_sz_773_, v___x_774_, v_cs_769_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_786_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_786_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_786_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_786_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v_a_776_);
v___x_781_ = v___x_771_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_781_);
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_del_object(v___x_771_);
v_a_787_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_775_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_775_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
else
{
lean_object* v_vs_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_822_; 
v_vs_796_ = lean_ctor_get(v_x_759_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_822_ == 0)
{
v___x_798_ = v_x_759_;
v_isShared_799_ = v_isSharedCheck_822_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_vs_796_);
lean_dec(v_x_759_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_822_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
size_t v_sz_800_; size_t v___x_801_; lean_object* v___x_802_; 
v_sz_800_ = lean_array_size(v_vs_796_);
v___x_801_ = ((size_t)0ULL);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_757_, v_ctx_x3f_758_, v_sz_800_, v___x_801_, v_vs_796_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_813_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_813_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_a_803_);
v___x_808_ = v___x_798_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_del_object(v___x_798_);
v_a_814_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_802_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_802_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(lean_object* v___x_823_, lean_object* v_ctx_x3f_824_, size_t v_sz_825_, size_t v_i_826_, lean_object* v_bs_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = lean_usize_dec_lt(v_i_826_, v_sz_825_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v_ctx_x3f_824_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v_bs_827_);
return v___x_838_;
}
else
{
lean_object* v_v_839_; lean_object* v___x_840_; 
v_v_839_ = lean_array_uget_borrowed(v_bs_827_, v_i_826_);
lean_inc(v_v_839_);
lean_inc_ref(v_ctx_x3f_824_);
v___x_840_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_823_, v_ctx_x3f_824_, v_v_839_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_842_; lean_object* v_bs_x27_843_; size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = lean_unsigned_to_nat(0u);
v_bs_x27_843_ = lean_array_uset(v_bs_827_, v_i_826_, v___x_842_);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_add(v_i_826_, v___x_844_);
v___x_846_ = lean_array_uset(v_bs_x27_843_, v_i_826_, v_a_841_);
v_i_826_ = v___x_845_;
v_bs_827_ = v___x_846_;
goto _start;
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_bs_827_);
lean_dec_ref(v_ctx_x3f_824_);
v_a_848_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_840_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_840_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(lean_object* v___x_856_, lean_object* v_ctx_x3f_857_, lean_object* v_sz_858_, lean_object* v_i_859_, lean_object* v_bs_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
size_t v_sz_boxed_870_; size_t v_i_boxed_871_; lean_object* v_res_872_; 
v_sz_boxed_870_ = lean_unbox_usize(v_sz_858_);
lean_dec(v_sz_858_);
v_i_boxed_871_ = lean_unbox_usize(v_i_859_);
lean_dec(v_i_859_);
v_res_872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_856_, v_ctx_x3f_857_, v_sz_boxed_870_, v_i_boxed_871_, v_bs_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec_ref(v___x_856_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9___boxed(lean_object* v___x_873_, lean_object* v_ctx_x3f_874_, lean_object* v_x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_873_, v_ctx_x3f_874_, v_x_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v___x_873_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(lean_object* v___x_886_, lean_object* v_ctx_x3f_887_, lean_object* v_t_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_root_898_; lean_object* v_tail_899_; lean_object* v_size_900_; size_t v_shift_901_; lean_object* v_tailOff_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_938_; 
v_root_898_ = lean_ctor_get(v_t_888_, 0);
v_tail_899_ = lean_ctor_get(v_t_888_, 1);
v_size_900_ = lean_ctor_get(v_t_888_, 2);
v_shift_901_ = lean_ctor_get_usize(v_t_888_, 4);
v_tailOff_902_ = lean_ctor_get(v_t_888_, 3);
v_isSharedCheck_938_ = !lean_is_exclusive(v_t_888_);
if (v_isSharedCheck_938_ == 0)
{
v___x_904_ = v_t_888_;
v_isShared_905_ = v_isSharedCheck_938_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_tailOff_902_);
lean_inc(v_size_900_);
lean_inc(v_tail_899_);
lean_inc(v_root_898_);
lean_dec(v_t_888_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_938_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; 
lean_inc_ref(v_ctx_x3f_887_);
v___x_906_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_886_, v_ctx_x3f_887_, v_root_898_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; size_t v_sz_908_; size_t v___x_909_; lean_object* v___x_910_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
v_sz_908_ = lean_array_size(v_tail_899_);
v___x_909_ = ((size_t)0ULL);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_886_, v_ctx_x3f_887_, v_sz_908_, v___x_909_, v_tail_899_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_921_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_921_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_921_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_a_911_);
lean_ctor_set(v___x_904_, 0, v_a_907_);
v___x_916_ = v___x_904_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_907_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_a_911_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v_size_900_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_tailOff_902_);
lean_ctor_set_usize(v_reuseFailAlloc_920_, 4, v_shift_901_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_a_907_);
lean_del_object(v___x_904_);
lean_dec(v_tailOff_902_);
lean_dec(v_size_900_);
v_a_922_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_910_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_910_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_del_object(v___x_904_);
lean_dec(v_tailOff_902_);
lean_dec(v_size_900_);
lean_dec_ref(v_tail_899_);
lean_dec_ref(v_ctx_x3f_887_);
v_a_930_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_906_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_906_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8___boxed(lean_object* v___x_939_, lean_object* v_ctx_x3f_940_, lean_object* v_t_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v___x_939_, v_ctx_x3f_940_, v_t_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec_ref(v___x_939_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(lean_object* v___y_952_, lean_object* v_ctx_x3f_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v_a_961_, lean_object* v_a_x3f_962_){
_start:
{
lean_object* v___x_964_; lean_object* v_infoState_965_; lean_object* v_trees_966_; lean_object* v___x_967_; 
v___x_964_ = lean_st_ref_get(v___y_952_);
v_infoState_965_ = lean_ctor_get(v___x_964_, 7);
lean_inc_ref(v_infoState_965_);
lean_dec(v___x_964_);
v_trees_966_ = lean_ctor_get(v_infoState_965_, 2);
lean_inc_ref(v_trees_966_);
v___x_967_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v_infoState_965_, v_ctx_x3f_953_, v_trees_966_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_952_);
lean_dec_ref(v_infoState_965_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1006_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_1006_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1006_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v_infoState_973_; lean_object* v_env_974_; lean_object* v_nextMacroScope_975_; lean_object* v_ngen_976_; lean_object* v_auxDeclNGen_977_; lean_object* v_traceState_978_; lean_object* v_cache_979_; lean_object* v_messages_980_; lean_object* v_snapshotTasks_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1005_; 
v___x_972_ = lean_st_ref_take(v___y_952_);
v_infoState_973_ = lean_ctor_get(v___x_972_, 7);
v_env_974_ = lean_ctor_get(v___x_972_, 0);
v_nextMacroScope_975_ = lean_ctor_get(v___x_972_, 1);
v_ngen_976_ = lean_ctor_get(v___x_972_, 2);
v_auxDeclNGen_977_ = lean_ctor_get(v___x_972_, 3);
v_traceState_978_ = lean_ctor_get(v___x_972_, 4);
v_cache_979_ = lean_ctor_get(v___x_972_, 5);
v_messages_980_ = lean_ctor_get(v___x_972_, 6);
v_snapshotTasks_981_ = lean_ctor_get(v___x_972_, 8);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_983_ = v___x_972_;
v_isShared_984_ = v_isSharedCheck_1005_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snapshotTasks_981_);
lean_inc(v_infoState_973_);
lean_inc(v_messages_980_);
lean_inc(v_cache_979_);
lean_inc(v_traceState_978_);
lean_inc(v_auxDeclNGen_977_);
lean_inc(v_ngen_976_);
lean_inc(v_nextMacroScope_975_);
lean_inc(v_env_974_);
lean_dec(v___x_972_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1005_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
uint8_t v_enabled_985_; lean_object* v_assignment_986_; lean_object* v_lazyAssignment_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1003_; 
v_enabled_985_ = lean_ctor_get_uint8(v_infoState_973_, sizeof(void*)*3);
v_assignment_986_ = lean_ctor_get(v_infoState_973_, 0);
v_lazyAssignment_987_ = lean_ctor_get(v_infoState_973_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_infoState_973_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_infoState_973_, 2);
lean_dec(v_unused_1004_);
v___x_989_ = v_infoState_973_;
v_isShared_990_ = v_isSharedCheck_1003_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_lazyAssignment_987_);
lean_inc(v_assignment_986_);
lean_dec(v_infoState_973_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1003_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_PersistentArray_append___redArg(v_a_961_, v_a_968_);
lean_dec(v_a_968_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 2, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_assignment_986_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_lazyAssignment_987_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v___x_991_);
lean_ctor_set_uint8(v_reuseFailAlloc_1002_, sizeof(void*)*3, v_enabled_985_);
v___x_993_ = v_reuseFailAlloc_1002_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 7, v___x_993_);
v___x_995_ = v___x_983_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_env_974_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_nextMacroScope_975_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_ngen_976_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_auxDeclNGen_977_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_traceState_978_);
lean_ctor_set(v_reuseFailAlloc_1001_, 5, v_cache_979_);
lean_ctor_set(v_reuseFailAlloc_1001_, 6, v_messages_980_);
lean_ctor_set(v_reuseFailAlloc_1001_, 7, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_1001_, 8, v_snapshotTasks_981_);
v___x_995_ = v_reuseFailAlloc_1001_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_996_ = lean_st_ref_put(v___y_952_, v___x_995_);
v___x_997_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_997_);
v___x_999_ = v___x_970_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_a_961_);
v_a_1007_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_967_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_967_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___y_1015_, lean_object* v_ctx_x3f_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v_a_1024_, lean_object* v_a_x3f_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1015_, v_ctx_x3f_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v_a_1024_, v_a_x3f_1025_);
lean_dec(v_a_x3f_1025_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1015_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(lean_object* v_x_1028_, lean_object* v_ctx_x3f_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v_infoState_1040_; uint8_t v_enabled_1041_; 
v___x_1039_ = lean_st_ref_get(v___y_1037_);
v_infoState_1040_ = lean_ctor_get(v___x_1039_, 7);
lean_inc_ref(v_infoState_1040_);
lean_dec(v___x_1039_);
v_enabled_1041_ = lean_ctor_get_uint8(v_infoState_1040_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1040_);
if (v_enabled_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec_ref(v_ctx_x3f_1029_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
lean_inc(v___y_1031_);
lean_inc_ref(v___y_1030_);
v___x_1042_ = lean_apply_9(v_x_1028_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, lean_box(0));
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v_a_1044_; lean_object* v_r_1045_; 
v___x_1043_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_1037_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref(v___x_1043_);
lean_inc(v___y_1037_);
lean_inc_ref(v___y_1036_);
lean_inc(v___y_1035_);
lean_inc_ref(v___y_1034_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
lean_inc(v___y_1031_);
lean_inc_ref(v___y_1030_);
v_r_1045_ = lean_apply_9(v_x_1028_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, lean_box(0));
if (lean_obj_tag(v_r_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1070_; 
v_a_1046_ = lean_ctor_get(v_r_1045_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_r_1045_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1048_ = v_r_1045_;
v_isShared_1049_ = v_isSharedCheck_1070_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v_r_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1070_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
lean_inc(v_a_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 1);
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; 
v___x_1052_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1037_, v_ctx_x3f_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v_a_1044_, v___x_1051_);
lean_dec_ref(v___x_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1052_, 0);
lean_dec(v_unused_1060_);
v___x_1054_ = v___x_1052_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_dec(v___x_1052_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v_a_1046_);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1046_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1046_);
v_a_1061_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1052_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1052_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_a_1071_ = lean_ctor_get(v_r_1045_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v_r_1045_, 1);
v___x_1072_ = lean_box(0);
v___x_1073_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1037_, v_ctx_x3f_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v_a_1044_, v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_1073_, 0);
lean_dec(v_unused_1081_);
v___x_1075_ = v___x_1073_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v___x_1073_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
lean_ctor_set(v___x_1075_, 0, v_a_1071_);
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1071_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_a_1071_);
v_a_1082_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1073_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1073_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___boxed(lean_object* v_x_1090_, lean_object* v_ctx_x3f_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1090_, v_ctx_x3f_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v___f_1113_; lean_object* v___x_1114_; 
v___f_1113_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0));
v___x_1114_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1103_, v___f_1113_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(lean_object* v_00_u03b1_1126_, lean_object* v_x_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed(lean_object* v_00_u03b1_1138_, lean_object* v_x_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(v_00_u03b1_1138_, v_x_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical(lean_object* v_stx_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = ((lean_object*)(l_Lean_Elab_Tactic_evalClassical___closed__0));
v___x_1163_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed), 13, 4);
lean_closure_set(v___x_1163_, 0, lean_box(0));
lean_closure_set(v___x_1163_, 1, v___x_1161_);
lean_closure_set(v___x_1163_, 2, v___x_1162_);
lean_closure_set(v___x_1163_, 3, v_stx_1151_);
v___x_1164_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed), 11, 2);
lean_closure_set(v___x_1164_, 0, lean_box(0));
lean_closure_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v___x_1164_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___boxed(lean_object* v_stx_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Elab_Tactic_evalClassical(v_stx_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1177_, lean_object* v_stx_1178_, lean_object* v_act_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_1178_, v_act_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_stx_1191_, lean_object* v_act_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(v_00_u03b1_1190_, v_stx_1191_, v_act_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(lean_object* v_00_u03b1_1203_, lean_object* v_split_1204_, lean_object* v_act_1205_, lean_object* v_stx_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_1204_, v_act_1205_, v_stx_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1217_, lean_object* v_split_1218_, lean_object* v_act_1219_, lean_object* v_stx_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(v_00_u03b1_1217_, v_split_1218_, v_act_1219_, v_stx_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___boxed(lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(lean_object* v_00_u03b1_1271_, lean_object* v_x_1272_, lean_object* v_ctx_x3f_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1272_, v_ctx_x3f_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_x_1285_, lean_object* v_ctx_x3f_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(v_00_u03b1_1284_, v_x_1285_, v_ctx_x3f_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1(){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1314_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4));
v___x_1316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1317_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalClassical___boxed), 10, 0);
v___x_1318_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1314_, v___x_1315_, v___x_1316_, v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___boxed(lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3(){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1323_ = l_Lean_Elab_addBuiltinIncrementalElab(v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
return v_res_1325_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Classical(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Classical(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Classical(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Classical(builtin);
}
#ifdef __cplusplus
}
#endif
