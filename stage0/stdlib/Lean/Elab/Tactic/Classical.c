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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go(lean_object*);
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
static const lean_closure_object l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_89_ = lean_st_ref_set(v___y_67_, v___x_88_);
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
v___x_100_ = lean_st_ref_set(v___y_70_, v___x_99_);
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
v___x_151_ = lean_st_ref_set(v___y_132_, v___x_150_);
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
v___x_163_ = lean_st_ref_set(v___y_130_, v___x_162_);
v___x_164_ = ((lean_object*)(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2));
v___x_165_ = 1;
v___x_166_ = lean_unsigned_to_nat(10u);
v___x_167_ = l_Lean_Meta_addInstance(v___x_164_, v___x_165_, v___x_166_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_r_168_; 
lean_dec_ref(v___x_167_);
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
lean_dec_ref(v_r_168_);
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
lean_object* v_fileName_257_; lean_object* v_fileMap_258_; lean_object* v_options_259_; lean_object* v_currRecDepth_260_; lean_object* v_maxRecDepth_261_; lean_object* v_currNamespace_262_; lean_object* v_openDecls_263_; lean_object* v_initHeartbeats_264_; lean_object* v_maxHeartbeats_265_; lean_object* v_quotContext_266_; lean_object* v_currMacroScope_267_; uint8_t v_diag_268_; lean_object* v_cancelTk_x3f_269_; uint8_t v_suppressElabErrors_270_; lean_object* v_inheritedTraceOptions_271_; uint8_t v___y_273_; 
v_fileName_257_ = lean_ctor_get(v___y_254_, 0);
v_fileMap_258_ = lean_ctor_get(v___y_254_, 1);
v_options_259_ = lean_ctor_get(v___y_254_, 2);
v_currRecDepth_260_ = lean_ctor_get(v___y_254_, 3);
v_maxRecDepth_261_ = lean_ctor_get(v___y_254_, 4);
v_currNamespace_262_ = lean_ctor_get(v___y_254_, 6);
v_openDecls_263_ = lean_ctor_get(v___y_254_, 7);
v_initHeartbeats_264_ = lean_ctor_get(v___y_254_, 8);
v_maxHeartbeats_265_ = lean_ctor_get(v___y_254_, 9);
v_quotContext_266_ = lean_ctor_get(v___y_254_, 10);
v_currMacroScope_267_ = lean_ctor_get(v___y_254_, 11);
v_diag_268_ = lean_ctor_get_uint8(v___y_254_, sizeof(void*)*14);
v_cancelTk_x3f_269_ = lean_ctor_get(v___y_254_, 12);
v_suppressElabErrors_270_ = lean_ctor_get_uint8(v___y_254_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_271_ = lean_ctor_get(v___y_254_, 13);
if (v_suppressElabErrors_270_ == 0)
{
v___y_273_ = v_suppressElabErrors_270_;
goto v___jp_272_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = l_Lean_Syntax_hasMissing(v_stx_246_);
v___y_273_ = v___x_276_;
goto v___jp_272_;
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_inc_ref(v_inheritedTraceOptions_271_);
lean_inc(v_cancelTk_x3f_269_);
lean_inc(v_currMacroScope_267_);
lean_inc(v_quotContext_266_);
lean_inc(v_maxHeartbeats_265_);
lean_inc(v_initHeartbeats_264_);
lean_inc(v_openDecls_263_);
lean_inc(v_currNamespace_262_);
lean_inc(v_maxRecDepth_261_);
lean_inc(v_currRecDepth_260_);
lean_inc_ref(v_options_259_);
lean_inc_ref(v_fileMap_258_);
lean_inc_ref(v_fileName_257_);
v___x_274_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_274_, 0, v_fileName_257_);
lean_ctor_set(v___x_274_, 1, v_fileMap_258_);
lean_ctor_set(v___x_274_, 2, v_options_259_);
lean_ctor_set(v___x_274_, 3, v_currRecDepth_260_);
lean_ctor_set(v___x_274_, 4, v_maxRecDepth_261_);
lean_ctor_set(v___x_274_, 5, v_stx_246_);
lean_ctor_set(v___x_274_, 6, v_currNamespace_262_);
lean_ctor_set(v___x_274_, 7, v_openDecls_263_);
lean_ctor_set(v___x_274_, 8, v_initHeartbeats_264_);
lean_ctor_set(v___x_274_, 9, v_maxHeartbeats_265_);
lean_ctor_set(v___x_274_, 10, v_quotContext_266_);
lean_ctor_set(v___x_274_, 11, v_currMacroScope_267_);
lean_ctor_set(v___x_274_, 12, v_cancelTk_x3f_269_);
lean_ctor_set(v___x_274_, 13, v_inheritedTraceOptions_271_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*14, v_diag_268_);
lean_ctor_set_uint8(v___x_274_, sizeof(void*)*14 + 1, v___y_273_);
lean_inc(v___y_255_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
v___x_275_ = lean_apply_9(v_act_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___x_274_, v___y_255_, lean_box(0));
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_stx_277_, lean_object* v_act_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_277_, v_act_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(lean_object* v_act_289_, lean_object* v_snd_290_, lean_object* v_____r_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_inc(v_snd_290_);
v___x_301_ = lean_apply_1(v_act_289_, v_snd_290_);
v___x_302_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_snd_290_, v___x_301_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_act_303_, lean_object* v_snd_304_, lean_object* v_____r_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_303_, v_snd_304_, v_____r_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(lean_object* v_val_317_, lean_object* v___f_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_tacSnap_x3f_333_; 
v_tacSnap_x3f_333_ = lean_ctor_get(v___y_321_, 6);
if (lean_obj_tag(v_tacSnap_x3f_333_) == 0)
{
goto v___jp_328_;
}
else
{
lean_object* v_val_334_; lean_object* v_old_x3f_335_; 
v_val_334_ = lean_ctor_get(v_tacSnap_x3f_333_, 0);
v_old_x3f_335_ = lean_ctor_get(v_val_334_, 0);
if (lean_obj_tag(v_old_x3f_335_) == 0)
{
goto v___jp_328_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref(v_val_317_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_apply_10(v___f_318_, v___x_336_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, lean_box(0));
return v___x_337_;
}
}
v___jp_328_:
{
lean_object* v_val_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_val_329_ = lean_ctor_get(v_val_317_, 1);
lean_inc(v_val_329_);
lean_dec_ref(v_val_317_);
v___x_330_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0));
v___x_331_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_330_, v_val_329_);
v___x_332_ = lean_apply_10(v___f_318_, v___x_331_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, lean_box(0));
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_val_338_, lean_object* v___f_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_338_, v___f_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(lean_object* v_split_350_, lean_object* v_act_351_, lean_object* v_stx_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___y_363_; lean_object* v___y_364_; uint8_t v___y_365_; uint8_t v___y_366_; uint8_t v___y_367_; uint8_t v___y_368_; lean_object* v___y_369_; uint8_t v___y_370_; uint8_t v___y_371_; uint8_t v___y_372_; uint8_t v___y_373_; uint8_t v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; uint8_t v___y_377_; lean_object* v___y_378_; uint8_t v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_386_; lean_object* v___y_387_; uint8_t v___y_388_; uint8_t v___y_389_; uint8_t v___y_390_; uint8_t v___y_391_; lean_object* v___y_392_; uint8_t v___y_393_; uint8_t v___y_394_; uint8_t v___y_395_; uint8_t v___y_396_; uint8_t v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; uint8_t v___y_401_; lean_object* v_new_402_; uint8_t v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___x_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v_options_412_; lean_object* v_declName_x3f_413_; lean_object* v_macroStack_414_; uint8_t v_mayPostpone_415_; uint8_t v_errToSorry_416_; lean_object* v_autoBoundImplicitContext_417_; lean_object* v_autoBoundImplicitForbidden_418_; lean_object* v_sectionVars_419_; lean_object* v_sectionFVars_420_; uint8_t v_implicitLambda_421_; uint8_t v_heedElabAsElim_422_; uint8_t v_isNoncomputableSection_423_; uint8_t v_isMetaSection_424_; uint8_t v_ignoreTCFailures_425_; uint8_t v_inPattern_426_; lean_object* v_tacSnap_x3f_427_; uint8_t v_saveRecAppSyntax_428_; uint8_t v_holesAsSyntheticOpaque_429_; uint8_t v_checkDeprecated_430_; lean_object* v_fixedTermElabs_431_; lean_object* v___y_433_; lean_object* v___f_454_; 
lean_inc_ref(v_split_350_);
v___x_409_ = lean_apply_1(v_split_350_, v_stx_352_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc_n(v_snd_411_, 2);
lean_dec_ref(v___x_409_);
v_options_412_ = lean_ctor_get(v___y_359_, 2);
v_declName_x3f_413_ = lean_ctor_get(v___y_355_, 0);
v_macroStack_414_ = lean_ctor_get(v___y_355_, 1);
v_mayPostpone_415_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8);
v_errToSorry_416_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_417_ = lean_ctor_get(v___y_355_, 2);
v_autoBoundImplicitForbidden_418_ = lean_ctor_get(v___y_355_, 3);
v_sectionVars_419_ = lean_ctor_get(v___y_355_, 4);
v_sectionFVars_420_ = lean_ctor_get(v___y_355_, 5);
v_implicitLambda_421_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 2);
v_heedElabAsElim_422_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_423_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 4);
v_isMetaSection_424_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_425_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 6);
v_inPattern_426_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_427_ = lean_ctor_get(v___y_355_, 6);
v_saveRecAppSyntax_428_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_429_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 9);
v_checkDeprecated_430_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*8 + 10);
v_fixedTermElabs_431_ = lean_ctor_get(v___y_355_, 7);
lean_inc_ref(v_act_351_);
v___f_454_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_454_, 0, v_act_351_);
lean_closure_set(v___f_454_, 1, v_snd_411_);
if (lean_obj_tag(v_tacSnap_x3f_427_) == 0)
{
lean_dec_ref(v___f_454_);
goto v___jp_455_;
}
else
{
lean_object* v_val_458_; lean_object* v_old_x3f_459_; 
v_val_458_ = lean_ctor_get(v_tacSnap_x3f_427_, 0);
v_old_x3f_459_ = lean_ctor_get(v_val_458_, 0);
if (lean_obj_tag(v_old_x3f_459_) == 1)
{
lean_object* v_val_460_; lean_object* v___f_461_; 
lean_dec(v_snd_411_);
lean_dec_ref(v_act_351_);
v_val_460_ = lean_ctor_get(v_old_x3f_459_, 0);
lean_inc(v_val_460_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed), 11, 2);
lean_closure_set(v___f_461_, 0, v_val_460_);
lean_closure_set(v___f_461_, 1, v___f_454_);
v___y_433_ = v___f_461_;
goto v___jp_432_;
}
else
{
lean_dec_ref(v___f_454_);
goto v___jp_455_;
}
}
v___jp_362_:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
lean_inc_ref(v___y_369_);
lean_inc(v___y_364_);
lean_inc(v___y_363_);
lean_inc_ref(v___y_375_);
lean_inc(v___y_376_);
lean_inc(v___y_380_);
lean_inc(v___y_378_);
v___x_383_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_383_, 0, v___y_378_);
lean_ctor_set(v___x_383_, 1, v___y_380_);
lean_ctor_set(v___x_383_, 2, v___y_376_);
lean_ctor_set(v___x_383_, 3, v___y_375_);
lean_ctor_set(v___x_383_, 4, v___y_363_);
lean_ctor_set(v___x_383_, 5, v___y_364_);
lean_ctor_set(v___x_383_, 6, v___y_382_);
lean_ctor_set(v___x_383_, 7, v___y_369_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8, v___y_371_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 1, v___y_372_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 2, v___y_366_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 3, v___y_365_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 4, v___y_368_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 5, v___y_379_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 6, v___y_374_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 7, v___y_373_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 8, v___y_370_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 9, v___y_367_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*8 + 10, v___y_377_);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
v___x_384_ = lean_apply_9(v___y_381_, v___y_353_, v___y_354_, v___x_383_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, lean_box(0));
return v___x_384_;
}
v___jp_385_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___y_406_);
lean_ctor_set(v___x_407_, 1, v_new_402_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___y_363_ = v___y_386_;
v___y_364_ = v___y_387_;
v___y_365_ = v___y_388_;
v___y_366_ = v___y_389_;
v___y_367_ = v___y_390_;
v___y_368_ = v___y_391_;
v___y_369_ = v___y_392_;
v___y_370_ = v___y_393_;
v___y_371_ = v___y_394_;
v___y_372_ = v___y_395_;
v___y_373_ = v___y_396_;
v___y_374_ = v___y_397_;
v___y_375_ = v___y_398_;
v___y_376_ = v___y_399_;
v___y_377_ = v___y_401_;
v___y_378_ = v___y_400_;
v___y_379_ = v___y_403_;
v___y_380_ = v___y_404_;
v___y_381_ = v___y_405_;
v___y_382_ = v___x_408_;
goto v___jp_362_;
}
v___jp_432_:
{
if (lean_obj_tag(v_tacSnap_x3f_427_) == 0)
{
lean_dec(v_fst_410_);
lean_dec_ref(v_split_350_);
v___y_363_ = v_sectionVars_419_;
v___y_364_ = v_sectionFVars_420_;
v___y_365_ = v_heedElabAsElim_422_;
v___y_366_ = v_implicitLambda_421_;
v___y_367_ = v_holesAsSyntheticOpaque_429_;
v___y_368_ = v_isNoncomputableSection_423_;
v___y_369_ = v_fixedTermElabs_431_;
v___y_370_ = v_saveRecAppSyntax_428_;
v___y_371_ = v_mayPostpone_415_;
v___y_372_ = v_errToSorry_416_;
v___y_373_ = v_inPattern_426_;
v___y_374_ = v_ignoreTCFailures_425_;
v___y_375_ = v_autoBoundImplicitForbidden_418_;
v___y_376_ = v_autoBoundImplicitContext_417_;
v___y_377_ = v_checkDeprecated_430_;
v___y_378_ = v_declName_x3f_413_;
v___y_379_ = v_isMetaSection_424_;
v___y_380_ = v_macroStack_414_;
v___y_381_ = v___y_433_;
v___y_382_ = v_tacSnap_x3f_427_;
goto v___jp_362_;
}
else
{
lean_object* v_val_434_; lean_object* v_old_x3f_435_; 
v_val_434_ = lean_ctor_get(v_tacSnap_x3f_427_, 0);
v_old_x3f_435_ = lean_ctor_get(v_val_434_, 0);
if (lean_obj_tag(v_old_x3f_435_) == 0)
{
lean_object* v_new_436_; 
lean_dec(v_fst_410_);
lean_dec_ref(v_split_350_);
v_new_436_ = lean_ctor_get(v_val_434_, 1);
lean_inc(v_new_436_);
v___y_386_ = v_sectionVars_419_;
v___y_387_ = v_sectionFVars_420_;
v___y_388_ = v_heedElabAsElim_422_;
v___y_389_ = v_implicitLambda_421_;
v___y_390_ = v_holesAsSyntheticOpaque_429_;
v___y_391_ = v_isNoncomputableSection_423_;
v___y_392_ = v_fixedTermElabs_431_;
v___y_393_ = v_saveRecAppSyntax_428_;
v___y_394_ = v_mayPostpone_415_;
v___y_395_ = v_errToSorry_416_;
v___y_396_ = v_inPattern_426_;
v___y_397_ = v_ignoreTCFailures_425_;
v___y_398_ = v_autoBoundImplicitForbidden_418_;
v___y_399_ = v_autoBoundImplicitContext_417_;
v___y_400_ = v_declName_x3f_413_;
v___y_401_ = v_checkDeprecated_430_;
v_new_402_ = v_new_436_;
v___y_403_ = v_isMetaSection_424_;
v___y_404_ = v_macroStack_414_;
v___y_405_ = v___y_433_;
v___y_406_ = v_old_x3f_435_;
goto v___jp_385_;
}
else
{
lean_object* v_val_437_; lean_object* v_new_438_; lean_object* v_stx_439_; lean_object* v_val_440_; lean_object* v___x_441_; lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v_val_437_ = lean_ctor_get(v_old_x3f_435_, 0);
v_new_438_ = lean_ctor_get(v_val_434_, 1);
v_stx_439_ = lean_ctor_get(v_val_437_, 0);
v_val_440_ = lean_ctor_get(v_val_437_, 1);
lean_inc(v_stx_439_);
v___x_441_ = lean_apply_1(v_split_350_, v_stx_439_);
v_fst_442_ = lean_ctor_get(v___x_441_, 0);
v_snd_443_ = lean_ctor_get(v___x_441_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_453_ == 0)
{
v___x_445_ = v___x_441_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snd_443_);
lean_inc(v_fst_442_);
lean_dec(v___x_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
uint8_t v___x_447_; 
v___x_447_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_options_412_, v_fst_410_, v_fst_442_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_del_object(v___x_445_);
lean_dec(v_snd_443_);
v___x_448_ = lean_box(0);
lean_inc(v_new_438_);
v___y_386_ = v_sectionVars_419_;
v___y_387_ = v_sectionFVars_420_;
v___y_388_ = v_heedElabAsElim_422_;
v___y_389_ = v_implicitLambda_421_;
v___y_390_ = v_holesAsSyntheticOpaque_429_;
v___y_391_ = v_isNoncomputableSection_423_;
v___y_392_ = v_fixedTermElabs_431_;
v___y_393_ = v_saveRecAppSyntax_428_;
v___y_394_ = v_mayPostpone_415_;
v___y_395_ = v_errToSorry_416_;
v___y_396_ = v_inPattern_426_;
v___y_397_ = v_ignoreTCFailures_425_;
v___y_398_ = v_autoBoundImplicitForbidden_418_;
v___y_399_ = v_autoBoundImplicitContext_417_;
v___y_400_ = v_declName_x3f_413_;
v___y_401_ = v_checkDeprecated_430_;
v_new_402_ = v_new_438_;
v___y_403_ = v_isMetaSection_424_;
v___y_404_ = v_macroStack_414_;
v___y_405_ = v___y_433_;
v___y_406_ = v___x_448_;
goto v___jp_385_;
}
else
{
lean_object* v___x_450_; 
lean_inc(v_val_440_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v_val_440_);
lean_ctor_set(v___x_445_, 0, v_snd_443_);
v___x_450_ = v___x_445_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_snd_443_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_val_440_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_inc(v_new_438_);
v___y_386_ = v_sectionVars_419_;
v___y_387_ = v_sectionFVars_420_;
v___y_388_ = v_heedElabAsElim_422_;
v___y_389_ = v_implicitLambda_421_;
v___y_390_ = v_holesAsSyntheticOpaque_429_;
v___y_391_ = v_isNoncomputableSection_423_;
v___y_392_ = v_fixedTermElabs_431_;
v___y_393_ = v_saveRecAppSyntax_428_;
v___y_394_ = v_mayPostpone_415_;
v___y_395_ = v_errToSorry_416_;
v___y_396_ = v_inPattern_426_;
v___y_397_ = v_ignoreTCFailures_425_;
v___y_398_ = v_autoBoundImplicitForbidden_418_;
v___y_399_ = v_autoBoundImplicitContext_417_;
v___y_400_ = v_declName_x3f_413_;
v___y_401_ = v_checkDeprecated_430_;
v_new_402_ = v_new_438_;
v___y_403_ = v_isMetaSection_424_;
v___y_404_ = v_macroStack_414_;
v___y_405_ = v___y_433_;
v___y_406_ = v___x_451_;
goto v___jp_385_;
}
}
}
}
}
}
v___jp_455_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_box(0);
v___x_457_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___x_457_, 0, v_act_351_);
lean_closure_set(v___x_457_, 1, v_snd_411_);
lean_closure_set(v___x_457_, 2, v___x_456_);
v___y_433_ = v___x_457_;
goto v___jp_432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(lean_object* v_split_462_, lean_object* v_act_463_, lean_object* v_stx_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_462_, v_act_463_, v_stx_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(lean_object* v_argIdx_478_, lean_object* v_stx_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_480_ = l_Lean_Syntax_getArgs(v_stx_479_);
v___x_481_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_478_);
v___x_482_ = l_Array_toSubarray___redArg(v___x_480_, v___x_481_, v_argIdx_478_);
v___x_483_ = l_Subarray_copy___redArg(v___x_482_);
v___x_484_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1));
v___x_485_ = lean_box(2);
v___x_486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
lean_ctor_set(v___x_486_, 2, v___x_483_);
v___x_487_ = l_Lean_Syntax_getArg(v_stx_479_, v_argIdx_478_);
lean_dec(v_argIdx_478_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(lean_object* v_argIdx_489_, lean_object* v_stx_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(v_argIdx_489_, v_stx_490_);
lean_dec(v_stx_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(lean_object* v_argIdx_492_, lean_object* v_act_493_, lean_object* v_stx_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___f_504_; lean_object* v___x_505_; 
v___f_504_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_504_, 0, v_argIdx_492_);
v___x_505_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v___f_504_, v_act_493_, v_stx_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(lean_object* v_argIdx_506_, lean_object* v_act_507_, lean_object* v_stx_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_506_, v_act_507_, v_stx_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(lean_object* v_00_u03b1_519_, lean_object* v_argIdx_520_, lean_object* v_act_521_, lean_object* v_stx_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_520_, v_act_521_, v_stx_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(lean_object* v_00_u03b1_533_, lean_object* v_argIdx_534_, lean_object* v_act_535_, lean_object* v_stx_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(v_00_u03b1_533_, v_argIdx_534_, v_act_535_, v_stx_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; lean_object* v_env_552_; lean_object* v___x_553_; lean_object* v_mctx_554_; lean_object* v_options_555_; lean_object* v_currNamespace_556_; lean_object* v_openDecls_557_; lean_object* v___x_558_; lean_object* v_ngen_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_551_ = lean_st_ref_get(v___y_549_);
v_env_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc_ref(v_env_552_);
lean_dec(v___x_551_);
v___x_553_ = lean_st_ref_get(v___y_547_);
v_mctx_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc_ref(v_mctx_554_);
lean_dec(v___x_553_);
v_options_555_ = lean_ctor_get(v___y_548_, 2);
v_currNamespace_556_ = lean_ctor_get(v___y_548_, 6);
v_openDecls_557_ = lean_ctor_get(v___y_548_, 7);
v___x_558_ = lean_st_ref_get(v___y_549_);
v_ngen_559_ = lean_ctor_get(v___x_558_, 2);
lean_inc_ref(v_ngen_559_);
lean_dec(v___x_558_);
v___x_560_ = lean_box(0);
v___x_561_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_557_);
lean_inc(v_currNamespace_556_);
lean_inc_ref(v_options_555_);
v___x_562_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_562_, 0, v_env_552_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
lean_ctor_set(v___x_562_, 2, v___x_561_);
lean_ctor_set(v___x_562_, 3, v_mctx_554_);
lean_ctor_set(v___x_562_, 4, v_options_555_);
lean_ctor_set(v___x_562_, 5, v_currNamespace_556_);
lean_ctor_set(v___x_562_, 6, v_openDecls_557_);
lean_ctor_set(v___x_562_, 7, v_ngen_559_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_603_; 
v___x_578_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_574_, v___y_575_, v___y_576_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_603_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_603_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_603_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v_fileMap_583_; lean_object* v_env_584_; lean_object* v_mctx_585_; lean_object* v_options_586_; lean_object* v_currNamespace_587_; lean_object* v_openDecls_588_; lean_object* v_ngen_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_600_; 
v_fileMap_583_ = lean_ctor_get(v___y_575_, 1);
v_env_584_ = lean_ctor_get(v_a_579_, 0);
v_mctx_585_ = lean_ctor_get(v_a_579_, 3);
v_options_586_ = lean_ctor_get(v_a_579_, 4);
v_currNamespace_587_ = lean_ctor_get(v_a_579_, 5);
v_openDecls_588_ = lean_ctor_get(v_a_579_, 6);
v_ngen_589_ = lean_ctor_get(v_a_579_, 7);
v_isSharedCheck_600_ = !lean_is_exclusive(v_a_579_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; lean_object* v_unused_602_; 
v_unused_601_ = lean_ctor_get(v_a_579_, 2);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_a_579_, 1);
lean_dec(v_unused_602_);
v___x_591_ = v_a_579_;
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_ngen_589_);
lean_inc(v_openDecls_588_);
lean_inc(v_currNamespace_587_);
lean_inc(v_options_586_);
lean_inc(v_mctx_585_);
lean_inc(v_env_584_);
lean_dec(v_a_579_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_600_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_box(0);
lean_inc_ref(v_fileMap_583_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 2, v_fileMap_583_);
lean_ctor_set(v___x_591_, 1, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_env_584_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_fileMap_583_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_mctx_585_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v_options_586_);
lean_ctor_set(v_reuseFailAlloc_599_, 5, v_currNamespace_587_);
lean_ctor_set(v_reuseFailAlloc_599_, 6, v_openDecls_588_);
lean_ctor_set(v_reuseFailAlloc_599_, 7, v_ngen_589_);
v___x_595_ = v_reuseFailAlloc_599_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_595_);
v___x_597_ = v___x_581_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2___boxed(lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_633_; 
v___x_623_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_633_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_633_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_633_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_a_624_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_629_);
v___x_631_ = v___x_626_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed(lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_643_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_unsigned_to_nat(32u);
v___x_645_ = lean_mk_empty_array_with_capacity(v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = ((size_t)5ULL);
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_unsigned_to_nat(32u);
v___x_650_ = lean_mk_empty_array_with_capacity(v___x_649_);
v___x_651_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0);
v___x_652_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_650_);
lean_ctor_set(v___x_652_, 2, v___x_648_);
lean_ctor_set(v___x_652_, 3, v___x_648_);
lean_ctor_set_usize(v___x_652_, 4, v___x_647_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(lean_object* v___y_653_){
_start:
{
lean_object* v___x_655_; lean_object* v_infoState_656_; lean_object* v_trees_657_; lean_object* v___x_658_; lean_object* v_infoState_659_; lean_object* v_env_660_; lean_object* v_nextMacroScope_661_; lean_object* v_ngen_662_; lean_object* v_auxDeclNGen_663_; lean_object* v_traceState_664_; lean_object* v_cache_665_; lean_object* v_messages_666_; lean_object* v_snapshotTasks_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_688_; 
v___x_655_ = lean_st_ref_get(v___y_653_);
v_infoState_656_ = lean_ctor_get(v___x_655_, 7);
lean_inc_ref(v_infoState_656_);
lean_dec(v___x_655_);
v_trees_657_ = lean_ctor_get(v_infoState_656_, 2);
lean_inc_ref(v_trees_657_);
lean_dec_ref(v_infoState_656_);
v___x_658_ = lean_st_ref_take(v___y_653_);
v_infoState_659_ = lean_ctor_get(v___x_658_, 7);
v_env_660_ = lean_ctor_get(v___x_658_, 0);
v_nextMacroScope_661_ = lean_ctor_get(v___x_658_, 1);
v_ngen_662_ = lean_ctor_get(v___x_658_, 2);
v_auxDeclNGen_663_ = lean_ctor_get(v___x_658_, 3);
v_traceState_664_ = lean_ctor_get(v___x_658_, 4);
v_cache_665_ = lean_ctor_get(v___x_658_, 5);
v_messages_666_ = lean_ctor_get(v___x_658_, 6);
v_snapshotTasks_667_ = lean_ctor_get(v___x_658_, 8);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_688_ == 0)
{
v___x_669_ = v___x_658_;
v_isShared_670_ = v_isSharedCheck_688_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_snapshotTasks_667_);
lean_inc(v_infoState_659_);
lean_inc(v_messages_666_);
lean_inc(v_cache_665_);
lean_inc(v_traceState_664_);
lean_inc(v_auxDeclNGen_663_);
lean_inc(v_ngen_662_);
lean_inc(v_nextMacroScope_661_);
lean_inc(v_env_660_);
lean_dec(v___x_658_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_688_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
uint8_t v_enabled_671_; lean_object* v_assignment_672_; lean_object* v_lazyAssignment_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_686_; 
v_enabled_671_ = lean_ctor_get_uint8(v_infoState_659_, sizeof(void*)*3);
v_assignment_672_ = lean_ctor_get(v_infoState_659_, 0);
v_lazyAssignment_673_ = lean_ctor_get(v_infoState_659_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_infoState_659_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_infoState_659_, 2);
lean_dec(v_unused_687_);
v___x_675_ = v_infoState_659_;
v_isShared_676_ = v_isSharedCheck_686_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_lazyAssignment_673_);
lean_inc(v_assignment_672_);
lean_dec(v_infoState_659_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_686_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 2, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_assignment_672_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_lazyAssignment_673_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_677_);
lean_ctor_set_uint8(v_reuseFailAlloc_685_, sizeof(void*)*3, v_enabled_671_);
v___x_679_ = v_reuseFailAlloc_685_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 7, v___x_679_);
v___x_681_ = v___x_669_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_env_660_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_nextMacroScope_661_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_ngen_662_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_auxDeclNGen_663_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_traceState_664_);
lean_ctor_set(v_reuseFailAlloc_684_, 5, v_cache_665_);
lean_ctor_set(v_reuseFailAlloc_684_, 6, v_messages_666_);
lean_ctor_set(v_reuseFailAlloc_684_, 7, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_684_, 8, v_snapshotTasks_667_);
v___x_681_ = v_reuseFailAlloc_684_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_st_ref_set(v___y_653_, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_trees_657_);
return v___x_683_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_689_);
lean_dec(v___y_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(lean_object* v___x_692_, lean_object* v_ctx_x3f_693_, size_t v_sz_694_, size_t v_i_695_, lean_object* v_bs_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v___x_706_; 
v___x_706_ = lean_usize_dec_lt(v_i_695_, v_sz_694_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec_ref(v_ctx_x3f_693_);
lean_dec_ref(v___x_692_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_bs_696_);
return v___x_707_;
}
else
{
lean_object* v_assignment_708_; lean_object* v___x_709_; 
v_assignment_708_ = lean_ctor_get(v___x_692_, 0);
lean_inc_ref(v_ctx_x3f_693_);
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
v___x_709_ = lean_apply_9(v_ctx_x3f_693_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, lean_box(0));
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v_v_711_; lean_object* v___x_712_; lean_object* v_bs_x27_713_; lean_object* v_a_715_; lean_object* v_tree_720_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_709_);
v_v_711_ = lean_array_uget(v_bs_696_, v_i_695_);
v___x_712_ = lean_unsigned_to_nat(0u);
v_bs_x27_713_ = lean_array_uset(v_bs_696_, v_i_695_, v___x_712_);
lean_inc_ref(v_assignment_708_);
v_tree_720_ = l_Lean_Elab_InfoTree_substitute(v_v_711_, v_assignment_708_);
if (lean_obj_tag(v_a_710_) == 0)
{
v_a_715_ = v_tree_720_;
goto v___jp_714_;
}
else
{
lean_object* v_val_721_; lean_object* v___x_722_; 
v_val_721_ = lean_ctor_get(v_a_710_, 0);
lean_inc(v_val_721_);
lean_dec_ref(v_a_710_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_val_721_);
lean_ctor_set(v___x_722_, 1, v_tree_720_);
v_a_715_ = v___x_722_;
goto v___jp_714_;
}
v___jp_714_:
{
size_t v___x_716_; size_t v___x_717_; lean_object* v___x_718_; 
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_add(v_i_695_, v___x_716_);
v___x_718_ = lean_array_uset(v_bs_x27_713_, v_i_695_, v_a_715_);
v_i_695_ = v___x_717_;
v_bs_696_ = v___x_718_;
goto _start;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_bs_696_);
lean_dec_ref(v_ctx_x3f_693_);
lean_dec_ref(v___x_692_);
v_a_723_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_709_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_709_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v___x_731_, lean_object* v_ctx_x3f_732_, lean_object* v_sz_733_, lean_object* v_i_734_, lean_object* v_bs_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
size_t v_sz_boxed_745_; size_t v_i_boxed_746_; lean_object* v_res_747_; 
v_sz_boxed_745_ = lean_unbox_usize(v_sz_733_);
lean_dec(v_sz_733_);
v_i_boxed_746_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_731_, v_ctx_x3f_732_, v_sz_boxed_745_, v_i_boxed_746_, v_bs_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(lean_object* v___x_748_, lean_object* v_ctx_x3f_749_, lean_object* v_x_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
lean_object* v_cs_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_786_; 
v_cs_760_ = lean_ctor_get(v_x_750_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_x_750_);
if (v_isSharedCheck_786_ == 0)
{
v___x_762_ = v_x_750_;
v_isShared_763_ = v_isSharedCheck_786_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_cs_760_);
lean_dec(v_x_750_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_786_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
size_t v_sz_764_; size_t v___x_765_; lean_object* v___x_766_; 
v_sz_764_ = lean_array_size(v_cs_760_);
v___x_765_ = ((size_t)0ULL);
v___x_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_748_, v_ctx_x3f_749_, v_sz_764_, v___x_765_, v_cs_760_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_777_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_777_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_777_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_777_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_a_767_);
v___x_772_ = v___x_762_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_762_);
v_a_778_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_766_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_766_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
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
}
else
{
lean_object* v_vs_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_813_; 
v_vs_787_ = lean_ctor_get(v_x_750_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_750_);
if (v_isSharedCheck_813_ == 0)
{
v___x_789_ = v_x_750_;
v_isShared_790_ = v_isSharedCheck_813_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_vs_787_);
lean_dec(v_x_750_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_813_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
size_t v_sz_791_; size_t v___x_792_; lean_object* v___x_793_; 
v_sz_791_ = lean_array_size(v_vs_787_);
v___x_792_ = ((size_t)0ULL);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_748_, v_ctx_x3f_749_, v_sz_791_, v___x_792_, v_vs_787_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_804_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_804_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_804_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v_a_794_);
v___x_799_ = v___x_789_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_799_);
v___x_801_ = v___x_796_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_del_object(v___x_789_);
v_a_805_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_793_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_793_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(lean_object* v___x_814_, lean_object* v_ctx_x3f_815_, size_t v_sz_816_, size_t v_i_817_, lean_object* v_bs_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v___x_828_; 
v___x_828_ = lean_usize_dec_lt(v_i_817_, v_sz_816_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec_ref(v_ctx_x3f_815_);
lean_dec_ref(v___x_814_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v_bs_818_);
return v___x_829_;
}
else
{
lean_object* v_v_830_; lean_object* v___x_831_; 
v_v_830_ = lean_array_uget_borrowed(v_bs_818_, v_i_817_);
lean_inc(v_v_830_);
lean_inc_ref(v_ctx_x3f_815_);
lean_inc_ref(v___x_814_);
v___x_831_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_814_, v_ctx_x3f_815_, v_v_830_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; lean_object* v_bs_x27_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref(v___x_831_);
v___x_833_ = lean_unsigned_to_nat(0u);
v_bs_x27_834_ = lean_array_uset(v_bs_818_, v_i_817_, v___x_833_);
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_817_, v___x_835_);
v___x_837_ = lean_array_uset(v_bs_x27_834_, v_i_817_, v_a_832_);
v_i_817_ = v___x_836_;
v_bs_818_ = v___x_837_;
goto _start;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v_bs_818_);
lean_dec_ref(v_ctx_x3f_815_);
lean_dec_ref(v___x_814_);
v_a_839_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_831_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_831_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(lean_object* v___x_847_, lean_object* v_ctx_x3f_848_, lean_object* v_sz_849_, lean_object* v_i_850_, lean_object* v_bs_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
size_t v_sz_boxed_861_; size_t v_i_boxed_862_; lean_object* v_res_863_; 
v_sz_boxed_861_ = lean_unbox_usize(v_sz_849_);
lean_dec(v_sz_849_);
v_i_boxed_862_ = lean_unbox_usize(v_i_850_);
lean_dec(v_i_850_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_847_, v_ctx_x3f_848_, v_sz_boxed_861_, v_i_boxed_862_, v_bs_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9___boxed(lean_object* v___x_864_, lean_object* v_ctx_x3f_865_, lean_object* v_x_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_864_, v_ctx_x3f_865_, v_x_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(lean_object* v___x_877_, lean_object* v_ctx_x3f_878_, lean_object* v_t_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_root_889_; lean_object* v_tail_890_; lean_object* v_size_891_; size_t v_shift_892_; lean_object* v_tailOff_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_929_; 
v_root_889_ = lean_ctor_get(v_t_879_, 0);
v_tail_890_ = lean_ctor_get(v_t_879_, 1);
v_size_891_ = lean_ctor_get(v_t_879_, 2);
v_shift_892_ = lean_ctor_get_usize(v_t_879_, 4);
v_tailOff_893_ = lean_ctor_get(v_t_879_, 3);
v_isSharedCheck_929_ = !lean_is_exclusive(v_t_879_);
if (v_isSharedCheck_929_ == 0)
{
v___x_895_ = v_t_879_;
v_isShared_896_ = v_isSharedCheck_929_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_tailOff_893_);
lean_inc(v_size_891_);
lean_inc(v_tail_890_);
lean_inc(v_root_889_);
lean_dec(v_t_879_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_929_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; 
lean_inc_ref(v_ctx_x3f_878_);
lean_inc_ref(v___x_877_);
v___x_897_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_877_, v_ctx_x3f_878_, v_root_889_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; size_t v_sz_899_; size_t v___x_900_; lean_object* v___x_901_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_897_);
v_sz_899_ = lean_array_size(v_tail_890_);
v___x_900_ = ((size_t)0ULL);
v___x_901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_877_, v_ctx_x3f_878_, v_sz_899_, v___x_900_, v_tail_890_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v_a_902_);
lean_ctor_set(v___x_895_, 0, v_a_898_);
v___x_907_ = v___x_895_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_898_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_a_902_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_size_891_);
lean_ctor_set(v_reuseFailAlloc_911_, 3, v_tailOff_893_);
lean_ctor_set_usize(v_reuseFailAlloc_911_, 4, v_shift_892_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_a_898_);
lean_del_object(v___x_895_);
lean_dec(v_tailOff_893_);
lean_dec(v_size_891_);
v_a_913_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_901_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_901_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
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
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_del_object(v___x_895_);
lean_dec(v_tailOff_893_);
lean_dec(v_size_891_);
lean_dec_ref(v_tail_890_);
lean_dec_ref(v_ctx_x3f_878_);
lean_dec_ref(v___x_877_);
v_a_921_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_897_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_897_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8___boxed(lean_object* v___x_930_, lean_object* v_ctx_x3f_931_, lean_object* v_t_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v___x_930_, v_ctx_x3f_931_, v_t_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(lean_object* v___y_943_, lean_object* v_ctx_x3f_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v_a_952_, lean_object* v_a_x3f_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_infoState_956_; lean_object* v_trees_957_; lean_object* v___x_958_; 
v___x_955_ = lean_st_ref_get(v___y_943_);
v_infoState_956_ = lean_ctor_get(v___x_955_, 7);
lean_inc_ref(v_infoState_956_);
lean_dec(v___x_955_);
v_trees_957_ = lean_ctor_get(v_infoState_956_, 2);
lean_inc_ref(v_trees_957_);
v___x_958_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v_infoState_956_, v_ctx_x3f_944_, v_trees_957_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_943_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_997_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_997_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_997_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_997_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v_infoState_964_; lean_object* v_env_965_; lean_object* v_nextMacroScope_966_; lean_object* v_ngen_967_; lean_object* v_auxDeclNGen_968_; lean_object* v_traceState_969_; lean_object* v_cache_970_; lean_object* v_messages_971_; lean_object* v_snapshotTasks_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_996_; 
v___x_963_ = lean_st_ref_take(v___y_943_);
v_infoState_964_ = lean_ctor_get(v___x_963_, 7);
v_env_965_ = lean_ctor_get(v___x_963_, 0);
v_nextMacroScope_966_ = lean_ctor_get(v___x_963_, 1);
v_ngen_967_ = lean_ctor_get(v___x_963_, 2);
v_auxDeclNGen_968_ = lean_ctor_get(v___x_963_, 3);
v_traceState_969_ = lean_ctor_get(v___x_963_, 4);
v_cache_970_ = lean_ctor_get(v___x_963_, 5);
v_messages_971_ = lean_ctor_get(v___x_963_, 6);
v_snapshotTasks_972_ = lean_ctor_get(v___x_963_, 8);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_996_ == 0)
{
v___x_974_ = v___x_963_;
v_isShared_975_ = v_isSharedCheck_996_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_snapshotTasks_972_);
lean_inc(v_infoState_964_);
lean_inc(v_messages_971_);
lean_inc(v_cache_970_);
lean_inc(v_traceState_969_);
lean_inc(v_auxDeclNGen_968_);
lean_inc(v_ngen_967_);
lean_inc(v_nextMacroScope_966_);
lean_inc(v_env_965_);
lean_dec(v___x_963_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_996_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
uint8_t v_enabled_976_; lean_object* v_assignment_977_; lean_object* v_lazyAssignment_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_994_; 
v_enabled_976_ = lean_ctor_get_uint8(v_infoState_964_, sizeof(void*)*3);
v_assignment_977_ = lean_ctor_get(v_infoState_964_, 0);
v_lazyAssignment_978_ = lean_ctor_get(v_infoState_964_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_infoState_964_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v_infoState_964_, 2);
lean_dec(v_unused_995_);
v___x_980_ = v_infoState_964_;
v_isShared_981_ = v_isSharedCheck_994_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_lazyAssignment_978_);
lean_inc(v_assignment_977_);
lean_dec(v_infoState_964_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_994_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_PersistentArray_append___redArg(v_a_952_, v_a_959_);
lean_dec(v_a_959_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 2, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_assignment_977_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_lazyAssignment_978_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v___x_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_993_, sizeof(void*)*3, v_enabled_976_);
v___x_984_ = v_reuseFailAlloc_993_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 7, v___x_984_);
v___x_986_ = v___x_974_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_env_965_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_nextMacroScope_966_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_ngen_967_);
lean_ctor_set(v_reuseFailAlloc_992_, 3, v_auxDeclNGen_968_);
lean_ctor_set(v_reuseFailAlloc_992_, 4, v_traceState_969_);
lean_ctor_set(v_reuseFailAlloc_992_, 5, v_cache_970_);
lean_ctor_set(v_reuseFailAlloc_992_, 6, v_messages_971_);
lean_ctor_set(v_reuseFailAlloc_992_, 7, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_992_, 8, v_snapshotTasks_972_);
v___x_986_ = v_reuseFailAlloc_992_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_987_ = lean_st_ref_set(v___y_943_, v___x_986_);
v___x_988_ = lean_box(0);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_988_);
v___x_990_ = v___x_961_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_a_952_);
v_a_998_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_958_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_958_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___y_1006_, lean_object* v_ctx_x3f_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v_a_1015_, lean_object* v_a_x3f_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1006_, v_ctx_x3f_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v_a_1015_, v_a_x3f_1016_);
lean_dec(v_a_x3f_1016_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1006_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(lean_object* v_x_1019_, lean_object* v_ctx_x3f_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v_infoState_1031_; uint8_t v_enabled_1032_; 
v___x_1030_ = lean_st_ref_get(v___y_1028_);
v_infoState_1031_ = lean_ctor_get(v___x_1030_, 7);
lean_inc_ref(v_infoState_1031_);
lean_dec(v___x_1030_);
v_enabled_1032_ = lean_ctor_get_uint8(v_infoState_1031_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1031_);
if (v_enabled_1032_ == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_ctx_x3f_1020_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
v___x_1033_ = lean_apply_9(v_x_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, lean_box(0));
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; lean_object* v_a_1035_; lean_object* v_r_1036_; 
v___x_1034_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_1028_);
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
v_r_1036_ = lean_apply_9(v_x_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, lean_box(0));
if (lean_obj_tag(v_r_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1061_; 
v_a_1037_ = lean_ctor_get(v_r_1036_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_r_1036_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1039_ = v_r_1036_;
v_isShared_1040_ = v_isSharedCheck_1061_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v_r_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1061_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
lean_inc(v_a_1037_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 1);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1028_, v_ctx_x3f_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v_a_1035_, v___x_1042_);
lean_dec_ref(v___x_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v___x_1043_, 0);
lean_dec(v_unused_1051_);
v___x_1045_ = v___x_1043_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_dec(v___x_1043_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v_a_1037_);
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1037_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v_a_1037_);
v_a_1052_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1043_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1043_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1062_ = lean_ctor_get(v_r_1036_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v_r_1036_);
v___x_1063_ = lean_box(0);
v___x_1064_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1028_, v_ctx_x3f_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v_a_1035_, v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v___x_1064_, 0);
lean_dec(v_unused_1072_);
v___x_1066_ = v___x_1064_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v___x_1064_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
lean_ctor_set(v___x_1066_, 0, v_a_1062_);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1062_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_a_1062_);
v_a_1073_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1064_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1064_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___boxed(lean_object* v_x_1081_, lean_object* v_ctx_x3f_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1081_, v_ctx_x3f_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(lean_object* v_x_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; 
v___f_1104_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0));
v___x_1105_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1094_, v___f_1104_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(lean_object* v_x_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(lean_object* v_00_u03b1_1117_, lean_object* v_x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_x_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(v_00_u03b1_1129_, v_x_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical(lean_object* v_stx_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = ((lean_object*)(l_Lean_Elab_Tactic_evalClassical___closed__0));
v___x_1154_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed), 13, 4);
lean_closure_set(v___x_1154_, 0, lean_box(0));
lean_closure_set(v___x_1154_, 1, v___x_1152_);
lean_closure_set(v___x_1154_, 2, v___x_1153_);
lean_closure_set(v___x_1154_, 3, v_stx_1142_);
v___x_1155_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed), 11, 2);
lean_closure_set(v___x_1155_, 0, lean_box(0));
lean_closure_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v___x_1155_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___boxed(lean_object* v_stx_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_Tactic_evalClassical(v_stx_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1168_, lean_object* v_stx_1169_, lean_object* v_act_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_1169_, v_act_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1181_, lean_object* v_stx_1182_, lean_object* v_act_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(v_00_u03b1_1181_, v_stx_1182_, v_act_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(lean_object* v_00_u03b1_1194_, lean_object* v_split_1195_, lean_object* v_act_1196_, lean_object* v_stx_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_1195_, v_act_1196_, v_stx_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_split_1209_, lean_object* v_act_1210_, lean_object* v_stx_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(v_00_u03b1_1208_, v_split_1209_, v_act_1210_, v_stx_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___boxed(lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(lean_object* v_00_u03b1_1262_, lean_object* v_x_1263_, lean_object* v_ctx_x3f_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1263_, v_ctx_x3f_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_x_1276_, lean_object* v_ctx_x3f_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(v_00_u03b1_1275_, v_x_1276_, v_ctx_x3f_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1(){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1305_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4));
v___x_1307_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1308_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalClassical___boxed), 10, 0);
v___x_1309_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1305_, v___x_1306_, v___x_1307_, v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___boxed(lean_object* v_a_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3(){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1314_ = l_Lean_Elab_addBuiltinIncrementalElab(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
return v_res_1316_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Classical(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
