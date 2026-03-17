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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addBuiltinIncrementalElab(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "classical"};
static const lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(29, 138, 254, 133, 236, 159, 90, 21)}};
static const lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalClassical"};
static const lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 86, 92, 131, 125, 72, 228, 49)}};
static const lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(lean_object*);
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
lean_inc(v_toBind_49_);
lean_dec_ref(v_inst_43_);
v_modifyEnv_50_ = lean_ctor_get(v_inst_44_, 1);
lean_inc(v_modifyEnv_50_);
lean_dec_ref(v_inst_44_);
v_toFunctor_51_ = lean_ctor_get(v_toApplicative_48_, 0);
lean_inc_ref(v_toFunctor_51_);
lean_dec_ref(v_toApplicative_48_);
v___f_52_ = ((lean_object*)(l_Lean_Elab_Tactic_classical___redArg___closed__0));
v___x_53_ = l_Lean_Meta_instanceExtension;
v___x_54_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___redArg___closed__1, &l_Lean_Elab_Tactic_classical___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_classical___redArg___closed__1);
lean_inc(v_modifyEnv_50_);
v___x_55_ = lean_apply_1(v_modifyEnv_50_, v___x_54_);
v___f_56_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_classical___redArg___lam__2), 7, 6);
lean_closure_set(v___f_56_, 0, v_toFunctor_51_);
lean_closure_set(v___f_56_, 1, v___x_53_);
lean_closure_set(v___f_56_, 2, v_modifyEnv_50_);
lean_closure_set(v___f_56_, 3, v_inst_45_);
lean_closure_set(v___f_56_, 4, v_t_47_);
lean_closure_set(v___f_56_, 5, v___f_52_);
lean_inc(v_toBind_49_);
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
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_167_ = l_Lean_Meta_addInstance(v___x_164_, v___x_165_, v___x_166_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_r_168_; 
lean_dec_ref(v___x_167_);
lean_inc(v___y_132_);
lean_inc(v___y_130_);
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
lean_dec(v___y_130_);
lean_dec(v___y_132_);
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
lean_dec(v___y_130_);
lean_dec(v___y_132_);
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
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
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
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(lean_object* v_stx_246_, lean_object* v_act_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_fileName_257_; lean_object* v_fileMap_258_; lean_object* v_options_259_; lean_object* v_currRecDepth_260_; lean_object* v_maxRecDepth_261_; lean_object* v_currNamespace_262_; lean_object* v_openDecls_263_; lean_object* v_initHeartbeats_264_; lean_object* v_maxHeartbeats_265_; lean_object* v_quotContext_266_; lean_object* v_currMacroScope_267_; uint8_t v_diag_268_; lean_object* v_cancelTk_x3f_269_; uint8_t v_suppressElabErrors_270_; lean_object* v_inheritedTraceOptions_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_282_; 
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
v_isSharedCheck_282_ = !lean_is_exclusive(v___y_254_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v___y_254_, 5);
lean_dec(v_unused_283_);
v___x_273_ = v___y_254_;
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_inheritedTraceOptions_271_);
lean_inc(v_cancelTk_x3f_269_);
lean_inc(v_currMacroScope_267_);
lean_inc(v_quotContext_266_);
lean_inc(v_maxHeartbeats_265_);
lean_inc(v_initHeartbeats_264_);
lean_inc(v_openDecls_263_);
lean_inc(v_currNamespace_262_);
lean_inc(v_maxRecDepth_261_);
lean_inc(v_currRecDepth_260_);
lean_inc(v_options_259_);
lean_inc(v_fileMap_258_);
lean_inc(v_fileName_257_);
lean_dec(v___y_254_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_282_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___y_276_; 
if (v_suppressElabErrors_270_ == 0)
{
v___y_276_ = v_suppressElabErrors_270_;
goto v___jp_275_;
}
else
{
uint8_t v___x_281_; 
lean_inc(v_stx_246_);
v___x_281_ = l_Lean_Syntax_hasMissing(v_stx_246_);
v___y_276_ = v___x_281_;
goto v___jp_275_;
}
v___jp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 5, v_stx_246_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_fileName_257_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_fileMap_258_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_options_259_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_currRecDepth_260_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v_maxRecDepth_261_);
lean_ctor_set(v_reuseFailAlloc_280_, 5, v_stx_246_);
lean_ctor_set(v_reuseFailAlloc_280_, 6, v_currNamespace_262_);
lean_ctor_set(v_reuseFailAlloc_280_, 7, v_openDecls_263_);
lean_ctor_set(v_reuseFailAlloc_280_, 8, v_initHeartbeats_264_);
lean_ctor_set(v_reuseFailAlloc_280_, 9, v_maxHeartbeats_265_);
lean_ctor_set(v_reuseFailAlloc_280_, 10, v_quotContext_266_);
lean_ctor_set(v_reuseFailAlloc_280_, 11, v_currMacroScope_267_);
lean_ctor_set(v_reuseFailAlloc_280_, 12, v_cancelTk_x3f_269_);
lean_ctor_set(v_reuseFailAlloc_280_, 13, v_inheritedTraceOptions_271_);
lean_ctor_set_uint8(v_reuseFailAlloc_280_, sizeof(void*)*14, v_diag_268_);
v___x_278_ = v_reuseFailAlloc_280_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; 
lean_ctor_set_uint8(v___x_278_, sizeof(void*)*14 + 1, v___y_276_);
v___x_279_ = lean_apply_9(v_act_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___x_278_, v___y_255_, lean_box(0));
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_stx_284_, lean_object* v_act_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_284_, v_act_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(lean_object* v_act_296_, lean_object* v_snd_297_, lean_object* v_____r_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_inc(v_snd_297_);
v___x_308_ = lean_apply_1(v_act_296_, v_snd_297_);
v___x_309_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_snd_297_, v___x_308_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_act_310_, lean_object* v_snd_311_, lean_object* v_____r_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_310_, v_snd_311_, v_____r_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(lean_object* v_val_324_, lean_object* v___f_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_tacSnap_x3f_340_; 
v_tacSnap_x3f_340_ = lean_ctor_get(v___y_328_, 6);
if (lean_obj_tag(v_tacSnap_x3f_340_) == 0)
{
goto v___jp_335_;
}
else
{
lean_object* v_val_341_; lean_object* v_old_x3f_342_; 
v_val_341_ = lean_ctor_get(v_tacSnap_x3f_340_, 0);
v_old_x3f_342_ = lean_ctor_get(v_val_341_, 0);
if (lean_obj_tag(v_old_x3f_342_) == 0)
{
goto v___jp_335_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec_ref(v_val_324_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_apply_10(v___f_325_, v___x_343_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, lean_box(0));
return v___x_344_;
}
}
v___jp_335_:
{
lean_object* v_val_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_val_336_ = lean_ctor_get(v_val_324_, 1);
lean_inc(v_val_336_);
lean_dec_ref(v_val_324_);
v___x_337_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___closed__0));
v___x_338_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_337_, v_val_336_);
v___x_339_ = lean_apply_10(v___f_325_, v___x_338_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, lean_box(0));
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_val_345_, lean_object* v___f_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_345_, v___f_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(lean_object* v_split_357_, lean_object* v_act_358_, lean_object* v_stx_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
uint8_t v___y_370_; uint8_t v___y_371_; uint8_t v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; lean_object* v___y_377_; uint8_t v___y_378_; uint8_t v___y_379_; lean_object* v___y_380_; uint8_t v___y_381_; lean_object* v___y_382_; uint8_t v___y_383_; lean_object* v___y_384_; uint8_t v___y_385_; lean_object* v___y_386_; uint8_t v___y_387_; lean_object* v___y_388_; uint8_t v___y_392_; uint8_t v___y_393_; uint8_t v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; uint8_t v___y_401_; lean_object* v___y_402_; uint8_t v___y_403_; lean_object* v___y_404_; lean_object* v_new_405_; uint8_t v___y_406_; lean_object* v___y_407_; uint8_t v___y_408_; lean_object* v___y_409_; uint8_t v___y_410_; lean_object* v___y_411_; lean_object* v___x_414_; lean_object* v_fst_415_; lean_object* v_snd_416_; lean_object* v_options_417_; lean_object* v_declName_x3f_418_; lean_object* v_macroStack_419_; uint8_t v_mayPostpone_420_; uint8_t v_errToSorry_421_; lean_object* v_autoBoundImplicitContext_422_; lean_object* v_autoBoundImplicitForbidden_423_; lean_object* v_sectionVars_424_; lean_object* v_sectionFVars_425_; uint8_t v_implicitLambda_426_; uint8_t v_heedElabAsElim_427_; uint8_t v_isNoncomputableSection_428_; uint8_t v_ignoreTCFailures_429_; uint8_t v_inPattern_430_; lean_object* v_tacSnap_x3f_431_; uint8_t v_saveRecAppSyntax_432_; uint8_t v_holesAsSyntheticOpaque_433_; uint8_t v_checkDeprecated_434_; lean_object* v_fixedTermElabs_435_; lean_object* v___y_437_; lean_object* v___f_464_; 
lean_inc_ref(v_split_357_);
v___x_414_ = lean_apply_1(v_split_357_, v_stx_359_);
v_fst_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_fst_415_);
v_snd_416_ = lean_ctor_get(v___x_414_, 1);
lean_inc(v_snd_416_);
lean_dec_ref(v___x_414_);
v_options_417_ = lean_ctor_get(v___y_366_, 2);
v_declName_x3f_418_ = lean_ctor_get(v___y_362_, 0);
lean_inc(v_declName_x3f_418_);
v_macroStack_419_ = lean_ctor_get(v___y_362_, 1);
lean_inc(v_macroStack_419_);
v_mayPostpone_420_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8);
v_errToSorry_421_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_422_ = lean_ctor_get(v___y_362_, 2);
lean_inc(v_autoBoundImplicitContext_422_);
v_autoBoundImplicitForbidden_423_ = lean_ctor_get(v___y_362_, 3);
lean_inc_ref(v_autoBoundImplicitForbidden_423_);
v_sectionVars_424_ = lean_ctor_get(v___y_362_, 4);
lean_inc(v_sectionVars_424_);
v_sectionFVars_425_ = lean_ctor_get(v___y_362_, 5);
lean_inc(v_sectionFVars_425_);
v_implicitLambda_426_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 2);
v_heedElabAsElim_427_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_428_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 4);
v_ignoreTCFailures_429_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 5);
v_inPattern_430_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 6);
v_tacSnap_x3f_431_ = lean_ctor_get(v___y_362_, 6);
lean_inc(v_tacSnap_x3f_431_);
v_saveRecAppSyntax_432_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 7);
v_holesAsSyntheticOpaque_433_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 8);
v_checkDeprecated_434_ = lean_ctor_get_uint8(v___y_362_, sizeof(void*)*8 + 9);
v_fixedTermElabs_435_ = lean_ctor_get(v___y_362_, 7);
lean_inc_ref(v_fixedTermElabs_435_);
lean_dec_ref(v___y_362_);
lean_inc(v_snd_416_);
lean_inc_ref(v_act_358_);
v___f_464_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_464_, 0, v_act_358_);
lean_closure_set(v___f_464_, 1, v_snd_416_);
if (lean_obj_tag(v_tacSnap_x3f_431_) == 0)
{
lean_dec_ref(v___f_464_);
goto v___jp_465_;
}
else
{
lean_object* v_val_468_; lean_object* v_old_x3f_469_; 
v_val_468_ = lean_ctor_get(v_tacSnap_x3f_431_, 0);
v_old_x3f_469_ = lean_ctor_get(v_val_468_, 0);
if (lean_obj_tag(v_old_x3f_469_) == 1)
{
lean_object* v_val_470_; lean_object* v___f_471_; 
lean_dec(v_snd_416_);
lean_dec_ref(v_act_358_);
v_val_470_ = lean_ctor_get(v_old_x3f_469_, 0);
lean_inc(v_val_470_);
v___f_471_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed), 11, 2);
lean_closure_set(v___f_471_, 0, v_val_470_);
lean_closure_set(v___f_471_, 1, v___f_464_);
v___y_437_ = v___f_471_;
goto v___jp_436_;
}
else
{
lean_dec_ref(v___f_464_);
goto v___jp_465_;
}
}
v___jp_369_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_389_, 0, v___y_374_);
lean_ctor_set(v___x_389_, 1, v___y_384_);
lean_ctor_set(v___x_389_, 2, v___y_380_);
lean_ctor_set(v___x_389_, 3, v___y_377_);
lean_ctor_set(v___x_389_, 4, v___y_373_);
lean_ctor_set(v___x_389_, 5, v___y_386_);
lean_ctor_set(v___x_389_, 6, v___y_388_);
lean_ctor_set(v___x_389_, 7, v___y_375_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8, v___y_385_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 1, v___y_379_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 2, v___y_371_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 3, v___y_376_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 4, v___y_387_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 5, v___y_381_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 6, v___y_378_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 7, v___y_372_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 8, v___y_383_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*8 + 9, v___y_370_);
v___x_390_ = lean_apply_9(v___y_382_, v___y_360_, v___y_361_, v___x_389_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, lean_box(0));
return v___x_390_;
}
v___jp_391_:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___y_411_);
lean_ctor_set(v___x_412_, 1, v_new_405_);
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
v___y_370_ = v___y_392_;
v___y_371_ = v___y_393_;
v___y_372_ = v___y_394_;
v___y_373_ = v___y_395_;
v___y_374_ = v___y_396_;
v___y_375_ = v___y_397_;
v___y_376_ = v___y_398_;
v___y_377_ = v___y_399_;
v___y_378_ = v___y_400_;
v___y_379_ = v___y_401_;
v___y_380_ = v___y_402_;
v___y_381_ = v___y_403_;
v___y_382_ = v___y_404_;
v___y_383_ = v___y_406_;
v___y_384_ = v___y_407_;
v___y_385_ = v___y_408_;
v___y_386_ = v___y_409_;
v___y_387_ = v___y_410_;
v___y_388_ = v___x_413_;
goto v___jp_369_;
}
v___jp_436_:
{
if (lean_obj_tag(v_tacSnap_x3f_431_) == 0)
{
lean_dec(v_fst_415_);
lean_dec_ref(v_split_357_);
v___y_370_ = v_checkDeprecated_434_;
v___y_371_ = v_implicitLambda_426_;
v___y_372_ = v_saveRecAppSyntax_432_;
v___y_373_ = v_sectionVars_424_;
v___y_374_ = v_declName_x3f_418_;
v___y_375_ = v_fixedTermElabs_435_;
v___y_376_ = v_heedElabAsElim_427_;
v___y_377_ = v_autoBoundImplicitForbidden_423_;
v___y_378_ = v_inPattern_430_;
v___y_379_ = v_errToSorry_421_;
v___y_380_ = v_autoBoundImplicitContext_422_;
v___y_381_ = v_ignoreTCFailures_429_;
v___y_382_ = v___y_437_;
v___y_383_ = v_holesAsSyntheticOpaque_433_;
v___y_384_ = v_macroStack_419_;
v___y_385_ = v_mayPostpone_420_;
v___y_386_ = v_sectionFVars_425_;
v___y_387_ = v_isNoncomputableSection_428_;
v___y_388_ = v_tacSnap_x3f_431_;
goto v___jp_369_;
}
else
{
lean_object* v_val_438_; lean_object* v_old_x3f_439_; 
v_val_438_ = lean_ctor_get(v_tacSnap_x3f_431_, 0);
lean_inc(v_val_438_);
lean_dec_ref(v_tacSnap_x3f_431_);
v_old_x3f_439_ = lean_ctor_get(v_val_438_, 0);
lean_inc(v_old_x3f_439_);
if (lean_obj_tag(v_old_x3f_439_) == 0)
{
lean_object* v_new_440_; 
lean_dec(v_fst_415_);
lean_dec_ref(v_split_357_);
v_new_440_ = lean_ctor_get(v_val_438_, 1);
lean_inc(v_new_440_);
lean_dec(v_val_438_);
v___y_392_ = v_checkDeprecated_434_;
v___y_393_ = v_implicitLambda_426_;
v___y_394_ = v_saveRecAppSyntax_432_;
v___y_395_ = v_sectionVars_424_;
v___y_396_ = v_declName_x3f_418_;
v___y_397_ = v_fixedTermElabs_435_;
v___y_398_ = v_heedElabAsElim_427_;
v___y_399_ = v_autoBoundImplicitForbidden_423_;
v___y_400_ = v_inPattern_430_;
v___y_401_ = v_errToSorry_421_;
v___y_402_ = v_autoBoundImplicitContext_422_;
v___y_403_ = v_ignoreTCFailures_429_;
v___y_404_ = v___y_437_;
v_new_405_ = v_new_440_;
v___y_406_ = v_holesAsSyntheticOpaque_433_;
v___y_407_ = v_macroStack_419_;
v___y_408_ = v_mayPostpone_420_;
v___y_409_ = v_sectionFVars_425_;
v___y_410_ = v_isNoncomputableSection_428_;
v___y_411_ = v_old_x3f_439_;
goto v___jp_391_;
}
else
{
lean_object* v_val_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_463_; 
v_val_441_ = lean_ctor_get(v_old_x3f_439_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_old_x3f_439_);
if (v_isSharedCheck_463_ == 0)
{
v___x_443_ = v_old_x3f_439_;
v_isShared_444_ = v_isSharedCheck_463_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_val_441_);
lean_dec(v_old_x3f_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_463_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v_new_445_; lean_object* v_stx_446_; lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_462_; 
v_new_445_ = lean_ctor_get(v_val_438_, 1);
lean_inc(v_new_445_);
lean_dec(v_val_438_);
v_stx_446_ = lean_ctor_get(v_val_441_, 0);
v_val_447_ = lean_ctor_get(v_val_441_, 1);
v_isSharedCheck_462_ = !lean_is_exclusive(v_val_441_);
if (v_isSharedCheck_462_ == 0)
{
v___x_449_ = v_val_441_;
v_isShared_450_ = v_isSharedCheck_462_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_inc(v_stx_446_);
lean_dec(v_val_441_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_462_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v_fst_452_; lean_object* v_snd_453_; uint8_t v___x_454_; 
v___x_451_ = lean_apply_1(v_split_357_, v_stx_446_);
v_fst_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_fst_452_);
v_snd_453_ = lean_ctor_get(v___x_451_, 1);
lean_inc(v_snd_453_);
lean_dec_ref(v___x_451_);
v___x_454_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_options_417_, v_fst_415_, v_fst_452_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v_snd_453_);
lean_del_object(v___x_449_);
lean_dec(v_val_447_);
lean_del_object(v___x_443_);
v___x_455_ = lean_box(0);
v___y_392_ = v_checkDeprecated_434_;
v___y_393_ = v_implicitLambda_426_;
v___y_394_ = v_saveRecAppSyntax_432_;
v___y_395_ = v_sectionVars_424_;
v___y_396_ = v_declName_x3f_418_;
v___y_397_ = v_fixedTermElabs_435_;
v___y_398_ = v_heedElabAsElim_427_;
v___y_399_ = v_autoBoundImplicitForbidden_423_;
v___y_400_ = v_inPattern_430_;
v___y_401_ = v_errToSorry_421_;
v___y_402_ = v_autoBoundImplicitContext_422_;
v___y_403_ = v_ignoreTCFailures_429_;
v___y_404_ = v___y_437_;
v_new_405_ = v_new_445_;
v___y_406_ = v_holesAsSyntheticOpaque_433_;
v___y_407_ = v_macroStack_419_;
v___y_408_ = v_mayPostpone_420_;
v___y_409_ = v_sectionFVars_425_;
v___y_410_ = v_isNoncomputableSection_428_;
v___y_411_ = v___x_455_;
goto v___jp_391_;
}
else
{
lean_object* v___x_457_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v_snd_453_);
v___x_457_ = v___x_449_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_snd_453_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_val_447_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v___x_457_);
v___x_459_ = v___x_443_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v___y_392_ = v_checkDeprecated_434_;
v___y_393_ = v_implicitLambda_426_;
v___y_394_ = v_saveRecAppSyntax_432_;
v___y_395_ = v_sectionVars_424_;
v___y_396_ = v_declName_x3f_418_;
v___y_397_ = v_fixedTermElabs_435_;
v___y_398_ = v_heedElabAsElim_427_;
v___y_399_ = v_autoBoundImplicitForbidden_423_;
v___y_400_ = v_inPattern_430_;
v___y_401_ = v_errToSorry_421_;
v___y_402_ = v_autoBoundImplicitContext_422_;
v___y_403_ = v_ignoreTCFailures_429_;
v___y_404_ = v___y_437_;
v_new_405_ = v_new_445_;
v___y_406_ = v_holesAsSyntheticOpaque_433_;
v___y_407_ = v_macroStack_419_;
v___y_408_ = v_mayPostpone_420_;
v___y_409_ = v_sectionFVars_425_;
v___y_410_ = v_isNoncomputableSection_428_;
v___y_411_ = v___x_459_;
goto v___jp_391_;
}
}
}
}
}
}
}
}
v___jp_465_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_box(0);
v___x_467_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___x_467_, 0, v_act_358_);
lean_closure_set(v___x_467_, 1, v_snd_416_);
lean_closure_set(v___x_467_, 2, v___x_466_);
v___y_437_ = v___x_467_;
goto v___jp_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(lean_object* v_split_472_, lean_object* v_act_473_, lean_object* v_stx_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_472_, v_act_473_, v_stx_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(lean_object* v_argIdx_488_, lean_object* v_stx_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_490_ = l_Lean_Syntax_getArgs(v_stx_489_);
v___x_491_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_488_);
v___x_492_ = l_Array_toSubarray___redArg(v___x_490_, v___x_491_, v_argIdx_488_);
v___x_493_ = l_Subarray_copy___redArg(v___x_492_);
v___x_494_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1));
v___x_495_ = lean_box(2);
v___x_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_493_);
v___x_497_ = l_Lean_Syntax_getArg(v_stx_489_, v_argIdx_488_);
lean_dec(v_argIdx_488_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(lean_object* v_argIdx_499_, lean_object* v_stx_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(v_argIdx_499_, v_stx_500_);
lean_dec(v_stx_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(lean_object* v_argIdx_502_, lean_object* v_act_503_, lean_object* v_stx_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___f_514_; lean_object* v___x_515_; 
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_514_, 0, v_argIdx_502_);
v___x_515_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v___f_514_, v_act_503_, v_stx_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(lean_object* v_argIdx_516_, lean_object* v_act_517_, lean_object* v_stx_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_516_, v_act_517_, v_stx_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(lean_object* v_00_u03b1_529_, lean_object* v_argIdx_530_, lean_object* v_act_531_, lean_object* v_stx_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_530_, v_act_531_, v_stx_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(lean_object* v_00_u03b1_543_, lean_object* v_argIdx_544_, lean_object* v_act_545_, lean_object* v_stx_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(v_00_u03b1_543_, v_argIdx_544_, v_act_545_, v_stx_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v_env_562_; lean_object* v___x_563_; lean_object* v_mctx_564_; lean_object* v_options_565_; lean_object* v_currNamespace_566_; lean_object* v_openDecls_567_; lean_object* v___x_568_; lean_object* v_ngen_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_561_ = lean_st_ref_get(v___y_559_);
v_env_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_561_);
v___x_563_ = lean_st_ref_get(v___y_557_);
v_mctx_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_mctx_564_);
lean_dec(v___x_563_);
v_options_565_ = lean_ctor_get(v___y_558_, 2);
v_currNamespace_566_ = lean_ctor_get(v___y_558_, 6);
v_openDecls_567_ = lean_ctor_get(v___y_558_, 7);
v___x_568_ = lean_st_ref_get(v___y_559_);
v_ngen_569_ = lean_ctor_get(v___x_568_, 2);
lean_inc_ref(v_ngen_569_);
lean_dec(v___x_568_);
v___x_570_ = lean_box(0);
v___x_571_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_567_);
lean_inc(v_currNamespace_566_);
lean_inc_ref(v_options_565_);
v___x_572_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_572_, 0, v_env_562_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
lean_ctor_set(v___x_572_, 2, v___x_571_);
lean_ctor_set(v___x_572_, 3, v_mctx_564_);
lean_ctor_set(v___x_572_, 4, v_options_565_);
lean_ctor_set(v___x_572_, 5, v_currNamespace_566_);
lean_ctor_set(v___x_572_, 6, v_openDecls_567_);
lean_ctor_set(v___x_572_, 7, v_ngen_569_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_613_; 
v___x_588_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_584_, v___y_585_, v___y_586_);
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_613_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_613_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_613_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_fileMap_593_; lean_object* v_env_594_; lean_object* v_mctx_595_; lean_object* v_options_596_; lean_object* v_currNamespace_597_; lean_object* v_openDecls_598_; lean_object* v_ngen_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_610_; 
v_fileMap_593_ = lean_ctor_get(v___y_585_, 1);
v_env_594_ = lean_ctor_get(v_a_589_, 0);
v_mctx_595_ = lean_ctor_get(v_a_589_, 3);
v_options_596_ = lean_ctor_get(v_a_589_, 4);
v_currNamespace_597_ = lean_ctor_get(v_a_589_, 5);
v_openDecls_598_ = lean_ctor_get(v_a_589_, 6);
v_ngen_599_ = lean_ctor_get(v_a_589_, 7);
v_isSharedCheck_610_ = !lean_is_exclusive(v_a_589_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; lean_object* v_unused_612_; 
v_unused_611_ = lean_ctor_get(v_a_589_, 2);
lean_dec(v_unused_611_);
v_unused_612_ = lean_ctor_get(v_a_589_, 1);
lean_dec(v_unused_612_);
v___x_601_ = v_a_589_;
v_isShared_602_ = v_isSharedCheck_610_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_ngen_599_);
lean_inc(v_openDecls_598_);
lean_inc(v_currNamespace_597_);
lean_inc(v_options_596_);
lean_inc(v_mctx_595_);
lean_inc(v_env_594_);
lean_dec(v_a_589_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_610_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_box(0);
lean_inc_ref(v_fileMap_593_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 2, v_fileMap_593_);
lean_ctor_set(v___x_601_, 1, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_env_594_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_609_, 2, v_fileMap_593_);
lean_ctor_set(v_reuseFailAlloc_609_, 3, v_mctx_595_);
lean_ctor_set(v_reuseFailAlloc_609_, 4, v_options_596_);
lean_ctor_set(v_reuseFailAlloc_609_, 5, v_currNamespace_597_);
lean_ctor_set(v_reuseFailAlloc_609_, 6, v_openDecls_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 7, v_ngen_599_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_605_);
v___x_607_ = v___x_591_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2___boxed(lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_643_; 
v___x_633_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_643_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v_a_634_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_639_);
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed(lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_653_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = lean_unsigned_to_nat(32u);
v___x_655_ = lean_mk_empty_array_with_capacity(v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_657_ = ((size_t)5ULL);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_unsigned_to_nat(32u);
v___x_660_ = lean_mk_empty_array_with_capacity(v___x_659_);
v___x_661_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0);
v___x_662_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
lean_ctor_set(v___x_662_, 2, v___x_658_);
lean_ctor_set(v___x_662_, 3, v___x_658_);
lean_ctor_set_usize(v___x_662_, 4, v___x_657_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; lean_object* v_infoState_666_; lean_object* v_trees_667_; lean_object* v___x_668_; lean_object* v_infoState_669_; lean_object* v_env_670_; lean_object* v_nextMacroScope_671_; lean_object* v_ngen_672_; lean_object* v_auxDeclNGen_673_; lean_object* v_traceState_674_; lean_object* v_cache_675_; lean_object* v_messages_676_; lean_object* v_snapshotTasks_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_698_; 
v___x_665_ = lean_st_ref_get(v___y_663_);
v_infoState_666_ = lean_ctor_get(v___x_665_, 7);
lean_inc_ref(v_infoState_666_);
lean_dec(v___x_665_);
v_trees_667_ = lean_ctor_get(v_infoState_666_, 2);
lean_inc_ref(v_trees_667_);
lean_dec_ref(v_infoState_666_);
v___x_668_ = lean_st_ref_take(v___y_663_);
v_infoState_669_ = lean_ctor_get(v___x_668_, 7);
v_env_670_ = lean_ctor_get(v___x_668_, 0);
v_nextMacroScope_671_ = lean_ctor_get(v___x_668_, 1);
v_ngen_672_ = lean_ctor_get(v___x_668_, 2);
v_auxDeclNGen_673_ = lean_ctor_get(v___x_668_, 3);
v_traceState_674_ = lean_ctor_get(v___x_668_, 4);
v_cache_675_ = lean_ctor_get(v___x_668_, 5);
v_messages_676_ = lean_ctor_get(v___x_668_, 6);
v_snapshotTasks_677_ = lean_ctor_get(v___x_668_, 8);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_698_ == 0)
{
v___x_679_ = v___x_668_;
v_isShared_680_ = v_isSharedCheck_698_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_snapshotTasks_677_);
lean_inc(v_infoState_669_);
lean_inc(v_messages_676_);
lean_inc(v_cache_675_);
lean_inc(v_traceState_674_);
lean_inc(v_auxDeclNGen_673_);
lean_inc(v_ngen_672_);
lean_inc(v_nextMacroScope_671_);
lean_inc(v_env_670_);
lean_dec(v___x_668_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_698_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
uint8_t v_enabled_681_; lean_object* v_assignment_682_; lean_object* v_lazyAssignment_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_696_; 
v_enabled_681_ = lean_ctor_get_uint8(v_infoState_669_, sizeof(void*)*3);
v_assignment_682_ = lean_ctor_get(v_infoState_669_, 0);
v_lazyAssignment_683_ = lean_ctor_get(v_infoState_669_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_infoState_669_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v_infoState_669_, 2);
lean_dec(v_unused_697_);
v___x_685_ = v_infoState_669_;
v_isShared_686_ = v_isSharedCheck_696_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_lazyAssignment_683_);
lean_inc(v_assignment_682_);
lean_dec(v_infoState_669_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_696_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 2, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_assignment_682_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_lazyAssignment_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v___x_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3, v_enabled_681_);
v___x_689_ = v_reuseFailAlloc_695_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 7, v___x_689_);
v___x_691_ = v___x_679_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_env_670_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_nextMacroScope_671_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_ngen_672_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_auxDeclNGen_673_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_traceState_674_);
lean_ctor_set(v_reuseFailAlloc_694_, 5, v_cache_675_);
lean_ctor_set(v_reuseFailAlloc_694_, 6, v_messages_676_);
lean_ctor_set(v_reuseFailAlloc_694_, 7, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_694_, 8, v_snapshotTasks_677_);
v___x_691_ = v_reuseFailAlloc_694_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_st_ref_set(v___y_663_, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_trees_667_);
return v___x_693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_699_);
lean_dec(v___y_699_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(lean_object* v___x_702_, lean_object* v_ctx_x3f_703_, size_t v_sz_704_, size_t v_i_705_, lean_object* v_bs_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_lt(v_i_705_, v_sz_704_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v_ctx_x3f_703_);
lean_dec_ref(v___x_702_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_bs_706_);
return v___x_717_;
}
else
{
lean_object* v_assignment_718_; lean_object* v___x_719_; 
v_assignment_718_ = lean_ctor_get(v___x_702_, 0);
lean_inc_ref(v_ctx_x3f_703_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
v___x_719_ = lean_apply_9(v_ctx_x3f_703_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, lean_box(0));
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v_v_721_; lean_object* v___x_722_; lean_object* v_bs_x27_723_; lean_object* v_a_725_; lean_object* v_tree_730_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_719_);
v_v_721_ = lean_array_uget(v_bs_706_, v_i_705_);
v___x_722_ = lean_unsigned_to_nat(0u);
v_bs_x27_723_ = lean_array_uset(v_bs_706_, v_i_705_, v___x_722_);
lean_inc_ref(v_assignment_718_);
v_tree_730_ = l_Lean_Elab_InfoTree_substitute(v_v_721_, v_assignment_718_);
if (lean_obj_tag(v_a_720_) == 0)
{
v_a_725_ = v_tree_730_;
goto v___jp_724_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_732_; 
v_val_731_ = lean_ctor_get(v_a_720_, 0);
lean_inc(v_val_731_);
lean_dec_ref(v_a_720_);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_val_731_);
lean_ctor_set(v___x_732_, 1, v_tree_730_);
v_a_725_ = v___x_732_;
goto v___jp_724_;
}
v___jp_724_:
{
size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_i_705_, v___x_726_);
v___x_728_ = lean_array_uset(v_bs_x27_723_, v_i_705_, v_a_725_);
v_i_705_ = v___x_727_;
v_bs_706_ = v___x_728_;
goto _start;
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec_ref(v_bs_706_);
lean_dec_ref(v_ctx_x3f_703_);
lean_dec_ref(v___x_702_);
v_a_733_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_719_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_719_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v___x_741_, lean_object* v_ctx_x3f_742_, lean_object* v_sz_743_, lean_object* v_i_744_, lean_object* v_bs_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
size_t v_sz_boxed_755_; size_t v_i_boxed_756_; lean_object* v_res_757_; 
v_sz_boxed_755_ = lean_unbox_usize(v_sz_743_);
lean_dec(v_sz_743_);
v_i_boxed_756_ = lean_unbox_usize(v_i_744_);
lean_dec(v_i_744_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_741_, v_ctx_x3f_742_, v_sz_boxed_755_, v_i_boxed_756_, v_bs_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(lean_object* v___x_758_, lean_object* v_ctx_x3f_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v_cs_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_796_; 
v_cs_770_ = lean_ctor_get(v_x_760_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_796_ == 0)
{
v___x_772_ = v_x_760_;
v_isShared_773_ = v_isSharedCheck_796_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_cs_770_);
lean_dec(v_x_760_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_796_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
size_t v_sz_774_; size_t v___x_775_; lean_object* v___x_776_; 
v_sz_774_ = lean_array_size(v_cs_770_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_758_, v_ctx_x3f_759_, v_sz_774_, v___x_775_, v_cs_770_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_787_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_787_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v_a_777_);
v___x_782_ = v___x_772_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_786_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_del_object(v___x_772_);
v_a_788_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_776_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_776_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
else
{
lean_object* v_vs_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_823_; 
v_vs_797_ = lean_ctor_get(v_x_760_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_823_ == 0)
{
v___x_799_ = v_x_760_;
v_isShared_800_ = v_isSharedCheck_823_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_vs_797_);
lean_dec(v_x_760_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_823_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
size_t v_sz_801_; size_t v___x_802_; lean_object* v___x_803_; 
v_sz_801_ = lean_array_size(v_vs_797_);
v___x_802_ = ((size_t)0ULL);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_758_, v_ctx_x3f_759_, v_sz_801_, v___x_802_, v_vs_797_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_814_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_814_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v_a_804_);
v___x_809_ = v___x_799_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_del_object(v___x_799_);
v_a_815_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_803_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_803_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(lean_object* v___x_824_, lean_object* v_ctx_x3f_825_, size_t v_sz_826_, size_t v_i_827_, lean_object* v_bs_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v___x_838_; 
v___x_838_ = lean_usize_dec_lt(v_i_827_, v_sz_826_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec_ref(v_ctx_x3f_825_);
lean_dec_ref(v___x_824_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v_bs_828_);
return v___x_839_;
}
else
{
lean_object* v_v_840_; lean_object* v___x_841_; 
v_v_840_ = lean_array_uget_borrowed(v_bs_828_, v_i_827_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v_v_840_);
lean_inc_ref(v_ctx_x3f_825_);
lean_inc_ref(v___x_824_);
v___x_841_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_824_, v_ctx_x3f_825_, v_v_840_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; lean_object* v_bs_x27_844_; size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___x_841_);
v___x_843_ = lean_unsigned_to_nat(0u);
v_bs_x27_844_ = lean_array_uset(v_bs_828_, v_i_827_, v___x_843_);
v___x_845_ = ((size_t)1ULL);
v___x_846_ = lean_usize_add(v_i_827_, v___x_845_);
v___x_847_ = lean_array_uset(v_bs_x27_844_, v_i_827_, v_a_842_);
v_i_827_ = v___x_846_;
v_bs_828_ = v___x_847_;
goto _start;
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec_ref(v_bs_828_);
lean_dec_ref(v_ctx_x3f_825_);
lean_dec_ref(v___x_824_);
v_a_849_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_841_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_841_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(lean_object* v___x_857_, lean_object* v_ctx_x3f_858_, lean_object* v_sz_859_, lean_object* v_i_860_, lean_object* v_bs_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
size_t v_sz_boxed_871_; size_t v_i_boxed_872_; lean_object* v_res_873_; 
v_sz_boxed_871_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_872_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_857_, v_ctx_x3f_858_, v_sz_boxed_871_, v_i_boxed_872_, v_bs_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9___boxed(lean_object* v___x_874_, lean_object* v_ctx_x3f_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_874_, v_ctx_x3f_875_, v_x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(lean_object* v___x_887_, lean_object* v_ctx_x3f_888_, lean_object* v_t_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_root_899_; lean_object* v_tail_900_; lean_object* v_size_901_; size_t v_shift_902_; lean_object* v_tailOff_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_939_; 
v_root_899_ = lean_ctor_get(v_t_889_, 0);
v_tail_900_ = lean_ctor_get(v_t_889_, 1);
v_size_901_ = lean_ctor_get(v_t_889_, 2);
v_shift_902_ = lean_ctor_get_usize(v_t_889_, 4);
v_tailOff_903_ = lean_ctor_get(v_t_889_, 3);
v_isSharedCheck_939_ = !lean_is_exclusive(v_t_889_);
if (v_isSharedCheck_939_ == 0)
{
v___x_905_ = v_t_889_;
v_isShared_906_ = v_isSharedCheck_939_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_tailOff_903_);
lean_inc(v_size_901_);
lean_inc(v_tail_900_);
lean_inc(v_root_899_);
lean_dec(v_t_889_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_939_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; 
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc_ref(v_ctx_x3f_888_);
lean_inc_ref(v___x_887_);
v___x_907_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_887_, v_ctx_x3f_888_, v_root_899_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; size_t v_sz_909_; size_t v___x_910_; lean_object* v___x_911_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v_sz_909_ = lean_array_size(v_tail_900_);
v___x_910_ = ((size_t)0ULL);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_887_, v_ctx_x3f_888_, v_sz_909_, v___x_910_, v_tail_900_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_922_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_922_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_922_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_922_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v_a_912_);
lean_ctor_set(v___x_905_, 0, v_a_908_);
v___x_917_ = v___x_905_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_908_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_a_912_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_size_901_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_tailOff_903_);
lean_ctor_set_usize(v_reuseFailAlloc_921_, 4, v_shift_902_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec(v_a_908_);
lean_del_object(v___x_905_);
lean_dec(v_tailOff_903_);
lean_dec(v_size_901_);
v_a_923_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_911_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_911_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_del_object(v___x_905_);
lean_dec(v_tailOff_903_);
lean_dec(v_size_901_);
lean_dec_ref(v_tail_900_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v_ctx_x3f_888_);
lean_dec_ref(v___x_887_);
v_a_931_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_907_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_907_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8___boxed(lean_object* v___x_940_, lean_object* v_ctx_x3f_941_, lean_object* v_t_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v___x_940_, v_ctx_x3f_941_, v_t_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(lean_object* v___y_953_, lean_object* v_ctx_x3f_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v_a_962_, lean_object* v_a_x3f_963_){
_start:
{
lean_object* v___x_965_; lean_object* v_infoState_966_; lean_object* v_trees_967_; lean_object* v___x_968_; 
v___x_965_ = lean_st_ref_get(v___y_953_);
v_infoState_966_ = lean_ctor_get(v___x_965_, 7);
lean_inc_ref(v_infoState_966_);
lean_dec(v___x_965_);
v_trees_967_ = lean_ctor_get(v_infoState_966_, 2);
lean_inc_ref(v_trees_967_);
lean_inc(v___y_953_);
v___x_968_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v_infoState_966_, v_ctx_x3f_954_, v_trees_967_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_953_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_1007_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_1007_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_1007_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; lean_object* v_infoState_974_; lean_object* v_env_975_; lean_object* v_nextMacroScope_976_; lean_object* v_ngen_977_; lean_object* v_auxDeclNGen_978_; lean_object* v_traceState_979_; lean_object* v_cache_980_; lean_object* v_messages_981_; lean_object* v_snapshotTasks_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1006_; 
v___x_973_ = lean_st_ref_take(v___y_953_);
v_infoState_974_ = lean_ctor_get(v___x_973_, 7);
v_env_975_ = lean_ctor_get(v___x_973_, 0);
v_nextMacroScope_976_ = lean_ctor_get(v___x_973_, 1);
v_ngen_977_ = lean_ctor_get(v___x_973_, 2);
v_auxDeclNGen_978_ = lean_ctor_get(v___x_973_, 3);
v_traceState_979_ = lean_ctor_get(v___x_973_, 4);
v_cache_980_ = lean_ctor_get(v___x_973_, 5);
v_messages_981_ = lean_ctor_get(v___x_973_, 6);
v_snapshotTasks_982_ = lean_ctor_get(v___x_973_, 8);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_984_ = v___x_973_;
v_isShared_985_ = v_isSharedCheck_1006_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snapshotTasks_982_);
lean_inc(v_infoState_974_);
lean_inc(v_messages_981_);
lean_inc(v_cache_980_);
lean_inc(v_traceState_979_);
lean_inc(v_auxDeclNGen_978_);
lean_inc(v_ngen_977_);
lean_inc(v_nextMacroScope_976_);
lean_inc(v_env_975_);
lean_dec(v___x_973_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1006_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
uint8_t v_enabled_986_; lean_object* v_assignment_987_; lean_object* v_lazyAssignment_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1004_; 
v_enabled_986_ = lean_ctor_get_uint8(v_infoState_974_, sizeof(void*)*3);
v_assignment_987_ = lean_ctor_get(v_infoState_974_, 0);
v_lazyAssignment_988_ = lean_ctor_get(v_infoState_974_, 1);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_infoState_974_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v_infoState_974_, 2);
lean_dec(v_unused_1005_);
v___x_990_ = v_infoState_974_;
v_isShared_991_ = v_isSharedCheck_1004_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_lazyAssignment_988_);
lean_inc(v_assignment_987_);
lean_dec(v_infoState_974_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1004_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = l_Lean_PersistentArray_append___redArg(v_a_962_, v_a_969_);
lean_dec(v_a_969_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 2, v___x_992_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_assignment_987_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_lazyAssignment_988_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v___x_992_);
lean_ctor_set_uint8(v_reuseFailAlloc_1003_, sizeof(void*)*3, v_enabled_986_);
v___x_994_ = v_reuseFailAlloc_1003_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 7, v___x_994_);
v___x_996_ = v___x_984_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_env_975_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_nextMacroScope_976_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_ngen_977_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_auxDeclNGen_978_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_traceState_979_);
lean_ctor_set(v_reuseFailAlloc_1002_, 5, v_cache_980_);
lean_ctor_set(v_reuseFailAlloc_1002_, 6, v_messages_981_);
lean_ctor_set(v_reuseFailAlloc_1002_, 7, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 8, v_snapshotTasks_982_);
v___x_996_ = v_reuseFailAlloc_1002_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = lean_st_ref_set(v___y_953_, v___x_996_);
lean_dec(v___y_953_);
v___x_998_ = lean_box(0);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_998_);
v___x_1000_ = v___x_971_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_a_962_);
lean_dec(v___y_953_);
v_a_1008_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_968_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_968_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___y_1016_, lean_object* v_ctx_x3f_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v_a_1025_, lean_object* v_a_x3f_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1016_, v_ctx_x3f_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v_a_1025_, v_a_x3f_1026_);
lean_dec(v_a_x3f_1026_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(lean_object* v_x_1029_, lean_object* v_ctx_x3f_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; lean_object* v_infoState_1041_; uint8_t v_enabled_1042_; 
v___x_1040_ = lean_st_ref_get(v___y_1038_);
v_infoState_1041_ = lean_ctor_get(v___x_1040_, 7);
lean_inc_ref(v_infoState_1041_);
lean_dec(v___x_1040_);
v_enabled_1042_ = lean_ctor_get_uint8(v_infoState_1041_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1041_);
if (v_enabled_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_dec_ref(v_ctx_x3f_1030_);
v___x_1043_ = lean_apply_9(v_x_1029_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, lean_box(0));
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; lean_object* v_a_1045_; lean_object* v_r_1046_; 
v___x_1044_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_1038_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v___x_1044_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
lean_inc(v___y_1036_);
lean_inc_ref(v___y_1035_);
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
v_r_1046_ = lean_apply_9(v_x_1029_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, lean_box(0));
if (lean_obj_tag(v_r_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1071_; 
v_a_1047_ = lean_ctor_get(v_r_1046_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_r_1046_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1049_ = v_r_1046_;
v_isShared_1050_ = v_isSharedCheck_1071_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v_r_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1071_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
lean_inc(v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; 
v___x_1053_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1038_, v_ctx_x3f_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v_a_1045_, v___x_1052_);
lean_dec_ref(v___x_1052_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v___x_1053_, 0);
lean_dec(v_unused_1061_);
v___x_1055_ = v___x_1053_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_dec(v___x_1053_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v_a_1047_);
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1047_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_a_1047_);
v_a_1062_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1053_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1053_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1072_ = lean_ctor_get(v_r_1046_, 0);
lean_inc(v_a_1072_);
lean_dec_ref(v_r_1046_);
v___x_1073_ = lean_box(0);
v___x_1074_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1038_, v_ctx_x3f_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v_a_1045_, v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___x_1074_, 0);
lean_dec(v_unused_1082_);
v___x_1076_ = v___x_1074_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_dec(v___x_1074_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 1);
lean_ctor_set(v___x_1076_, 0, v_a_1072_);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1072_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_a_1072_);
v_a_1083_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1074_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1074_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___boxed(lean_object* v_x_1091_, lean_object* v_ctx_x3f_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1091_, v_ctx_x3f_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___f_1114_; lean_object* v___x_1115_; 
v___f_1114_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0));
v___x_1115_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1104_, v___f_1114_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(lean_object* v_x_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(lean_object* v_00_u03b1_1127_, lean_object* v_x_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(v_00_u03b1_1139_, v_x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical(lean_object* v_stx_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Tactic_evalClassical___closed__0));
v___x_1164_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed), 13, 4);
lean_closure_set(v___x_1164_, 0, lean_box(0));
lean_closure_set(v___x_1164_, 1, v___x_1162_);
lean_closure_set(v___x_1164_, 2, v___x_1163_);
lean_closure_set(v___x_1164_, 3, v_stx_1152_);
v___x_1165_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed), 11, 2);
lean_closure_set(v___x_1165_, 0, lean_box(0));
lean_closure_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v___x_1165_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___boxed(lean_object* v_stx_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Elab_Tactic_evalClassical(v_stx_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1178_, lean_object* v_stx_1179_, lean_object* v_act_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_1179_, v_act_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_stx_1192_, lean_object* v_act_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(v_00_u03b1_1191_, v_stx_1192_, v_act_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(lean_object* v_00_u03b1_1204_, lean_object* v_split_1205_, lean_object* v_act_1206_, lean_object* v_stx_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_1205_, v_act_1206_, v_stx_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1218_, lean_object* v_split_1219_, lean_object* v_act_1220_, lean_object* v_stx_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(v_00_u03b1_1218_, v_split_1219_, v_act_1220_, v_stx_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1237_, v___y_1238_, v___y_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___boxed(lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(lean_object* v_00_u03b1_1272_, lean_object* v_x_1273_, lean_object* v_ctx_x3f_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1273_, v_ctx_x3f_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1285_, lean_object* v_x_1286_, lean_object* v_ctx_x3f_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(v_00_u03b1_1285_, v_x_1286_, v_ctx_x3f_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1(){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1315_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4));
v___x_1317_ = ((lean_object*)(l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1318_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalClassical___boxed), 10, 0);
v___x_1319_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1315_, v___x_1316_, v___x_1317_, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___boxed(lean_object* v_a_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3(){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1324_ = l_Lean_Elab_addBuiltinIncrementalElab(v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
return v_res_1326_;
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
res = l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
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
