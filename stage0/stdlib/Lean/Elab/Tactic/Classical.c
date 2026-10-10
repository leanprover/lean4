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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
extern lean_object* l_Lean_Meta_instanceExtension;
lean_object* l_Lean_ScopedEnvExtension_pushScope___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(lean_object* v___y_67_, lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v___y_70_, lean_object* v___x_71_, lean_object* v_a_x3f_72_){
_start:
{
lean_object* v___x_74_; lean_object* v_env_75_; lean_object* v_nextMacroScope_76_; lean_object* v_ngen_77_; lean_object* v_auxDeclNGen_78_; lean_object* v_traceState_79_; lean_object* v_recordedDeps_80_; lean_object* v_messages_81_; lean_object* v_infoState_82_; lean_object* v_snapshotTasks_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_108_; 
v___x_74_ = lean_st_ref_take(v___y_67_);
v_env_75_ = lean_ctor_get(v___x_74_, 0);
v_nextMacroScope_76_ = lean_ctor_get(v___x_74_, 1);
v_ngen_77_ = lean_ctor_get(v___x_74_, 2);
v_auxDeclNGen_78_ = lean_ctor_get(v___x_74_, 3);
v_traceState_79_ = lean_ctor_get(v___x_74_, 4);
v_recordedDeps_80_ = lean_ctor_get(v___x_74_, 6);
v_messages_81_ = lean_ctor_get(v___x_74_, 7);
v_infoState_82_ = lean_ctor_get(v___x_74_, 8);
v_snapshotTasks_83_ = lean_ctor_get(v___x_74_, 9);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v___x_74_, 5);
lean_dec(v_unused_109_);
v___x_85_ = v___x_74_;
v_isShared_86_ = v_isSharedCheck_108_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_snapshotTasks_83_);
lean_inc(v_infoState_82_);
lean_inc(v_messages_81_);
lean_inc(v_recordedDeps_80_);
lean_inc(v_traceState_79_);
lean_inc(v_auxDeclNGen_78_);
lean_inc(v_ngen_77_);
lean_inc(v_nextMacroScope_76_);
lean_inc(v_env_75_);
lean_dec(v___x_74_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_108_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = l_Lean_ScopedEnvExtension_popScope___redArg(v___x_68_, v_env_75_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 5, v___x_69_);
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_nextMacroScope_76_);
lean_ctor_set(v_reuseFailAlloc_107_, 2, v_ngen_77_);
lean_ctor_set(v_reuseFailAlloc_107_, 3, v_auxDeclNGen_78_);
lean_ctor_set(v_reuseFailAlloc_107_, 4, v_traceState_79_);
lean_ctor_set(v_reuseFailAlloc_107_, 5, v___x_69_);
lean_ctor_set(v_reuseFailAlloc_107_, 6, v_recordedDeps_80_);
lean_ctor_set(v_reuseFailAlloc_107_, 7, v_messages_81_);
lean_ctor_set(v_reuseFailAlloc_107_, 8, v_infoState_82_);
lean_ctor_set(v_reuseFailAlloc_107_, 9, v_snapshotTasks_83_);
v___x_89_ = v_reuseFailAlloc_107_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v_mctx_92_; lean_object* v_zetaDeltaFVarIds_93_; lean_object* v_postponed_94_; lean_object* v_diag_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_105_; 
v___x_90_ = lean_st_ref_put(v___y_67_, v___x_89_);
v___x_91_ = lean_st_ref_take(v___y_70_);
v_mctx_92_ = lean_ctor_get(v___x_91_, 0);
v_zetaDeltaFVarIds_93_ = lean_ctor_get(v___x_91_, 2);
v_postponed_94_ = lean_ctor_get(v___x_91_, 3);
v_diag_95_ = lean_ctor_get(v___x_91_, 4);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_105_ == 0)
{
lean_object* v_unused_106_; 
v_unused_106_ = lean_ctor_get(v___x_91_, 1);
lean_dec(v_unused_106_);
v___x_97_ = v___x_91_;
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_diag_95_);
lean_inc(v_postponed_94_);
lean_inc(v_zetaDeltaFVarIds_93_);
lean_inc(v_mctx_92_);
lean_dec(v___x_91_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_105_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_box(0);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___x_71_);
v___x_101_ = v___x_97_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_mctx_92_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___x_71_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v_zetaDeltaFVarIds_93_);
lean_ctor_set(v_reuseFailAlloc_104_, 3, v_postponed_94_);
lean_ctor_set(v_reuseFailAlloc_104_, 4, v_diag_95_);
v___x_101_ = v_reuseFailAlloc_104_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_st_ref_put(v___y_70_, v___x_101_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_99_);
return v___x_103_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_67_ = stack[0].m_obj;
lean_object* v___x_68_ = stack[1].m_obj;
lean_object* v___x_69_ = stack[2].m_obj;
lean_object* v___y_70_ = stack[3].m_obj;
lean_object* v___x_71_ = stack[4].m_obj;
lean_object* v_a_x3f_72_ = stack[5].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_67_, v___x_68_, v___x_69_, v___y_70_, v___x_71_, v_a_x3f_72_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0___boxed(lean_object* v___y_111_, lean_object* v___x_112_, lean_object* v___x_113_, lean_object* v___y_114_, lean_object* v___x_115_, lean_object* v_a_x3f_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_111_, v___x_112_, v___x_113_, v___y_114_, v___x_115_, v_a_x3f_116_);
lean_dec(v_a_x3f_116_);
lean_dec(v___y_114_);
lean_dec(v___y_111_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
v___x_125_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
lean_ctor_set(v___x_125_, 2, v___x_124_);
lean_ctor_set(v___x_125_, 3, v___x_124_);
lean_ctor_set(v___x_125_, 4, v___x_124_);
lean_ctor_set(v___x_125_, 5, v___x_124_);
return v___x_125_;
}
}
lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(lean_object* v_t_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_env_138_; lean_object* v_nextMacroScope_139_; lean_object* v_ngen_140_; lean_object* v_auxDeclNGen_141_; lean_object* v_traceState_142_; lean_object* v_recordedDeps_143_; lean_object* v_messages_144_; lean_object* v_infoState_145_; lean_object* v_snapshotTasks_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_212_; 
v___x_136_ = l_Lean_Meta_instanceExtension;
v___x_137_ = lean_st_ref_take(v___y_134_);
v_env_138_ = lean_ctor_get(v___x_137_, 0);
v_nextMacroScope_139_ = lean_ctor_get(v___x_137_, 1);
v_ngen_140_ = lean_ctor_get(v___x_137_, 2);
v_auxDeclNGen_141_ = lean_ctor_get(v___x_137_, 3);
v_traceState_142_ = lean_ctor_get(v___x_137_, 4);
v_recordedDeps_143_ = lean_ctor_get(v___x_137_, 6);
v_messages_144_ = lean_ctor_get(v___x_137_, 7);
v_infoState_145_ = lean_ctor_get(v___x_137_, 8);
v_snapshotTasks_146_ = lean_ctor_get(v___x_137_, 9);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v___x_137_, 5);
lean_dec(v_unused_213_);
v___x_148_ = v___x_137_;
v_isShared_149_ = v_isSharedCheck_212_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_snapshotTasks_146_);
lean_inc(v_infoState_145_);
lean_inc(v_messages_144_);
lean_inc(v_recordedDeps_143_);
lean_inc(v_traceState_142_);
lean_inc(v_auxDeclNGen_141_);
lean_inc(v_ngen_140_);
lean_inc(v_nextMacroScope_139_);
lean_inc(v_env_138_);
lean_dec(v___x_137_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_212_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_150_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v___x_136_, v_env_138_);
v___x_151_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 5, v___x_151_);
lean_ctor_set(v___x_148_, 0, v___x_150_);
v___x_153_ = v___x_148_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_nextMacroScope_139_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_ngen_140_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_auxDeclNGen_141_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v_traceState_142_);
lean_ctor_set(v_reuseFailAlloc_211_, 5, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_211_, 6, v_recordedDeps_143_);
lean_ctor_set(v_reuseFailAlloc_211_, 7, v_messages_144_);
lean_ctor_set(v_reuseFailAlloc_211_, 8, v_infoState_145_);
lean_ctor_set(v_reuseFailAlloc_211_, 9, v_snapshotTasks_146_);
v___x_153_ = v_reuseFailAlloc_211_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_mctx_156_; lean_object* v_zetaDeltaFVarIds_157_; lean_object* v_postponed_158_; lean_object* v_diag_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_209_; 
v___x_154_ = lean_st_ref_put(v___y_134_, v___x_153_);
v___x_155_ = lean_st_ref_take(v___y_132_);
v_mctx_156_ = lean_ctor_get(v___x_155_, 0);
v_zetaDeltaFVarIds_157_ = lean_ctor_get(v___x_155_, 2);
v_postponed_158_ = lean_ctor_get(v___x_155_, 3);
v_diag_159_ = lean_ctor_get(v___x_155_, 4);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v___x_155_, 1);
lean_dec(v_unused_210_);
v___x_161_ = v___x_155_;
v_isShared_162_ = v_isSharedCheck_209_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_diag_159_);
lean_inc(v_postponed_158_);
lean_inc(v_zetaDeltaFVarIds_157_);
lean_inc(v_mctx_156_);
lean_dec(v___x_155_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_209_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_mctx_156_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v_zetaDeltaFVarIds_157_);
lean_ctor_set(v_reuseFailAlloc_208_, 3, v_postponed_158_);
lean_ctor_set(v_reuseFailAlloc_208_, 4, v_diag_159_);
v___x_165_ = v_reuseFailAlloc_208_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_166_ = lean_st_ref_put(v___y_132_, v___x_165_);
v___x_167_ = ((lean_object*)(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2));
v___x_168_ = 1;
v___x_169_ = lean_unsigned_to_nat(10u);
v___x_170_ = l_Lean_Meta_addInstance(v___x_167_, v___x_168_, v___x_169_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_r_171_; 
lean_dec_ref_known(v___x_170_, 1);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
v_r_171_ = lean_apply_9(v_t_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, lean_box(0));
if (lean_obj_tag(v_r_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_188_; 
v_a_172_ = lean_ctor_get(v_r_171_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v_r_171_);
if (v_isSharedCheck_188_ == 0)
{
v___x_174_ = v_r_171_;
v_isShared_175_ = v_isSharedCheck_188_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v_r_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_188_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
lean_inc(v_a_172_);
if (v_isShared_175_ == 0)
{
lean_ctor_set_tag(v___x_174_, 1);
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_187_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v___x_178_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_134_, v___x_136_, v___x_151_, v___y_132_, v___x_163_, v___x_177_);
lean_dec_ref(v___x_177_);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v___x_178_, 0);
lean_dec(v_unused_186_);
v___x_180_ = v___x_178_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_dec(v___x_178_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v_a_172_);
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_172_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
v_a_189_ = lean_ctor_get(v_r_171_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v_r_171_, 1);
v___x_190_ = lean_box(0);
v___x_191_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_134_, v___x_136_, v___x_151_, v___y_132_, v___x_163_, v___x_190_);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v___x_191_, 0);
lean_dec(v_unused_199_);
v___x_193_ = v___x_191_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_dec(v___x_191_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 1);
lean_ctor_set(v___x_193_, 0, v_a_189_);
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_189_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_t_126_);
v_a_200_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_170_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_170_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_126_ = stack[0].m_obj;
lean_object* v___y_127_ = stack[1].m_obj;
lean_object* v___y_128_ = stack[2].m_obj;
lean_object* v___y_129_ = stack[3].m_obj;
lean_object* v___y_130_ = stack[4].m_obj;
lean_object* v___y_131_ = stack[5].m_obj;
lean_object* v___y_132_ = stack[6].m_obj;
lean_object* v___y_133_ = stack[7].m_obj;
lean_object* v___y_134_ = stack[8].m_obj;
lean_object* v_res_214_;
v_res_214_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v_t_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___boxed(lean_object* v_t_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v_t_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_225_;
}
}
lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(lean_object* v_00_u03b1_226_, lean_object* v_t_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v_t_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_227_ = stack[1].m_obj;
lean_object* v___y_228_ = stack[2].m_obj;
lean_object* v___y_229_ = stack[3].m_obj;
lean_object* v___y_230_ = stack[4].m_obj;
lean_object* v___y_231_ = stack[5].m_obj;
lean_object* v___y_232_ = stack[6].m_obj;
lean_object* v___y_233_ = stack[7].m_obj;
lean_object* v___y_234_ = stack[8].m_obj;
lean_object* v___y_235_ = stack[9].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(lean_box(0), v_t_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___boxed(lean_object* v_00_u03b1_239_, lean_object* v_t_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(v_00_u03b1_239_, v_t_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_250_;
}
}
lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(lean_object* v_stx_251_, lean_object* v_act_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_toCold_262_; lean_object* v_currRecDepth_263_; uint16_t v_optionFlags_264_; uint8_t v_suppressElabErrors_265_; uint8_t v_isRecordingDeps_266_; uint8_t v___y_268_; 
v_toCold_262_ = lean_ctor_get(v___y_259_, 0);
v_currRecDepth_263_ = lean_ctor_get(v___y_259_, 1);
v_optionFlags_264_ = lean_ctor_get_uint16(v___y_259_, sizeof(void*)*3);
v_suppressElabErrors_265_ = lean_ctor_get_uint8(v___y_259_, sizeof(void*)*3 + 2);
v_isRecordingDeps_266_ = lean_ctor_get_uint8(v___y_259_, sizeof(void*)*3 + 3);
if (v_suppressElabErrors_265_ == 0)
{
v___y_268_ = v_suppressElabErrors_265_;
goto v___jp_267_;
}
else
{
uint8_t v___x_271_; 
v___x_271_ = l_Lean_Syntax_hasMissing(v_stx_251_);
v___y_268_ = v___x_271_;
goto v___jp_267_;
}
v___jp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_inc(v_currRecDepth_263_);
lean_inc_ref(v_toCold_262_);
v___x_269_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_269_, 0, v_toCold_262_);
lean_ctor_set(v___x_269_, 1, v_currRecDepth_263_);
lean_ctor_set(v___x_269_, 2, v_stx_251_);
lean_ctor_set_uint16(v___x_269_, sizeof(void*)*3, v_optionFlags_264_);
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*3 + 2, v___y_268_);
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*3 + 3, v_isRecordingDeps_266_);
lean_inc(v___y_260_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
v___x_270_ = lean_apply_9(v_act_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___x_269_, v___y_260_, lean_box(0));
return v___x_270_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_251_ = stack[0].m_obj;
lean_object* v_act_252_ = stack[1].m_obj;
lean_object* v___y_253_ = stack[2].m_obj;
lean_object* v___y_254_ = stack[3].m_obj;
lean_object* v___y_255_ = stack[4].m_obj;
lean_object* v___y_256_ = stack[5].m_obj;
lean_object* v___y_257_ = stack[6].m_obj;
lean_object* v___y_258_ = stack[7].m_obj;
lean_object* v___y_259_ = stack[8].m_obj;
lean_object* v___y_260_ = stack[9].m_obj;
lean_object* v_res_272_;
v_res_272_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_251_, v_act_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_stx_273_, lean_object* v_act_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_273_, v_act_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_284_;
}
}
lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(lean_object* v_act_285_, lean_object* v_snd_286_, lean_object* v_____r_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_inc(v_snd_286_);
v___x_297_ = lean_apply_1(v_act_285_, v_snd_286_);
v___x_298_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_snd_286_, v___x_297_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
return v___x_298_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_285_ = stack[0].m_obj;
lean_object* v_snd_286_ = stack[1].m_obj;
lean_object* v_____r_287_ = stack[2].m_obj;
lean_object* v___y_288_ = stack[3].m_obj;
lean_object* v___y_289_ = stack[4].m_obj;
lean_object* v___y_290_ = stack[5].m_obj;
lean_object* v___y_291_ = stack[6].m_obj;
lean_object* v___y_292_ = stack[7].m_obj;
lean_object* v___y_293_ = stack[8].m_obj;
lean_object* v___y_294_ = stack[9].m_obj;
lean_object* v___y_295_ = stack[10].m_obj;
lean_object* v_res_299_;
v_res_299_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_285_, v_snd_286_, v_____r_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_act_300_, lean_object* v_snd_301_, lean_object* v_____r_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_300_, v_snd_301_, v_____r_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_312_;
}
}
lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(lean_object* v_val_313_, lean_object* v___x_314_, lean_object* v___f_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_tacSnap_x3f_329_; 
v_tacSnap_x3f_329_ = lean_ctor_get(v___y_318_, 6);
if (lean_obj_tag(v_tacSnap_x3f_329_) == 0)
{
goto v___jp_325_;
}
else
{
lean_object* v_val_330_; lean_object* v_old_x3f_331_; 
v_val_330_ = lean_ctor_get(v_tacSnap_x3f_329_, 0);
v_old_x3f_331_ = lean_ctor_get(v_val_330_, 0);
if (lean_obj_tag(v_old_x3f_331_) == 0)
{
goto v___jp_325_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec_ref(v___x_314_);
lean_dec_ref(v_val_313_);
v___x_332_ = lean_box(0);
v___x_333_ = lean_apply_10(v___f_315_, v___x_332_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, lean_box(0));
return v___x_333_;
}
}
v___jp_325_:
{
lean_object* v_val_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_val_326_ = lean_ctor_get(v_val_313_, 1);
lean_inc(v_val_326_);
lean_dec_ref(v_val_313_);
v___x_327_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_314_, v_val_326_);
v___x_328_ = lean_apply_10(v___f_315_, v___x_327_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, lean_box(0));
return v___x_328_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_313_ = stack[0].m_obj;
lean_object* v___x_314_ = stack[1].m_obj;
lean_object* v___f_315_ = stack[2].m_obj;
lean_object* v___y_316_ = stack[3].m_obj;
lean_object* v___y_317_ = stack[4].m_obj;
lean_object* v___y_318_ = stack[5].m_obj;
lean_object* v___y_319_ = stack[6].m_obj;
lean_object* v___y_320_ = stack[7].m_obj;
lean_object* v___y_321_ = stack[8].m_obj;
lean_object* v___y_322_ = stack[9].m_obj;
lean_object* v___y_323_ = stack[10].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_313_, v___x_314_, v___f_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_val_335_, lean_object* v___x_336_, lean_object* v___f_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_335_, v___x_336_, v___f_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v_res_347_;
}
}
lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(lean_object* v_split_349_, lean_object* v_act_350_, lean_object* v_stx_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___y_362_; lean_object* v___y_363_; uint8_t v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; uint8_t v___y_367_; uint8_t v___y_368_; uint8_t v___y_369_; uint8_t v___y_370_; uint8_t v___y_371_; lean_object* v___y_372_; uint8_t v___y_373_; lean_object* v___y_374_; uint8_t v___y_375_; uint8_t v___y_376_; uint8_t v___y_377_; uint8_t v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_385_; lean_object* v___y_386_; uint8_t v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; uint8_t v___y_390_; uint8_t v___y_391_; uint8_t v___y_392_; uint8_t v___y_393_; uint8_t v___y_394_; lean_object* v___y_395_; lean_object* v_new_396_; uint8_t v___y_397_; uint8_t v___y_398_; lean_object* v___y_399_; uint8_t v___y_400_; uint8_t v___y_401_; uint8_t v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___x_408_; lean_object* v_fst_409_; lean_object* v_snd_410_; lean_object* v_declName_x3f_411_; lean_object* v_macroStack_412_; uint8_t v_mayPostpone_413_; uint8_t v_errToSorry_414_; lean_object* v_autoBoundImplicitContext_415_; lean_object* v_autoBoundImplicitForbidden_416_; lean_object* v_sectionVars_417_; lean_object* v_sectionFVars_418_; uint8_t v_implicitLambda_419_; uint8_t v_heedElabAsElim_420_; uint8_t v_isNoncomputableSection_421_; uint8_t v_isMetaSection_422_; uint8_t v_ignoreTCFailures_423_; uint8_t v_inPattern_424_; lean_object* v_tacSnap_x3f_425_; uint8_t v_saveRecAppSyntax_426_; uint8_t v_holesAsSyntheticOpaque_427_; uint8_t v_checkDeprecated_428_; lean_object* v_fixedTermElabs_429_; lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___y_433_; 
lean_inc_ref(v_split_349_);
v___x_408_ = lean_apply_1(v_split_349_, v_stx_351_);
v_fst_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_fst_409_);
v_snd_410_ = lean_ctor_get(v___x_408_, 1);
lean_inc_n(v_snd_410_, 2);
lean_dec_ref(v___x_408_);
v_declName_x3f_411_ = lean_ctor_get(v___y_354_, 0);
v_macroStack_412_ = lean_ctor_get(v___y_354_, 1);
v_mayPostpone_413_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8);
v_errToSorry_414_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_415_ = lean_ctor_get(v___y_354_, 2);
v_autoBoundImplicitForbidden_416_ = lean_ctor_get(v___y_354_, 3);
v_sectionVars_417_ = lean_ctor_get(v___y_354_, 4);
v_sectionFVars_418_ = lean_ctor_get(v___y_354_, 5);
v_implicitLambda_419_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 2);
v_heedElabAsElim_420_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_421_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 4);
v_isMetaSection_422_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_423_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 6);
v_inPattern_424_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_425_ = lean_ctor_get(v___y_354_, 6);
v_saveRecAppSyntax_426_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_427_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 9);
v_checkDeprecated_428_ = lean_ctor_get_uint8(v___y_354_, sizeof(void*)*8 + 10);
v_fixedTermElabs_429_ = lean_ctor_get(v___y_354_, 7);
lean_inc_ref(v_act_350_);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_430_, 0, v_act_350_);
lean_closure_set(v___f_430_, 1, v_snd_410_);
v___x_431_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_358_);
if (lean_obj_tag(v_tacSnap_x3f_425_) == 0)
{
lean_dec_ref(v___f_430_);
goto v___jp_454_;
}
else
{
lean_object* v_val_457_; lean_object* v_old_x3f_458_; 
v_val_457_ = lean_ctor_get(v_tacSnap_x3f_425_, 0);
v_old_x3f_458_ = lean_ctor_get(v_val_457_, 0);
if (lean_obj_tag(v_old_x3f_458_) == 1)
{
lean_object* v_val_459_; lean_object* v___x_460_; lean_object* v___f_461_; 
lean_dec(v_snd_410_);
lean_dec_ref(v_act_350_);
v_val_459_ = lean_ctor_get(v_old_x3f_458_, 0);
v___x_460_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___closed__0));
lean_inc(v_val_459_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_461_, 0, v_val_459_);
lean_closure_set(v___f_461_, 1, v___x_460_);
lean_closure_set(v___f_461_, 2, v___f_430_);
v___y_433_ = v___f_461_;
goto v___jp_432_;
}
else
{
lean_dec_ref(v___f_430_);
goto v___jp_454_;
}
}
v___jp_361_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_inc_ref(v___y_365_);
lean_inc(v___y_363_);
lean_inc(v___y_372_);
lean_inc_ref(v___y_366_);
lean_inc(v___y_380_);
lean_inc(v___y_362_);
lean_inc(v___y_374_);
v___x_382_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_382_, 0, v___y_374_);
lean_ctor_set(v___x_382_, 1, v___y_362_);
lean_ctor_set(v___x_382_, 2, v___y_380_);
lean_ctor_set(v___x_382_, 3, v___y_366_);
lean_ctor_set(v___x_382_, 4, v___y_372_);
lean_ctor_set(v___x_382_, 5, v___y_363_);
lean_ctor_set(v___x_382_, 6, v___y_381_);
lean_ctor_set(v___x_382_, 7, v___y_365_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8, v___y_373_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 1, v___y_364_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 2, v___y_376_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 3, v___y_377_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 4, v___y_368_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 5, v___y_371_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 6, v___y_375_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 7, v___y_370_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 8, v___y_369_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 9, v___y_367_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 10, v___y_378_);
lean_inc(v___y_359_);
lean_inc_ref(v___y_358_);
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
v___x_383_ = lean_apply_9(v___y_379_, v___y_352_, v___y_353_, v___x_382_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, lean_box(0));
return v___x_383_;
}
v___jp_384_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___y_405_);
lean_ctor_set(v___x_406_, 1, v_new_396_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___y_362_ = v___y_385_;
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
v___y_373_ = v___y_397_;
v___y_374_ = v___y_399_;
v___y_375_ = v___y_398_;
v___y_376_ = v___y_401_;
v___y_377_ = v___y_400_;
v___y_378_ = v___y_402_;
v___y_379_ = v___y_403_;
v___y_380_ = v___y_404_;
v___y_381_ = v___x_407_;
goto v___jp_361_;
}
v___jp_432_:
{
if (lean_obj_tag(v_tacSnap_x3f_425_) == 0)
{
lean_dec_ref(v___x_431_);
lean_dec(v_fst_409_);
lean_dec_ref(v_split_349_);
v___y_362_ = v_macroStack_412_;
v___y_363_ = v_sectionFVars_418_;
v___y_364_ = v_errToSorry_414_;
v___y_365_ = v_fixedTermElabs_429_;
v___y_366_ = v_autoBoundImplicitForbidden_416_;
v___y_367_ = v_holesAsSyntheticOpaque_427_;
v___y_368_ = v_isNoncomputableSection_421_;
v___y_369_ = v_saveRecAppSyntax_426_;
v___y_370_ = v_inPattern_424_;
v___y_371_ = v_isMetaSection_422_;
v___y_372_ = v_sectionVars_417_;
v___y_373_ = v_mayPostpone_413_;
v___y_374_ = v_declName_x3f_411_;
v___y_375_ = v_ignoreTCFailures_423_;
v___y_376_ = v_implicitLambda_419_;
v___y_377_ = v_heedElabAsElim_420_;
v___y_378_ = v_checkDeprecated_428_;
v___y_379_ = v___y_433_;
v___y_380_ = v_autoBoundImplicitContext_415_;
v___y_381_ = v_tacSnap_x3f_425_;
goto v___jp_361_;
}
else
{
lean_object* v_val_434_; lean_object* v_old_x3f_435_; 
v_val_434_ = lean_ctor_get(v_tacSnap_x3f_425_, 0);
v_old_x3f_435_ = lean_ctor_get(v_val_434_, 0);
if (lean_obj_tag(v_old_x3f_435_) == 0)
{
lean_object* v_new_436_; 
lean_dec_ref(v___x_431_);
lean_dec(v_fst_409_);
lean_dec_ref(v_split_349_);
v_new_436_ = lean_ctor_get(v_val_434_, 1);
lean_inc(v_new_436_);
v___y_385_ = v_macroStack_412_;
v___y_386_ = v_sectionFVars_418_;
v___y_387_ = v_errToSorry_414_;
v___y_388_ = v_fixedTermElabs_429_;
v___y_389_ = v_autoBoundImplicitForbidden_416_;
v___y_390_ = v_holesAsSyntheticOpaque_427_;
v___y_391_ = v_isNoncomputableSection_421_;
v___y_392_ = v_saveRecAppSyntax_426_;
v___y_393_ = v_inPattern_424_;
v___y_394_ = v_isMetaSection_422_;
v___y_395_ = v_sectionVars_417_;
v_new_396_ = v_new_436_;
v___y_397_ = v_mayPostpone_413_;
v___y_398_ = v_ignoreTCFailures_423_;
v___y_399_ = v_declName_x3f_411_;
v___y_400_ = v_heedElabAsElim_420_;
v___y_401_ = v_implicitLambda_419_;
v___y_402_ = v_checkDeprecated_428_;
v___y_403_ = v___y_433_;
v___y_404_ = v_autoBoundImplicitContext_415_;
v___y_405_ = v_old_x3f_435_;
goto v___jp_384_;
}
else
{
lean_object* v_val_437_; lean_object* v_new_438_; lean_object* v_stx_439_; lean_object* v_val_440_; lean_object* v___x_441_; lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v_val_437_ = lean_ctor_get(v_old_x3f_435_, 0);
v_new_438_ = lean_ctor_get(v_val_434_, 1);
v_stx_439_ = lean_ctor_get(v_val_437_, 0);
v_val_440_ = lean_ctor_get(v_val_437_, 1);
lean_inc(v_stx_439_);
v___x_441_ = lean_apply_1(v_split_349_, v_stx_439_);
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
v___x_447_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v___x_431_, v_fst_409_, v_fst_442_);
lean_dec_ref(v___x_431_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_del_object(v___x_445_);
lean_dec(v_snd_443_);
v___x_448_ = lean_box(0);
lean_inc(v_new_438_);
v___y_385_ = v_macroStack_412_;
v___y_386_ = v_sectionFVars_418_;
v___y_387_ = v_errToSorry_414_;
v___y_388_ = v_fixedTermElabs_429_;
v___y_389_ = v_autoBoundImplicitForbidden_416_;
v___y_390_ = v_holesAsSyntheticOpaque_427_;
v___y_391_ = v_isNoncomputableSection_421_;
v___y_392_ = v_saveRecAppSyntax_426_;
v___y_393_ = v_inPattern_424_;
v___y_394_ = v_isMetaSection_422_;
v___y_395_ = v_sectionVars_417_;
v_new_396_ = v_new_438_;
v___y_397_ = v_mayPostpone_413_;
v___y_398_ = v_ignoreTCFailures_423_;
v___y_399_ = v_declName_x3f_411_;
v___y_400_ = v_heedElabAsElim_420_;
v___y_401_ = v_implicitLambda_419_;
v___y_402_ = v_checkDeprecated_428_;
v___y_403_ = v___y_433_;
v___y_404_ = v_autoBoundImplicitContext_415_;
v___y_405_ = v___x_448_;
goto v___jp_384_;
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
v___y_385_ = v_macroStack_412_;
v___y_386_ = v_sectionFVars_418_;
v___y_387_ = v_errToSorry_414_;
v___y_388_ = v_fixedTermElabs_429_;
v___y_389_ = v_autoBoundImplicitForbidden_416_;
v___y_390_ = v_holesAsSyntheticOpaque_427_;
v___y_391_ = v_isNoncomputableSection_421_;
v___y_392_ = v_saveRecAppSyntax_426_;
v___y_393_ = v_inPattern_424_;
v___y_394_ = v_isMetaSection_422_;
v___y_395_ = v_sectionVars_417_;
v_new_396_ = v_new_438_;
v___y_397_ = v_mayPostpone_413_;
v___y_398_ = v_ignoreTCFailures_423_;
v___y_399_ = v_declName_x3f_411_;
v___y_400_ = v_heedElabAsElim_420_;
v___y_401_ = v_implicitLambda_419_;
v___y_402_ = v_checkDeprecated_428_;
v___y_403_ = v___y_433_;
v___y_404_ = v_autoBoundImplicitContext_415_;
v___y_405_ = v___x_451_;
goto v___jp_384_;
}
}
}
}
}
}
v___jp_454_:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_box(0);
v___x_456_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___x_456_, 0, v_act_350_);
lean_closure_set(v___x_456_, 1, v_snd_410_);
lean_closure_set(v___x_456_, 2, v___x_455_);
v___y_433_ = v___x_456_;
goto v___jp_432_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_split_349_ = stack[0].m_obj;
lean_object* v_act_350_ = stack[1].m_obj;
lean_object* v_stx_351_ = stack[2].m_obj;
lean_object* v___y_352_ = stack[3].m_obj;
lean_object* v___y_353_ = stack[4].m_obj;
lean_object* v___y_354_ = stack[5].m_obj;
lean_object* v___y_355_ = stack[6].m_obj;
lean_object* v___y_356_ = stack[7].m_obj;
lean_object* v___y_357_ = stack[8].m_obj;
lean_object* v___y_358_ = stack[9].m_obj;
lean_object* v___y_359_ = stack[10].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_349_, v_act_350_, v_stx_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(lean_object* v_split_463_, lean_object* v_act_464_, lean_object* v_stx_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_463_, v_act_464_, v_stx_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(lean_object* v_argIdx_479_, lean_object* v_stx_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_481_ = l_Lean_Syntax_getArgs(v_stx_480_);
v___x_482_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_479_);
v___x_483_ = l_Array_toSubarray___redArg(v___x_481_, v___x_482_, v_argIdx_479_);
v___x_484_ = l_Subarray_copy___redArg(v___x_483_);
v___x_485_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1));
v___x_486_ = lean_box(2);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_484_);
v___x_488_ = l_Lean_Syntax_getArg(v_stx_480_, v_argIdx_479_);
lean_dec(v_argIdx_479_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(lean_object* v_argIdx_490_, lean_object* v_stx_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(v_argIdx_490_, v_stx_491_);
lean_dec(v_stx_491_);
return v_res_492_;
}
}
lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(lean_object* v_argIdx_493_, lean_object* v_act_494_, lean_object* v_stx_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___f_505_; lean_object* v___x_506_; 
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_505_, 0, v_argIdx_493_);
v___x_506_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v___f_505_, v_act_494_, v_stx_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_506_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_argIdx_493_ = stack[0].m_obj;
lean_object* v_act_494_ = stack[1].m_obj;
lean_object* v_stx_495_ = stack[2].m_obj;
lean_object* v___y_496_ = stack[3].m_obj;
lean_object* v___y_497_ = stack[4].m_obj;
lean_object* v___y_498_ = stack[5].m_obj;
lean_object* v___y_499_ = stack[6].m_obj;
lean_object* v___y_500_ = stack[7].m_obj;
lean_object* v___y_501_ = stack[8].m_obj;
lean_object* v___y_502_ = stack[9].m_obj;
lean_object* v___y_503_ = stack[10].m_obj;
lean_object* v_res_507_;
v_res_507_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_493_, v_act_494_, v_stx_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(lean_object* v_argIdx_508_, lean_object* v_act_509_, lean_object* v_stx_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_508_, v_act_509_, v_stx_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_520_;
}
}
lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(lean_object* v_00_u03b1_521_, lean_object* v_argIdx_522_, lean_object* v_act_523_, lean_object* v_stx_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_522_, v_act_523_, v_stx_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
return v___x_534_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_argIdx_522_ = stack[1].m_obj;
lean_object* v_act_523_ = stack[2].m_obj;
lean_object* v_stx_524_ = stack[3].m_obj;
lean_object* v___y_525_ = stack[4].m_obj;
lean_object* v___y_526_ = stack[5].m_obj;
lean_object* v___y_527_ = stack[6].m_obj;
lean_object* v___y_528_ = stack[7].m_obj;
lean_object* v___y_529_ = stack[8].m_obj;
lean_object* v___y_530_ = stack[9].m_obj;
lean_object* v___y_531_ = stack[10].m_obj;
lean_object* v___y_532_ = stack[11].m_obj;
lean_object* v_res_535_;
v_res_535_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(lean_box(0), v_argIdx_522_, v_act_523_, v_stx_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
stack->m_obj
 = v_res_535_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(lean_object* v_00_u03b1_536_, lean_object* v_argIdx_537_, lean_object* v_act_538_, lean_object* v_stx_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(v_00_u03b1_536_, v_argIdx_537_, v_act_538_, v_stx_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_549_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v_env_555_; lean_object* v___x_556_; lean_object* v_toCold_557_; lean_object* v_mctx_558_; lean_object* v_currNamespace_559_; lean_object* v_openDecls_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_ngen_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_554_ = lean_st_ref_get(v___y_552_);
v_env_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc_ref(v_env_555_);
lean_dec(v___x_554_);
v___x_556_ = lean_st_ref_get(v___y_550_);
v_toCold_557_ = lean_ctor_get(v___y_551_, 0);
v_mctx_558_ = lean_ctor_get(v___x_556_, 0);
lean_inc_ref(v_mctx_558_);
lean_dec(v___x_556_);
v_currNamespace_559_ = lean_ctor_get(v_toCold_557_, 4);
v_openDecls_560_ = lean_ctor_get(v_toCold_557_, 5);
v___x_561_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_551_);
v___x_562_ = lean_st_ref_get(v___y_552_);
v_ngen_563_ = lean_ctor_get(v___x_562_, 2);
lean_inc_ref(v_ngen_563_);
lean_dec(v___x_562_);
v___x_564_ = lean_box(0);
v___x_565_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_560_);
lean_inc(v_currNamespace_559_);
v___x_566_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_566_, 0, v_env_555_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
lean_ctor_set(v___x_566_, 2, v___x_565_);
lean_ctor_set(v___x_566_, 3, v_mctx_558_);
lean_ctor_set(v___x_566_, 4, v___x_561_);
lean_ctor_set(v___x_566_, 5, v_currNamespace_559_);
lean_ctor_set(v___x_566_, 6, v_openDecls_560_);
lean_ctor_set(v___x_566_, 7, v_ngen_563_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_550_ = stack[0].m_obj;
lean_object* v___y_551_ = stack[1].m_obj;
lean_object* v___y_552_ = stack[2].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_550_, v___y_551_, v___y_552_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
return v_res_573_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v_toCold_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_609_; 
v___x_583_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_579_, v___y_580_, v___y_581_);
v_toCold_584_ = lean_ctor_get(v___y_580_, 0);
v_a_585_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_609_ == 0)
{
v___x_587_ = v___x_583_;
v_isShared_588_ = v_isSharedCheck_609_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_609_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_fileMap_589_; lean_object* v_env_590_; lean_object* v_mctx_591_; lean_object* v_options_592_; lean_object* v_currNamespace_593_; lean_object* v_openDecls_594_; lean_object* v_ngen_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_606_; 
v_fileMap_589_ = lean_ctor_get(v_toCold_584_, 1);
v_env_590_ = lean_ctor_get(v_a_585_, 0);
v_mctx_591_ = lean_ctor_get(v_a_585_, 3);
v_options_592_ = lean_ctor_get(v_a_585_, 4);
v_currNamespace_593_ = lean_ctor_get(v_a_585_, 5);
v_openDecls_594_ = lean_ctor_get(v_a_585_, 6);
v_ngen_595_ = lean_ctor_get(v_a_585_, 7);
v_isSharedCheck_606_ = !lean_is_exclusive(v_a_585_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; lean_object* v_unused_608_; 
v_unused_607_ = lean_ctor_get(v_a_585_, 2);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_a_585_, 1);
lean_dec(v_unused_608_);
v___x_597_ = v_a_585_;
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_ngen_595_);
lean_inc(v_openDecls_594_);
lean_inc(v_currNamespace_593_);
lean_inc(v_options_592_);
lean_inc(v_mctx_591_);
lean_inc(v_env_590_);
lean_dec(v_a_585_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_606_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
lean_inc_ref(v_fileMap_589_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 2, v_fileMap_589_);
lean_ctor_set(v___x_597_, 1, v___x_599_);
v___x_601_ = v___x_597_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_env_590_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_fileMap_589_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_mctx_591_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_options_592_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v_currNamespace_593_);
lean_ctor_set(v_reuseFailAlloc_605_, 6, v_openDecls_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 7, v_ngen_595_);
v___x_601_ = v_reuseFailAlloc_605_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_603_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_601_);
v___x_603_ = v___x_587_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_574_ = stack[0].m_obj;
lean_object* v___y_575_ = stack[1].m_obj;
lean_object* v___y_576_ = stack[2].m_obj;
lean_object* v___y_577_ = stack[3].m_obj;
lean_object* v___y_578_ = stack[4].m_obj;
lean_object* v___y_579_ = stack[5].m_obj;
lean_object* v___y_580_ = stack[6].m_obj;
lean_object* v___y_581_ = stack[7].m_obj;
lean_object* v_res_610_;
v_res_610_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2___boxed(lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_620_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v___x_630_; lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_640_; 
v___x_630_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_640_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_640_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v_a_631_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_621_ = stack[0].m_obj;
lean_object* v___y_622_ = stack[1].m_obj;
lean_object* v___y_623_ = stack[2].m_obj;
lean_object* v___y_624_ = stack[3].m_obj;
lean_object* v___y_625_ = stack[4].m_obj;
lean_object* v___y_626_ = stack[5].m_obj;
lean_object* v___y_627_ = stack[6].m_obj;
lean_object* v___y_628_ = stack[7].m_obj;
lean_object* v_res_641_;
v_res_641_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
stack->m_obj
 = v_res_641_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed(lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_651_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_unsigned_to_nat(32u);
v___x_653_ = lean_mk_empty_array_with_capacity(v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = ((size_t)5ULL);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_unsigned_to_nat(32u);
v___x_658_ = lean_mk_empty_array_with_capacity(v___x_657_);
v___x_659_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg___closed__0);
v___x_660_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___x_658_);
lean_ctor_set(v___x_660_, 2, v___x_656_);
lean_ctor_set(v___x_660_, 3, v___x_656_);
lean_ctor_set_usize(v___x_660_, 4, v___x_655_);
return v___x_660_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; lean_object* v_infoState_664_; lean_object* v_trees_665_; lean_object* v___x_666_; lean_object* v_infoState_667_; lean_object* v_env_668_; lean_object* v_nextMacroScope_669_; lean_object* v_ngen_670_; lean_object* v_auxDeclNGen_671_; lean_object* v_traceState_672_; lean_object* v_cache_673_; lean_object* v_recordedDeps_674_; lean_object* v_messages_675_; lean_object* v_snapshotTasks_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_697_; 
v___x_663_ = lean_st_ref_get(v___y_661_);
v_infoState_664_ = lean_ctor_get(v___x_663_, 8);
lean_inc_ref(v_infoState_664_);
lean_dec(v___x_663_);
v_trees_665_ = lean_ctor_get(v_infoState_664_, 2);
lean_inc_ref(v_trees_665_);
lean_dec_ref(v_infoState_664_);
v___x_666_ = lean_st_ref_take(v___y_661_);
v_infoState_667_ = lean_ctor_get(v___x_666_, 8);
v_env_668_ = lean_ctor_get(v___x_666_, 0);
v_nextMacroScope_669_ = lean_ctor_get(v___x_666_, 1);
v_ngen_670_ = lean_ctor_get(v___x_666_, 2);
v_auxDeclNGen_671_ = lean_ctor_get(v___x_666_, 3);
v_traceState_672_ = lean_ctor_get(v___x_666_, 4);
v_cache_673_ = lean_ctor_get(v___x_666_, 5);
v_recordedDeps_674_ = lean_ctor_get(v___x_666_, 6);
v_messages_675_ = lean_ctor_get(v___x_666_, 7);
v_snapshotTasks_676_ = lean_ctor_get(v___x_666_, 9);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_697_ == 0)
{
v___x_678_ = v___x_666_;
v_isShared_679_ = v_isSharedCheck_697_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snapshotTasks_676_);
lean_inc(v_infoState_667_);
lean_inc(v_messages_675_);
lean_inc(v_recordedDeps_674_);
lean_inc(v_cache_673_);
lean_inc(v_traceState_672_);
lean_inc(v_auxDeclNGen_671_);
lean_inc(v_ngen_670_);
lean_inc(v_nextMacroScope_669_);
lean_inc(v_env_668_);
lean_dec(v___x_666_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_697_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
uint8_t v_enabled_680_; lean_object* v_assignment_681_; lean_object* v_lazyAssignment_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_695_; 
v_enabled_680_ = lean_ctor_get_uint8(v_infoState_667_, sizeof(void*)*3);
v_assignment_681_ = lean_ctor_get(v_infoState_667_, 0);
v_lazyAssignment_682_ = lean_ctor_get(v_infoState_667_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_infoState_667_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_infoState_667_, 2);
lean_dec(v_unused_696_);
v___x_684_ = v_infoState_667_;
v_isShared_685_ = v_isSharedCheck_695_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_lazyAssignment_682_);
lean_inc(v_assignment_681_);
lean_dec(v_infoState_667_);
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
lean_ctor_set(v___x_678_, 8, v___x_688_);
v___x_690_ = v___x_678_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_env_668_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_nextMacroScope_669_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_ngen_670_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v_auxDeclNGen_671_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_traceState_672_);
lean_ctor_set(v_reuseFailAlloc_693_, 5, v_cache_673_);
lean_ctor_set(v_reuseFailAlloc_693_, 6, v_recordedDeps_674_);
lean_ctor_set(v_reuseFailAlloc_693_, 7, v_messages_675_);
lean_ctor_set(v_reuseFailAlloc_693_, 8, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_693_, 9, v_snapshotTasks_676_);
v___x_690_ = v_reuseFailAlloc_693_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_st_ref_put(v___y_661_, v___x_690_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_trees_665_);
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_661_ = stack[0].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_661_);
stack->m_obj
 = v_res_698_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(lean_object* v___x_702_, lean_object* v_ctx_x3f_703_, size_t v_sz_704_, size_t v_i_705_, lean_object* v_bs_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_lt(v_i_705_, v_sz_704_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec_ref(v_ctx_x3f_703_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_bs_706_);
return v___x_717_;
}
else
{
lean_object* v_assignment_718_; lean_object* v_v_719_; lean_object* v___x_720_; lean_object* v_bs_x27_721_; lean_object* v_a_723_; lean_object* v_tree_728_; lean_object* v___x_729_; 
v_assignment_718_ = lean_ctor_get(v___x_702_, 0);
v_v_719_ = lean_array_uget(v_bs_706_, v_i_705_);
v___x_720_ = lean_unsigned_to_nat(0u);
v_bs_x27_721_ = lean_array_uset(v_bs_706_, v_i_705_, v___x_720_);
v_tree_728_ = l_Lean_Elab_InfoTree_substitute(v_v_719_, v_assignment_718_);
lean_inc_ref(v_ctx_x3f_703_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
v___x_729_ = lean_apply_9(v_ctx_x3f_703_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, lean_box(0));
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
if (lean_obj_tag(v_a_730_) == 0)
{
v_a_723_ = v_tree_728_;
goto v___jp_722_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_732_; 
v_val_731_ = lean_ctor_get(v_a_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref_known(v_a_730_, 1);
v___x_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_732_, 0, v_val_731_);
lean_ctor_set(v___x_732_, 1, v_tree_728_);
v_a_723_ = v___x_732_;
goto v___jp_722_;
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v_tree_728_);
lean_dec_ref(v_bs_x27_721_);
lean_dec_ref(v_ctx_x3f_703_);
v_a_733_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_729_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_729_);
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
v___jp_722_:
{
size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; 
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_705_, v___x_724_);
v___x_726_ = lean_array_uset(v_bs_x27_721_, v_i_705_, v_a_723_);
v_i_705_ = v___x_725_;
v_bs_706_ = v___x_726_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_702_ = stack[0].m_obj;
lean_object* v_ctx_x3f_703_ = stack[1].m_obj;
size_t v_sz_704_ = stack[2].m_num;
size_t v_i_705_ = stack[3].m_num;
lean_object* v_bs_706_ = stack[4].m_obj;
lean_object* v___y_707_ = stack[5].m_obj;
lean_object* v___y_708_ = stack[6].m_obj;
lean_object* v___y_709_ = stack[7].m_obj;
lean_object* v___y_710_ = stack[8].m_obj;
lean_object* v___y_711_ = stack[9].m_obj;
lean_object* v___y_712_ = stack[10].m_obj;
lean_object* v___y_713_ = stack[11].m_obj;
lean_object* v___y_714_ = stack[12].m_obj;
lean_object* v_res_741_;
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_702_, v_ctx_x3f_703_, v_sz_704_, v_i_705_, v_bs_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10___boxed(lean_object* v___x_742_, lean_object* v_ctx_x3f_743_, lean_object* v_sz_744_, lean_object* v_i_745_, lean_object* v_bs_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
size_t v_sz_boxed_756_; size_t v_i_boxed_757_; lean_object* v_res_758_; 
v_sz_boxed_756_ = lean_unbox_usize(v_sz_744_);
lean_dec(v_sz_744_);
v_i_boxed_757_ = lean_unbox_usize(v_i_745_);
lean_dec(v_i_745_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_742_, v_ctx_x3f_743_, v_sz_boxed_756_, v_i_boxed_757_, v_bs_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v___x_742_);
return v_res_758_;
}
}
lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(lean_object* v___x_759_, lean_object* v_ctx_x3f_760_, lean_object* v_x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v_cs_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_797_; 
v_cs_771_ = lean_ctor_get(v_x_761_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_797_ == 0)
{
v___x_773_ = v_x_761_;
v_isShared_774_ = v_isSharedCheck_797_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_cs_771_);
lean_dec(v_x_761_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_797_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
size_t v_sz_775_; size_t v___x_776_; lean_object* v___x_777_; 
v_sz_775_ = lean_array_size(v_cs_771_);
v___x_776_ = ((size_t)0ULL);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_759_, v_ctx_x3f_760_, v_sz_775_, v___x_776_, v_cs_771_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_788_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_788_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_788_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_a_778_);
v___x_783_ = v___x_773_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_del_object(v___x_773_);
v_a_789_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_777_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_777_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
else
{
lean_object* v_vs_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_824_; 
v_vs_798_ = lean_ctor_get(v_x_761_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_824_ == 0)
{
v___x_800_ = v_x_761_;
v_isShared_801_ = v_isSharedCheck_824_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_vs_798_);
lean_dec(v_x_761_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_824_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
size_t v_sz_802_; size_t v___x_803_; lean_object* v___x_804_; 
v_sz_802_ = lean_array_size(v_vs_798_);
v___x_803_ = ((size_t)0ULL);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_759_, v_ctx_x3f_760_, v_sz_802_, v___x_803_, v_vs_798_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_815_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_815_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_815_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_a_805_);
v___x_810_ = v___x_800_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_810_);
v___x_812_ = v___x_807_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_del_object(v___x_800_);
v_a_816_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_804_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_804_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_759_ = stack[0].m_obj;
lean_object* v_ctx_x3f_760_ = stack[1].m_obj;
lean_object* v_x_761_ = stack[2].m_obj;
lean_object* v___y_762_ = stack[3].m_obj;
lean_object* v___y_763_ = stack[4].m_obj;
lean_object* v___y_764_ = stack[5].m_obj;
lean_object* v___y_765_ = stack[6].m_obj;
lean_object* v___y_766_ = stack[7].m_obj;
lean_object* v___y_767_ = stack[8].m_obj;
lean_object* v___y_768_ = stack[9].m_obj;
lean_object* v___y_769_ = stack[10].m_obj;
lean_object* v_res_825_;
v_res_825_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_759_, v_ctx_x3f_760_, v_x_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
stack->m_obj
 = v_res_825_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(lean_object* v___x_826_, lean_object* v_ctx_x3f_827_, size_t v_sz_828_, size_t v_i_829_, lean_object* v_bs_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = lean_usize_dec_lt(v_i_829_, v_sz_828_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec_ref(v_ctx_x3f_827_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v_bs_830_);
return v___x_841_;
}
else
{
lean_object* v_v_842_; lean_object* v___x_843_; lean_object* v_bs_x27_844_; lean_object* v___x_845_; 
v_v_842_ = lean_array_uget(v_bs_830_, v_i_829_);
v___x_843_ = lean_unsigned_to_nat(0u);
v_bs_x27_844_ = lean_array_uset(v_bs_830_, v_i_829_, v___x_843_);
lean_inc_ref(v_ctx_x3f_827_);
v___x_845_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_826_, v_ctx_x3f_827_, v_v_842_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_add(v_i_829_, v___x_847_);
v___x_849_ = lean_array_uset(v_bs_x27_844_, v_i_829_, v_a_846_);
v_i_829_ = v___x_848_;
v_bs_830_ = v___x_849_;
goto _start;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v_bs_x27_844_);
lean_dec_ref(v_ctx_x3f_827_);
v_a_851_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_845_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_845_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_826_ = stack[0].m_obj;
lean_object* v_ctx_x3f_827_ = stack[1].m_obj;
size_t v_sz_828_ = stack[2].m_num;
size_t v_i_829_ = stack[3].m_num;
lean_object* v_bs_830_ = stack[4].m_obj;
lean_object* v___y_831_ = stack[5].m_obj;
lean_object* v___y_832_ = stack[6].m_obj;
lean_object* v___y_833_ = stack[7].m_obj;
lean_object* v___y_834_ = stack[8].m_obj;
lean_object* v___y_835_ = stack[9].m_obj;
lean_object* v___y_836_ = stack[10].m_obj;
lean_object* v___y_837_ = stack[11].m_obj;
lean_object* v___y_838_ = stack[12].m_obj;
lean_object* v_res_859_;
v_res_859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_826_, v_ctx_x3f_827_, v_sz_828_, v_i_829_, v_bs_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(lean_object* v___x_860_, lean_object* v_ctx_x3f_861_, lean_object* v_sz_862_, lean_object* v_i_863_, lean_object* v_bs_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
size_t v_sz_boxed_874_; size_t v_i_boxed_875_; lean_object* v_res_876_; 
v_sz_boxed_874_ = lean_unbox_usize(v_sz_862_);
lean_dec(v_sz_862_);
v_i_boxed_875_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9_spec__10(v___x_860_, v_ctx_x3f_861_, v_sz_boxed_874_, v_i_boxed_875_, v_bs_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec_ref(v___x_860_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9___boxed(lean_object* v___x_877_, lean_object* v_ctx_x3f_878_, lean_object* v_x_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_877_, v_ctx_x3f_878_, v_x_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v___x_877_);
return v_res_889_;
}
}
lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(lean_object* v___x_890_, lean_object* v_ctx_x3f_891_, lean_object* v_t_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_root_902_; lean_object* v_tail_903_; lean_object* v_size_904_; size_t v_shift_905_; lean_object* v_tailOff_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_942_; 
v_root_902_ = lean_ctor_get(v_t_892_, 0);
v_tail_903_ = lean_ctor_get(v_t_892_, 1);
v_size_904_ = lean_ctor_get(v_t_892_, 2);
v_shift_905_ = lean_ctor_get_usize(v_t_892_, 4);
v_tailOff_906_ = lean_ctor_get(v_t_892_, 3);
v_isSharedCheck_942_ = !lean_is_exclusive(v_t_892_);
if (v_isSharedCheck_942_ == 0)
{
v___x_908_ = v_t_892_;
v_isShared_909_ = v_isSharedCheck_942_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_tailOff_906_);
lean_inc(v_size_904_);
lean_inc(v_tail_903_);
lean_inc(v_root_902_);
lean_dec(v_t_892_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_942_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; 
lean_inc_ref(v_ctx_x3f_891_);
v___x_910_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__9(v___x_890_, v_ctx_x3f_891_, v_root_902_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; size_t v_sz_912_; size_t v___x_913_; lean_object* v___x_914_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v_sz_912_ = lean_array_size(v_tail_903_);
v___x_913_ = ((size_t)0ULL);
v___x_914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_spec__10(v___x_890_, v_ctx_x3f_891_, v_sz_912_, v___x_913_, v_tail_903_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_925_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_925_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_925_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 1, v_a_915_);
lean_ctor_set(v___x_908_, 0, v_a_911_);
v___x_920_ = v___x_908_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_911_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_915_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_size_904_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_tailOff_906_);
lean_ctor_set_usize(v_reuseFailAlloc_924_, 4, v_shift_905_);
v___x_920_ = v_reuseFailAlloc_924_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_922_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_920_);
v___x_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_911_);
lean_del_object(v___x_908_);
lean_dec(v_tailOff_906_);
lean_dec(v_size_904_);
v_a_926_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_914_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_914_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_del_object(v___x_908_);
lean_dec(v_tailOff_906_);
lean_dec(v_size_904_);
lean_dec_ref(v_tail_903_);
lean_dec_ref(v_ctx_x3f_891_);
v_a_934_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_910_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_910_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_890_ = stack[0].m_obj;
lean_object* v_ctx_x3f_891_ = stack[1].m_obj;
lean_object* v_t_892_ = stack[2].m_obj;
lean_object* v___y_893_ = stack[3].m_obj;
lean_object* v___y_894_ = stack[4].m_obj;
lean_object* v___y_895_ = stack[5].m_obj;
lean_object* v___y_896_ = stack[6].m_obj;
lean_object* v___y_897_ = stack[7].m_obj;
lean_object* v___y_898_ = stack[8].m_obj;
lean_object* v___y_899_ = stack[9].m_obj;
lean_object* v___y_900_ = stack[10].m_obj;
lean_object* v_res_943_;
v_res_943_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v___x_890_, v_ctx_x3f_891_, v_t_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
stack->m_obj
 = v_res_943_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8___boxed(lean_object* v___x_944_, lean_object* v_ctx_x3f_945_, lean_object* v_t_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v___x_944_, v_ctx_x3f_945_, v_t_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec_ref(v___x_944_);
return v_res_956_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(lean_object* v___y_957_, lean_object* v_ctx_x3f_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v_a_966_, lean_object* v_a_x3f_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_infoState_970_; lean_object* v_trees_971_; lean_object* v___x_972_; 
v___x_969_ = lean_st_ref_get(v___y_957_);
v_infoState_970_ = lean_ctor_get(v___x_969_, 8);
lean_inc_ref(v_infoState_970_);
lean_dec(v___x_969_);
v_trees_971_ = lean_ctor_get(v_infoState_970_, 2);
lean_inc_ref(v_trees_971_);
v___x_972_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__8(v_infoState_970_, v_ctx_x3f_958_, v_trees_971_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_957_);
lean_dec_ref(v_infoState_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1012_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1012_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1012_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v_infoState_978_; lean_object* v_env_979_; lean_object* v_nextMacroScope_980_; lean_object* v_ngen_981_; lean_object* v_auxDeclNGen_982_; lean_object* v_traceState_983_; lean_object* v_cache_984_; lean_object* v_recordedDeps_985_; lean_object* v_messages_986_; lean_object* v_snapshotTasks_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1011_; 
v___x_977_ = lean_st_ref_take(v___y_957_);
v_infoState_978_ = lean_ctor_get(v___x_977_, 8);
v_env_979_ = lean_ctor_get(v___x_977_, 0);
v_nextMacroScope_980_ = lean_ctor_get(v___x_977_, 1);
v_ngen_981_ = lean_ctor_get(v___x_977_, 2);
v_auxDeclNGen_982_ = lean_ctor_get(v___x_977_, 3);
v_traceState_983_ = lean_ctor_get(v___x_977_, 4);
v_cache_984_ = lean_ctor_get(v___x_977_, 5);
v_recordedDeps_985_ = lean_ctor_get(v___x_977_, 6);
v_messages_986_ = lean_ctor_get(v___x_977_, 7);
v_snapshotTasks_987_ = lean_ctor_get(v___x_977_, 9);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_989_ = v___x_977_;
v_isShared_990_ = v_isSharedCheck_1011_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_snapshotTasks_987_);
lean_inc(v_infoState_978_);
lean_inc(v_messages_986_);
lean_inc(v_recordedDeps_985_);
lean_inc(v_cache_984_);
lean_inc(v_traceState_983_);
lean_inc(v_auxDeclNGen_982_);
lean_inc(v_ngen_981_);
lean_inc(v_nextMacroScope_980_);
lean_inc(v_env_979_);
lean_dec(v___x_977_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1011_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
uint8_t v_enabled_991_; lean_object* v_assignment_992_; lean_object* v_lazyAssignment_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1009_; 
v_enabled_991_ = lean_ctor_get_uint8(v_infoState_978_, sizeof(void*)*3);
v_assignment_992_ = lean_ctor_get(v_infoState_978_, 0);
v_lazyAssignment_993_ = lean_ctor_get(v_infoState_978_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_infoState_978_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_infoState_978_, 2);
lean_dec(v_unused_1010_);
v___x_995_ = v_infoState_978_;
v_isShared_996_ = v_isSharedCheck_1009_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_lazyAssignment_993_);
lean_inc(v_assignment_992_);
lean_dec(v_infoState_978_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1009_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_997_ = lean_box(0);
v___x_998_ = l_Lean_PersistentArray_append___redArg(v_a_966_, v_a_973_);
lean_dec(v_a_973_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 2, v___x_998_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_assignment_992_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_lazyAssignment_993_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v___x_998_);
lean_ctor_set_uint8(v_reuseFailAlloc_1008_, sizeof(void*)*3, v_enabled_991_);
v___x_1000_ = v_reuseFailAlloc_1008_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1002_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 8, v___x_1000_);
v___x_1002_ = v___x_989_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_env_979_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_nextMacroScope_980_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_ngen_981_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_auxDeclNGen_982_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_traceState_983_);
lean_ctor_set(v_reuseFailAlloc_1007_, 5, v_cache_984_);
lean_ctor_set(v_reuseFailAlloc_1007_, 6, v_recordedDeps_985_);
lean_ctor_set(v_reuseFailAlloc_1007_, 7, v_messages_986_);
lean_ctor_set(v_reuseFailAlloc_1007_, 8, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1007_, 9, v_snapshotTasks_987_);
v___x_1002_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = lean_st_ref_put(v___y_957_, v___x_1002_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_997_);
v___x_1005_ = v___x_975_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_997_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_dec_ref(v_a_966_);
v_a_1013_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_972_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_972_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_957_ = stack[0].m_obj;
lean_object* v_ctx_x3f_958_ = stack[1].m_obj;
lean_object* v___y_959_ = stack[2].m_obj;
lean_object* v___y_960_ = stack[3].m_obj;
lean_object* v___y_961_ = stack[4].m_obj;
lean_object* v___y_962_ = stack[5].m_obj;
lean_object* v___y_963_ = stack[6].m_obj;
lean_object* v___y_964_ = stack[7].m_obj;
lean_object* v___y_965_ = stack[8].m_obj;
lean_object* v_a_966_ = stack[9].m_obj;
lean_object* v_a_x3f_967_ = stack[10].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_957_, v_ctx_x3f_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v_a_966_, v_a_x3f_967_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___y_1022_, lean_object* v_ctx_x3f_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v_a_1031_, lean_object* v_a_x3f_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1022_, v_ctx_x3f_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v_a_1031_, v_a_x3f_1032_);
lean_dec(v_a_x3f_1032_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1022_);
return v_res_1034_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(lean_object* v_x_1035_, lean_object* v_ctx_x3f_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; lean_object* v_infoState_1047_; uint8_t v_enabled_1048_; 
v___x_1046_ = lean_st_ref_get(v___y_1044_);
v_infoState_1047_ = lean_ctor_get(v___x_1046_, 8);
lean_inc_ref(v_infoState_1047_);
lean_dec(v___x_1046_);
v_enabled_1048_ = lean_ctor_get_uint8(v_infoState_1047_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1047_);
if (v_enabled_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec_ref(v_ctx_x3f_1036_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v___x_1049_ = lean_apply_9(v_x_1035_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; lean_object* v_a_1051_; lean_object* v_r_1052_; 
v___x_1050_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_1044_);
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref(v___x_1050_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v_r_1052_ = lean_apply_9(v_x_1035_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
if (lean_obj_tag(v_r_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1077_; 
v_a_1053_ = lean_ctor_get(v_r_1052_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1055_ = v_r_1052_;
v_isShared_1056_ = v_isSharedCheck_1077_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v_r_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1077_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
lean_inc(v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 1);
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; 
v___x_1059_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1044_, v_ctx_x3f_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v_a_1051_, v___x_1058_);
lean_dec_ref(v___x_1058_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v___x_1059_, 0);
lean_dec(v_unused_1067_);
v___x_1061_ = v___x_1059_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_dec(v___x_1059_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_a_1053_);
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1053_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec(v_a_1053_);
v_a_1068_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1059_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1059_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_a_1078_ = lean_ctor_get(v_r_1052_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v_r_1052_, 1);
v___x_1079_ = lean_box(0);
v___x_1080_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1044_, v_ctx_x3f_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v_a_1051_, v___x_1079_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v___x_1080_, 0);
lean_dec(v_unused_1088_);
v___x_1082_ = v___x_1080_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v___x_1080_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 1);
lean_ctor_set(v___x_1082_, 0, v_a_1078_);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1078_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec(v_a_1078_);
v_a_1089_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1080_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1080_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1035_ = stack[0].m_obj;
lean_object* v_ctx_x3f_1036_ = stack[1].m_obj;
lean_object* v___y_1037_ = stack[2].m_obj;
lean_object* v___y_1038_ = stack[3].m_obj;
lean_object* v___y_1039_ = stack[4].m_obj;
lean_object* v___y_1040_ = stack[5].m_obj;
lean_object* v___y_1041_ = stack[6].m_obj;
lean_object* v___y_1042_ = stack[7].m_obj;
lean_object* v___y_1043_ = stack[8].m_obj;
lean_object* v___y_1044_ = stack[9].m_obj;
lean_object* v_res_1097_;
v_res_1097_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1035_, v_ctx_x3f_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
stack->m_obj
 = v_res_1097_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___boxed(lean_object* v_x_1098_, lean_object* v_ctx_x3f_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1098_, v_ctx_x3f_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1109_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(lean_object* v_x_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___f_1121_; lean_object* v___x_1122_; 
v___f_1121_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0));
v___x_1122_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1111_, v___f_1121_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1122_;
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1111_ = stack[0].m_obj;
lean_object* v___y_1112_ = stack[1].m_obj;
lean_object* v___y_1113_ = stack[2].m_obj;
lean_object* v___y_1114_ = stack[3].m_obj;
lean_object* v___y_1115_ = stack[4].m_obj;
lean_object* v___y_1116_ = stack[5].m_obj;
lean_object* v___y_1117_ = stack[6].m_obj;
lean_object* v___y_1118_ = stack[7].m_obj;
lean_object* v___y_1119_ = stack[8].m_obj;
lean_object* v_res_1123_;
v_res_1123_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
stack->m_obj
 = v_res_1123_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(lean_object* v_x_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1134_;
}
}
lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(lean_object* v_00_u03b1_1135_, lean_object* v_x_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
return v___x_1146_;
}
}
LEAN_EXPORT void l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1136_ = stack[1].m_obj;
lean_object* v___y_1137_ = stack[2].m_obj;
lean_object* v___y_1138_ = stack[3].m_obj;
lean_object* v___y_1139_ = stack[4].m_obj;
lean_object* v___y_1140_ = stack[5].m_obj;
lean_object* v___y_1141_ = stack[6].m_obj;
lean_object* v___y_1142_ = stack[7].m_obj;
lean_object* v___y_1143_ = stack[8].m_obj;
lean_object* v___y_1144_ = stack[9].m_obj;
lean_object* v_res_1147_;
v_res_1147_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(lean_box(0), v_x_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_x_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(v_00_u03b1_1148_, v_x_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1159_;
}
}
lean_object* l_Lean_Elab_Tactic_evalClassical(lean_object* v_stx_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Tactic_evalClassical___closed__0));
v___x_1173_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed), 13, 4);
lean_closure_set(v___x_1173_, 0, lean_box(0));
lean_closure_set(v___x_1173_, 1, v___x_1171_);
lean_closure_set(v___x_1173_, 2, v___x_1172_);
lean_closure_set(v___x_1173_, 3, v_stx_1161_);
v___x_1174_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed), 11, 2);
lean_closure_set(v___x_1174_, 0, lean_box(0));
lean_closure_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v___x_1174_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1175_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_evalClassical_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1161_ = stack[0].m_obj;
lean_object* v_a_1162_ = stack[1].m_obj;
lean_object* v_a_1163_ = stack[2].m_obj;
lean_object* v_a_1164_ = stack[3].m_obj;
lean_object* v_a_1165_ = stack[4].m_obj;
lean_object* v_a_1166_ = stack[5].m_obj;
lean_object* v_a_1167_ = stack[6].m_obj;
lean_object* v_a_1168_ = stack[7].m_obj;
lean_object* v_a_1169_ = stack[8].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l_Lean_Elab_Tactic_evalClassical(v_stx_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___boxed(lean_object* v_stx_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Elab_Tactic_evalClassical(v_stx_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
return v_res_1187_;
}
}
lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1188_, lean_object* v_stx_1189_, lean_object* v_act_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___redArg(v_stx_1189_, v_act_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1189_ = stack[1].m_obj;
lean_object* v_act_1190_ = stack[2].m_obj;
lean_object* v___y_1191_ = stack[3].m_obj;
lean_object* v___y_1192_ = stack[4].m_obj;
lean_object* v___y_1193_ = stack[5].m_obj;
lean_object* v___y_1194_ = stack[6].m_obj;
lean_object* v___y_1195_ = stack[7].m_obj;
lean_object* v___y_1196_ = stack[8].m_obj;
lean_object* v___y_1197_ = stack[9].m_obj;
lean_object* v___y_1198_ = stack[10].m_obj;
lean_object* v_res_1201_;
v_res_1201_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(lean_box(0), v_stx_1189_, v_act_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
stack->m_obj
 = v_res_1201_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1202_, lean_object* v_stx_1203_, lean_object* v_act_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__2(v_00_u03b1_1202_, v_stx_1203_, v_act_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1214_;
}
}
lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(lean_object* v_00_u03b1_1215_, lean_object* v_split_1216_, lean_object* v_act_1217_, lean_object* v_stx_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_1216_, v_act_1217_, v_stx_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
return v___x_1228_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_split_1216_ = stack[1].m_obj;
lean_object* v_act_1217_ = stack[2].m_obj;
lean_object* v_stx_1218_ = stack[3].m_obj;
lean_object* v___y_1219_ = stack[4].m_obj;
lean_object* v___y_1220_ = stack[5].m_obj;
lean_object* v___y_1221_ = stack[6].m_obj;
lean_object* v___y_1222_ = stack[7].m_obj;
lean_object* v___y_1223_ = stack[8].m_obj;
lean_object* v___y_1224_ = stack[9].m_obj;
lean_object* v___y_1225_ = stack[10].m_obj;
lean_object* v___y_1226_ = stack[11].m_obj;
lean_object* v_res_1229_;
v_res_1229_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(lean_box(0), v_split_1216_, v_act_1217_, v_stx_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
stack->m_obj
 = v_res_1229_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_split_1231_, lean_object* v_act_1232_, lean_object* v_stx_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(v_00_u03b1_1230_, v_split_1231_, v_act_1232_, v_stx_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
return v_res_1243_;
}
}
lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___redArg(v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT void l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1244_ = stack[0].m_obj;
lean_object* v___y_1245_ = stack[1].m_obj;
lean_object* v___y_1246_ = stack[2].m_obj;
lean_object* v___y_1247_ = stack[3].m_obj;
lean_object* v___y_1248_ = stack[4].m_obj;
lean_object* v___y_1249_ = stack[5].m_obj;
lean_object* v___y_1250_ = stack[6].m_obj;
lean_object* v___y_1251_ = stack[7].m_obj;
lean_object* v_res_1254_;
v_res_1254_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
stack->m_obj
 = v_res_1254_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5___boxed(lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__5(v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1264_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___redArg(v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1265_ = stack[0].m_obj;
lean_object* v___y_1266_ = stack[1].m_obj;
lean_object* v___y_1267_ = stack[2].m_obj;
lean_object* v___y_1268_ = stack[3].m_obj;
lean_object* v___y_1269_ = stack[4].m_obj;
lean_object* v___y_1270_ = stack[5].m_obj;
lean_object* v___y_1271_ = stack[6].m_obj;
lean_object* v___y_1272_ = stack[7].m_obj;
lean_object* v_res_1275_;
v_res_1275_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
stack->m_obj
 = v_res_1275_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1285_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(lean_object* v_00_u03b1_1286_, lean_object* v_x_1287_, lean_object* v_ctx_x3f_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1287_, v_ctx_x3f_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1287_ = stack[1].m_obj;
lean_object* v_ctx_x3f_1288_ = stack[2].m_obj;
lean_object* v___y_1289_ = stack[3].m_obj;
lean_object* v___y_1290_ = stack[4].m_obj;
lean_object* v___y_1291_ = stack[5].m_obj;
lean_object* v___y_1292_ = stack[6].m_obj;
lean_object* v___y_1293_ = stack[7].m_obj;
lean_object* v___y_1294_ = stack[8].m_obj;
lean_object* v___y_1295_ = stack[9].m_obj;
lean_object* v___y_1296_ = stack[10].m_obj;
lean_object* v_res_1299_;
v_res_1299_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(lean_box(0), v_x_1287_, v_ctx_x3f_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
stack->m_obj
 = v_res_1299_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1300_, lean_object* v_x_1301_, lean_object* v_ctx_x3f_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(v_00_u03b1_1300_, v_x_1301_, v_ctx_x3f_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
return v_res_1312_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1(){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1330_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1331_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4));
v___x_1332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1333_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalClassical___boxed), 10, 0);
v___x_1334_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1330_, v___x_1331_, v___x_1332_, v___x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1335_;
v_res_1335_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
stack->m_obj
 = v_res_1335_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___boxed(lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
return v_res_1337_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3(){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1340_ = l_Lean_Elab_addBuiltinIncrementalElab(v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1341_;
v_res_1341_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
stack->m_obj
 = v_res_1341_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
return v_res_1343_;
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
