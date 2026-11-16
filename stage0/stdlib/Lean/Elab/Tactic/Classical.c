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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0___boxed(lean_object* v___y_110_, lean_object* v___x_111_, lean_object* v___x_112_, lean_object* v___y_113_, lean_object* v___x_114_, lean_object* v_a_x3f_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_110_, v___x_111_, v___x_112_, v___y_113_, v___x_114_, v_a_x3f_115_);
lean_dec(v_a_x3f_115_);
lean_dec(v___y_113_);
lean_dec(v___y_110_);
return v_res_117_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_118_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0);
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg(){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__1);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___boxed(lean_object* v___dummy_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg();
return v_res_124_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg___closed__0);
v___x_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10___redArg();
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
v___x_134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
lean_ctor_set(v___x_134_, 2, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_135_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__4, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__4);
v___x_136_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__3);
v___x_137_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__0);
v___x_138_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
v___x_139_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
lean_ctor_set(v___x_139_, 2, v___x_136_);
lean_ctor_set(v___x_139_, 3, v___x_137_);
lean_ctor_set(v___x_139_, 4, v___x_137_);
lean_ctor_set(v___x_139_, 5, v___x_137_);
lean_ctor_set(v___x_139_, 6, v___x_137_);
lean_ctor_set(v___x_139_, 7, v___x_135_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(lean_object* v_t_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_env_152_; lean_object* v_nextMacroScope_153_; lean_object* v_ngen_154_; lean_object* v_auxDeclNGen_155_; lean_object* v_traceState_156_; lean_object* v_recordedDeps_157_; lean_object* v_messages_158_; lean_object* v_infoState_159_; lean_object* v_snapshotTasks_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_226_; 
v___x_150_ = l_Lean_Meta_instanceExtension;
v___x_151_ = lean_st_ref_take(v___y_148_);
v_env_152_ = lean_ctor_get(v___x_151_, 0);
v_nextMacroScope_153_ = lean_ctor_get(v___x_151_, 1);
v_ngen_154_ = lean_ctor_get(v___x_151_, 2);
v_auxDeclNGen_155_ = lean_ctor_get(v___x_151_, 3);
v_traceState_156_ = lean_ctor_get(v___x_151_, 4);
v_recordedDeps_157_ = lean_ctor_get(v___x_151_, 6);
v_messages_158_ = lean_ctor_get(v___x_151_, 7);
v_infoState_159_ = lean_ctor_get(v___x_151_, 8);
v_snapshotTasks_160_ = lean_ctor_get(v___x_151_, 9);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_226_ == 0)
{
lean_object* v_unused_227_; 
v_unused_227_ = lean_ctor_get(v___x_151_, 5);
lean_dec(v_unused_227_);
v___x_162_ = v___x_151_;
v_isShared_163_ = v_isSharedCheck_226_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_snapshotTasks_160_);
lean_inc(v_infoState_159_);
lean_inc(v_messages_158_);
lean_inc(v_recordedDeps_157_);
lean_inc(v_traceState_156_);
lean_inc(v_auxDeclNGen_155_);
lean_inc(v_ngen_154_);
lean_inc(v_nextMacroScope_153_);
lean_inc(v_env_152_);
lean_dec(v___x_151_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_226_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_164_ = l_Lean_ScopedEnvExtension_pushScope___redArg(v___x_150_, v_env_152_);
v___x_165_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__1);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 5, v___x_165_);
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_nextMacroScope_153_);
lean_ctor_set(v_reuseFailAlloc_225_, 2, v_ngen_154_);
lean_ctor_set(v_reuseFailAlloc_225_, 3, v_auxDeclNGen_155_);
lean_ctor_set(v_reuseFailAlloc_225_, 4, v_traceState_156_);
lean_ctor_set(v_reuseFailAlloc_225_, 5, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_225_, 6, v_recordedDeps_157_);
lean_ctor_set(v_reuseFailAlloc_225_, 7, v_messages_158_);
lean_ctor_set(v_reuseFailAlloc_225_, 8, v_infoState_159_);
lean_ctor_set(v_reuseFailAlloc_225_, 9, v_snapshotTasks_160_);
v___x_167_ = v_reuseFailAlloc_225_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_mctx_170_; lean_object* v_zetaDeltaFVarIds_171_; lean_object* v_postponed_172_; lean_object* v_diag_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_223_; 
v___x_168_ = lean_st_ref_put(v___y_148_, v___x_167_);
v___x_169_ = lean_st_ref_take(v___y_146_);
v_mctx_170_ = lean_ctor_get(v___x_169_, 0);
v_zetaDeltaFVarIds_171_ = lean_ctor_get(v___x_169_, 2);
v_postponed_172_ = lean_ctor_get(v___x_169_, 3);
v_diag_173_ = lean_ctor_get(v___x_169_, 4);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; 
v_unused_224_ = lean_ctor_get(v___x_169_, 1);
lean_dec(v_unused_224_);
v___x_175_ = v___x_169_;
v_isShared_176_ = v_isSharedCheck_223_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_diag_173_);
lean_inc(v_postponed_172_);
lean_inc(v_zetaDeltaFVarIds_171_);
lean_inc(v_mctx_170_);
lean_dec(v___x_169_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_223_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__5, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__5);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_mctx_170_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_177_);
lean_ctor_set(v_reuseFailAlloc_222_, 2, v_zetaDeltaFVarIds_171_);
lean_ctor_set(v_reuseFailAlloc_222_, 3, v_postponed_172_);
lean_ctor_set(v_reuseFailAlloc_222_, 4, v_diag_173_);
v___x_179_ = v_reuseFailAlloc_222_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_180_ = lean_st_ref_put(v___y_146_, v___x_179_);
v___x_181_ = ((lean_object*)(l_Lean_Elab_Tactic_classical___redArg___lam__3___closed__2));
v___x_182_ = 1;
v___x_183_ = lean_unsigned_to_nat(10u);
v___x_184_ = l_Lean_Meta_addInstance(v___x_181_, v___x_182_, v___x_183_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_r_185_; 
lean_dec_ref_known(v___x_184_, 1);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc_ref(v___y_145_);
lean_inc(v___y_144_);
lean_inc_ref(v___y_143_);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
v_r_185_ = lean_apply_9(v_t_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, lean_box(0));
if (lean_obj_tag(v_r_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_202_; 
v_a_186_ = lean_ctor_get(v_r_185_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_r_185_);
if (v_isSharedCheck_202_ == 0)
{
v___x_188_ = v_r_185_;
v_isShared_189_ = v_isSharedCheck_202_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v_r_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_202_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
lean_inc(v_a_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 1);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_201_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v___x_192_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_148_, v___x_150_, v___x_165_, v___y_146_, v___x_177_, v___x_191_);
lean_dec_ref(v___x_191_);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v___x_192_, 0);
lean_dec(v_unused_200_);
v___x_194_ = v___x_192_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_dec(v___x_192_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v_a_186_);
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_186_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_203_ = lean_ctor_get(v_r_185_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v_r_185_, 1);
v___x_204_ = lean_box(0);
v___x_205_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___lam__0(v___y_148_, v___x_150_, v___x_165_, v___y_146_, v___x_177_, v___x_204_);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v___x_205_, 0);
lean_dec(v_unused_213_);
v___x_207_ = v___x_205_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_dec(v___x_205_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set_tag(v___x_207_, 1);
lean_ctor_set(v___x_207_, 0, v_a_203_);
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_203_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec_ref(v_t_140_);
v_a_214_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_184_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_184_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___boxed(lean_object* v_t_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v_t_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___redArg(lean_object* v_stx_239_, lean_object* v_act_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_toCold_250_; lean_object* v_currRecDepth_251_; uint16_t v_optionFlags_252_; uint8_t v_suppressElabErrors_253_; uint8_t v_checkDeprecated_254_; uint8_t v_isRecordingDeps_255_; uint8_t v___y_257_; 
v_toCold_250_ = lean_ctor_get(v___y_247_, 0);
v_currRecDepth_251_ = lean_ctor_get(v___y_247_, 1);
v_optionFlags_252_ = lean_ctor_get_uint16(v___y_247_, sizeof(void*)*3);
v_suppressElabErrors_253_ = lean_ctor_get_uint8(v___y_247_, sizeof(void*)*3 + 2);
v_checkDeprecated_254_ = lean_ctor_get_uint8(v___y_247_, sizeof(void*)*3 + 3);
v_isRecordingDeps_255_ = lean_ctor_get_uint8(v___y_247_, sizeof(void*)*3 + 4);
if (v_suppressElabErrors_253_ == 0)
{
v___y_257_ = v_suppressElabErrors_253_;
goto v___jp_256_;
}
else
{
uint8_t v___x_260_; 
v___x_260_ = l_Lean_Syntax_hasMissing(v_stx_239_);
v___y_257_ = v___x_260_;
goto v___jp_256_;
}
v___jp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_inc(v_currRecDepth_251_);
lean_inc_ref(v_toCold_250_);
v___x_258_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_258_, 0, v_toCold_250_);
lean_ctor_set(v___x_258_, 1, v_currRecDepth_251_);
lean_ctor_set(v___x_258_, 2, v_stx_239_);
lean_ctor_set_uint16(v___x_258_, sizeof(void*)*3, v_optionFlags_252_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*3 + 2, v___y_257_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*3 + 3, v_checkDeprecated_254_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*3 + 4, v_isRecordingDeps_255_);
lean_inc(v___y_248_);
lean_inc(v___y_246_);
lean_inc_ref(v___y_245_);
lean_inc(v___y_244_);
lean_inc_ref(v___y_243_);
lean_inc(v___y_242_);
lean_inc_ref(v___y_241_);
v___x_259_ = lean_apply_9(v_act_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___x_258_, v___y_248_, lean_box(0));
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_stx_261_, lean_object* v_act_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___redArg(v_stx_261_, v_act_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(lean_object* v_act_273_, lean_object* v_snd_274_, lean_object* v_____r_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_inc(v_snd_274_);
v___x_285_ = lean_apply_1(v_act_273_, v_snd_274_);
v___x_286_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___redArg(v_snd_274_, v___x_285_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_act_287_, lean_object* v_snd_288_, lean_object* v_____r_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0(v_act_287_, v_snd_288_, v_____r_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(lean_object* v_val_300_, lean_object* v___x_301_, lean_object* v___f_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_tacSnap_x3f_316_; 
v_tacSnap_x3f_316_ = lean_ctor_get(v___y_305_, 6);
if (lean_obj_tag(v_tacSnap_x3f_316_) == 0)
{
goto v___jp_312_;
}
else
{
lean_object* v_val_317_; lean_object* v_old_x3f_318_; 
v_val_317_ = lean_ctor_get(v_tacSnap_x3f_316_, 0);
v_old_x3f_318_ = lean_ctor_get(v_val_317_, 0);
if (lean_obj_tag(v_old_x3f_318_) == 0)
{
goto v___jp_312_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v___x_301_);
lean_dec_ref(v_val_300_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_apply_10(v___f_302_, v___x_319_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, lean_box(0));
return v___x_320_;
}
}
v___jp_312_:
{
lean_object* v_val_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_val_313_ = lean_ctor_get(v_val_300_, 1);
lean_inc(v_val_313_);
lean_dec_ref(v_val_300_);
v___x_314_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_301_, v_val_313_);
v___x_315_ = lean_apply_10(v___f_302_, v___x_314_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, lean_box(0));
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_val_321_, lean_object* v___x_322_, lean_object* v___f_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1(v_val_321_, v___x_322_, v___f_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(lean_object* v_split_335_, lean_object* v_act_336_, lean_object* v_stx_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v___y_348_; lean_object* v___y_349_; uint8_t v___y_350_; uint8_t v___y_351_; lean_object* v___y_352_; lean_object* v___y_353_; uint8_t v___y_354_; uint8_t v___y_355_; uint8_t v___y_356_; lean_object* v___y_357_; uint8_t v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; uint8_t v___y_361_; lean_object* v___y_362_; uint8_t v___y_363_; uint8_t v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; uint8_t v___y_370_; lean_object* v___y_371_; uint8_t v___y_372_; uint8_t v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; uint8_t v___y_376_; uint8_t v___y_377_; uint8_t v___y_378_; lean_object* v___y_379_; uint8_t v___y_380_; lean_object* v_new_381_; lean_object* v___y_382_; lean_object* v___y_383_; uint8_t v___y_384_; lean_object* v___y_385_; uint8_t v___y_386_; lean_object* v___y_387_; uint8_t v___y_388_; lean_object* v___y_389_; lean_object* v___x_392_; lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v_declName_x3f_395_; lean_object* v_macroStack_396_; uint8_t v_mayPostpone_397_; uint8_t v_errToSorry_398_; lean_object* v_autoBoundImplicitContext_399_; lean_object* v_autoBoundImplicitForbidden_400_; lean_object* v_sectionVars_401_; lean_object* v_sectionFVars_402_; uint8_t v_implicitLambda_403_; uint8_t v_heedElabAsElim_404_; uint8_t v_isNoncomputableSection_405_; uint8_t v_isMetaSection_406_; uint8_t v_ignoreTCFailures_407_; uint8_t v_inPattern_408_; lean_object* v_tacSnap_x3f_409_; uint8_t v_saveRecAppSyntax_410_; uint8_t v_holesAsSyntheticOpaque_411_; lean_object* v_fixedTermElabs_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___y_416_; 
lean_inc_ref(v_split_335_);
v___x_392_ = lean_apply_1(v_split_335_, v_stx_337_);
v_fst_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_fst_393_);
v_snd_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc_n(v_snd_394_, 2);
lean_dec_ref(v___x_392_);
v_declName_x3f_395_ = lean_ctor_get(v___y_340_, 0);
v_macroStack_396_ = lean_ctor_get(v___y_340_, 1);
v_mayPostpone_397_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8);
v_errToSorry_398_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_399_ = lean_ctor_get(v___y_340_, 2);
v_autoBoundImplicitForbidden_400_ = lean_ctor_get(v___y_340_, 3);
v_sectionVars_401_ = lean_ctor_get(v___y_340_, 4);
v_sectionFVars_402_ = lean_ctor_get(v___y_340_, 5);
v_implicitLambda_403_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 2);
v_heedElabAsElim_404_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_405_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 4);
v_isMetaSection_406_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_407_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 6);
v_inPattern_408_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_409_ = lean_ctor_get(v___y_340_, 6);
v_saveRecAppSyntax_410_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_411_ = lean_ctor_get_uint8(v___y_340_, sizeof(void*)*8 + 9);
v_fixedTermElabs_412_ = lean_ctor_get(v___y_340_, 7);
lean_inc_ref(v_act_336_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 2);
lean_closure_set(v___f_413_, 0, v_act_336_);
lean_closure_set(v___f_413_, 1, v_snd_394_);
v___x_414_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_344_);
if (lean_obj_tag(v_tacSnap_x3f_409_) == 0)
{
lean_dec_ref(v___f_413_);
goto v___jp_437_;
}
else
{
lean_object* v_val_440_; lean_object* v_old_x3f_441_; 
v_val_440_ = lean_ctor_get(v_tacSnap_x3f_409_, 0);
v_old_x3f_441_ = lean_ctor_get(v_val_440_, 0);
if (lean_obj_tag(v_old_x3f_441_) == 1)
{
lean_object* v_val_442_; lean_object* v___x_443_; lean_object* v___f_444_; 
lean_dec(v_snd_394_);
lean_dec_ref(v_act_336_);
v_val_442_ = lean_ctor_get(v_old_x3f_441_, 0);
v___x_443_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___closed__0));
lean_inc(v_val_442_);
v___f_444_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__1___boxed), 12, 3);
lean_closure_set(v___f_444_, 0, v_val_442_);
lean_closure_set(v___f_444_, 1, v___x_443_);
lean_closure_set(v___f_444_, 2, v___f_413_);
v___y_416_ = v___f_444_;
goto v___jp_415_;
}
else
{
lean_dec_ref(v___f_413_);
goto v___jp_437_;
}
}
v___jp_347_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_inc_ref(v___y_353_);
lean_inc(v___y_359_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_360_);
lean_inc(v___y_349_);
lean_inc(v___y_357_);
lean_inc(v___y_365_);
v___x_367_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v___x_367_, 0, v___y_365_);
lean_ctor_set(v___x_367_, 1, v___y_357_);
lean_ctor_set(v___x_367_, 2, v___y_349_);
lean_ctor_set(v___x_367_, 3, v___y_360_);
lean_ctor_set(v___x_367_, 4, v___y_352_);
lean_ctor_set(v___x_367_, 5, v___y_359_);
lean_ctor_set(v___x_367_, 6, v___y_366_);
lean_ctor_set(v___x_367_, 7, v___y_353_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8, v___y_354_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 1, v___y_361_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 2, v___y_355_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 3, v___y_358_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 4, v___y_356_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 5, v___y_363_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 6, v___y_348_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 7, v___y_350_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 8, v___y_351_);
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*8 + 9, v___y_364_);
lean_inc(v___y_345_);
lean_inc_ref(v___y_344_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc(v___y_339_);
lean_inc_ref(v___y_338_);
v___x_368_ = lean_apply_9(v___y_362_, v___y_338_, v___y_339_, v___x_367_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, lean_box(0));
return v___x_368_;
}
v___jp_369_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___y_389_);
lean_ctor_set(v___x_390_, 1, v_new_381_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
v___y_348_ = v___y_370_;
v___y_349_ = v___y_371_;
v___y_350_ = v___y_372_;
v___y_351_ = v___y_373_;
v___y_352_ = v___y_374_;
v___y_353_ = v___y_375_;
v___y_354_ = v___y_376_;
v___y_355_ = v___y_377_;
v___y_356_ = v___y_378_;
v___y_357_ = v___y_379_;
v___y_358_ = v___y_380_;
v___y_359_ = v___y_382_;
v___y_360_ = v___y_383_;
v___y_361_ = v___y_384_;
v___y_362_ = v___y_385_;
v___y_363_ = v___y_386_;
v___y_364_ = v___y_388_;
v___y_365_ = v___y_387_;
v___y_366_ = v___x_391_;
goto v___jp_347_;
}
v___jp_415_:
{
if (lean_obj_tag(v_tacSnap_x3f_409_) == 0)
{
lean_dec_ref(v___x_414_);
lean_dec(v_fst_393_);
lean_dec_ref(v_split_335_);
v___y_348_ = v_ignoreTCFailures_407_;
v___y_349_ = v_autoBoundImplicitContext_399_;
v___y_350_ = v_inPattern_408_;
v___y_351_ = v_saveRecAppSyntax_410_;
v___y_352_ = v_sectionVars_401_;
v___y_353_ = v_fixedTermElabs_412_;
v___y_354_ = v_mayPostpone_397_;
v___y_355_ = v_implicitLambda_403_;
v___y_356_ = v_isNoncomputableSection_405_;
v___y_357_ = v_macroStack_396_;
v___y_358_ = v_heedElabAsElim_404_;
v___y_359_ = v_sectionFVars_402_;
v___y_360_ = v_autoBoundImplicitForbidden_400_;
v___y_361_ = v_errToSorry_398_;
v___y_362_ = v___y_416_;
v___y_363_ = v_isMetaSection_406_;
v___y_364_ = v_holesAsSyntheticOpaque_411_;
v___y_365_ = v_declName_x3f_395_;
v___y_366_ = v_tacSnap_x3f_409_;
goto v___jp_347_;
}
else
{
lean_object* v_val_417_; lean_object* v_old_x3f_418_; 
v_val_417_ = lean_ctor_get(v_tacSnap_x3f_409_, 0);
v_old_x3f_418_ = lean_ctor_get(v_val_417_, 0);
if (lean_obj_tag(v_old_x3f_418_) == 0)
{
lean_object* v_new_419_; 
lean_dec_ref(v___x_414_);
lean_dec(v_fst_393_);
lean_dec_ref(v_split_335_);
v_new_419_ = lean_ctor_get(v_val_417_, 1);
lean_inc(v_new_419_);
v___y_370_ = v_ignoreTCFailures_407_;
v___y_371_ = v_autoBoundImplicitContext_399_;
v___y_372_ = v_inPattern_408_;
v___y_373_ = v_saveRecAppSyntax_410_;
v___y_374_ = v_sectionVars_401_;
v___y_375_ = v_fixedTermElabs_412_;
v___y_376_ = v_mayPostpone_397_;
v___y_377_ = v_implicitLambda_403_;
v___y_378_ = v_isNoncomputableSection_405_;
v___y_379_ = v_macroStack_396_;
v___y_380_ = v_heedElabAsElim_404_;
v_new_381_ = v_new_419_;
v___y_382_ = v_sectionFVars_402_;
v___y_383_ = v_autoBoundImplicitForbidden_400_;
v___y_384_ = v_errToSorry_398_;
v___y_385_ = v___y_416_;
v___y_386_ = v_isMetaSection_406_;
v___y_387_ = v_declName_x3f_395_;
v___y_388_ = v_holesAsSyntheticOpaque_411_;
v___y_389_ = v_old_x3f_418_;
goto v___jp_369_;
}
else
{
lean_object* v_val_420_; lean_object* v_new_421_; lean_object* v_stx_422_; lean_object* v_val_423_; lean_object* v___x_424_; lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_436_; 
v_val_420_ = lean_ctor_get(v_old_x3f_418_, 0);
v_new_421_ = lean_ctor_get(v_val_417_, 1);
v_stx_422_ = lean_ctor_get(v_val_420_, 0);
v_val_423_ = lean_ctor_get(v_val_420_, 1);
lean_inc(v_stx_422_);
v___x_424_ = lean_apply_1(v_split_335_, v_stx_422_);
v_fst_425_ = lean_ctor_get(v___x_424_, 0);
v_snd_426_ = lean_ctor_get(v___x_424_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_436_ == 0)
{
v___x_428_ = v___x_424_;
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snd_426_);
lean_inc(v_fst_425_);
lean_dec(v___x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_436_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v___x_430_; 
v___x_430_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v___x_414_, v_fst_393_, v_fst_425_);
lean_dec_ref(v___x_414_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_del_object(v___x_428_);
lean_dec(v_snd_426_);
v___x_431_ = lean_box(0);
lean_inc(v_new_421_);
v___y_370_ = v_ignoreTCFailures_407_;
v___y_371_ = v_autoBoundImplicitContext_399_;
v___y_372_ = v_inPattern_408_;
v___y_373_ = v_saveRecAppSyntax_410_;
v___y_374_ = v_sectionVars_401_;
v___y_375_ = v_fixedTermElabs_412_;
v___y_376_ = v_mayPostpone_397_;
v___y_377_ = v_implicitLambda_403_;
v___y_378_ = v_isNoncomputableSection_405_;
v___y_379_ = v_macroStack_396_;
v___y_380_ = v_heedElabAsElim_404_;
v_new_381_ = v_new_421_;
v___y_382_ = v_sectionFVars_402_;
v___y_383_ = v_autoBoundImplicitForbidden_400_;
v___y_384_ = v_errToSorry_398_;
v___y_385_ = v___y_416_;
v___y_386_ = v_isMetaSection_406_;
v___y_387_ = v_declName_x3f_395_;
v___y_388_ = v_holesAsSyntheticOpaque_411_;
v___y_389_ = v___x_431_;
goto v___jp_369_;
}
else
{
lean_object* v___x_433_; 
lean_inc(v_val_423_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v_val_423_);
lean_ctor_set(v___x_428_, 0, v_snd_426_);
v___x_433_ = v___x_428_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_snd_426_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_val_423_);
v___x_433_ = v_reuseFailAlloc_435_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; 
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_inc(v_new_421_);
v___y_370_ = v_ignoreTCFailures_407_;
v___y_371_ = v_autoBoundImplicitContext_399_;
v___y_372_ = v_inPattern_408_;
v___y_373_ = v_saveRecAppSyntax_410_;
v___y_374_ = v_sectionVars_401_;
v___y_375_ = v_fixedTermElabs_412_;
v___y_376_ = v_mayPostpone_397_;
v___y_377_ = v_implicitLambda_403_;
v___y_378_ = v_isNoncomputableSection_405_;
v___y_379_ = v_macroStack_396_;
v___y_380_ = v_heedElabAsElim_404_;
v_new_381_ = v_new_421_;
v___y_382_ = v_sectionFVars_402_;
v___y_383_ = v_autoBoundImplicitForbidden_400_;
v___y_384_ = v_errToSorry_398_;
v___y_385_ = v___y_416_;
v___y_386_ = v_isMetaSection_406_;
v___y_387_ = v_declName_x3f_395_;
v___y_388_ = v_holesAsSyntheticOpaque_411_;
v___y_389_ = v___x_434_;
goto v___jp_369_;
}
}
}
}
}
}
v___jp_437_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___lam__0___boxed), 12, 3);
lean_closure_set(v___x_439_, 0, v_act_336_);
lean_closure_set(v___x_439_, 1, v_snd_394_);
lean_closure_set(v___x_439_, 2, v___x_438_);
v___y_416_ = v___x_439_;
goto v___jp_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg___boxed(lean_object* v_split_445_, lean_object* v_act_446_, lean_object* v_stx_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_445_, v_act_446_, v_stx_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(lean_object* v_argIdx_461_, lean_object* v_stx_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_463_ = l_Lean_Syntax_getArgs(v_stx_462_);
v___x_464_ = lean_unsigned_to_nat(0u);
lean_inc(v_argIdx_461_);
v___x_465_ = l_Array_toSubarray___redArg(v___x_463_, v___x_464_, v_argIdx_461_);
v___x_466_ = l_Subarray_copy___redArg(v___x_465_);
v___x_467_ = ((lean_object*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___closed__1));
v___x_468_ = lean_box(2);
v___x_469_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_467_);
lean_ctor_set(v___x_469_, 2, v___x_466_);
v___x_470_ = l_Lean_Syntax_getArg(v_stx_462_, v_argIdx_461_);
lean_dec(v_argIdx_461_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed(lean_object* v_argIdx_472_, lean_object* v_stx_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0(v_argIdx_472_, v_stx_473_);
lean_dec(v_stx_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(lean_object* v_argIdx_475_, lean_object* v_act_476_, lean_object* v_stx_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v___f_487_; lean_object* v___x_488_; 
v___f_487_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_487_, 0, v_argIdx_475_);
v___x_488_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v___f_487_, v_act_476_, v_stx_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg___boxed(lean_object* v_argIdx_489_, lean_object* v_act_490_, lean_object* v_stx_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_489_, v_act_490_, v_stx_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(lean_object* v_00_u03b1_502_, lean_object* v_argIdx_503_, lean_object* v_act_504_, lean_object* v_stx_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___redArg(v_argIdx_503_, v_act_504_, v_stx_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed(lean_object* v_00_u03b1_516_, lean_object* v_argIdx_517_, lean_object* v_act_518_, lean_object* v_stx_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0(v_00_u03b1_516_, v_argIdx_517_, v_act_518_, v_stx_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___redArg(lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; lean_object* v_env_535_; lean_object* v___x_536_; lean_object* v_toCold_537_; lean_object* v_mctx_538_; lean_object* v_currNamespace_539_; lean_object* v_openDecls_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_ngen_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_534_ = lean_st_ref_get(v___y_532_);
v_env_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc_ref(v_env_535_);
lean_dec(v___x_534_);
v___x_536_ = lean_st_ref_get(v___y_530_);
v_toCold_537_ = lean_ctor_get(v___y_531_, 0);
v_mctx_538_ = lean_ctor_get(v___x_536_, 0);
lean_inc_ref(v_mctx_538_);
lean_dec(v___x_536_);
v_currNamespace_539_ = lean_ctor_get(v_toCold_537_, 4);
v_openDecls_540_ = lean_ctor_get(v_toCold_537_, 5);
v___x_541_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_531_);
v___x_542_ = lean_st_ref_get(v___y_532_);
v_ngen_543_ = lean_ctor_get(v___x_542_, 2);
lean_inc_ref(v_ngen_543_);
lean_dec(v___x_542_);
v___x_544_ = lean_box(0);
v___x_545_ = l_Lean_instInhabitedFileMap_default;
lean_inc(v_openDecls_540_);
lean_inc(v_currNamespace_539_);
v___x_546_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_546_, 0, v_env_535_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
lean_ctor_set(v___x_546_, 3, v_mctx_538_);
lean_ctor_set(v___x_546_, 4, v___x_541_);
lean_ctor_set(v___x_546_, 5, v_currNamespace_539_);
lean_ctor_set(v___x_546_, 6, v_openDecls_540_);
lean_ctor_set(v___x_546_, 7, v_ngen_543_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___redArg(v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; lean_object* v_toCold_563_; lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_588_; 
v___x_562_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___redArg(v___y_558_, v___y_559_, v___y_560_);
v_toCold_563_ = lean_ctor_get(v___y_559_, 0);
v_a_564_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_588_ == 0)
{
v___x_566_ = v___x_562_;
v_isShared_567_ = v_isSharedCheck_588_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_562_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_588_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_fileMap_568_; lean_object* v_env_569_; lean_object* v_mctx_570_; lean_object* v_options_571_; lean_object* v_currNamespace_572_; lean_object* v_openDecls_573_; lean_object* v_ngen_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_585_; 
v_fileMap_568_ = lean_ctor_get(v_toCold_563_, 1);
v_env_569_ = lean_ctor_get(v_a_564_, 0);
v_mctx_570_ = lean_ctor_get(v_a_564_, 3);
v_options_571_ = lean_ctor_get(v_a_564_, 4);
v_currNamespace_572_ = lean_ctor_get(v_a_564_, 5);
v_openDecls_573_ = lean_ctor_get(v_a_564_, 6);
v_ngen_574_ = lean_ctor_get(v_a_564_, 7);
v_isSharedCheck_585_ = !lean_is_exclusive(v_a_564_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; lean_object* v_unused_587_; 
v_unused_586_ = lean_ctor_get(v_a_564_, 2);
lean_dec(v_unused_586_);
v_unused_587_ = lean_ctor_get(v_a_564_, 1);
lean_dec(v_unused_587_);
v___x_576_ = v_a_564_;
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_ngen_574_);
lean_inc(v_openDecls_573_);
lean_inc(v_currNamespace_572_);
lean_inc(v_options_571_);
lean_inc(v_mctx_570_);
lean_inc(v_env_569_);
lean_dec(v_a_564_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
lean_inc_ref(v_fileMap_568_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 2, v_fileMap_568_);
lean_ctor_set(v___x_576_, 1, v___x_578_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_env_569_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_fileMap_568_);
lean_ctor_set(v_reuseFailAlloc_584_, 3, v_mctx_570_);
lean_ctor_set(v_reuseFailAlloc_584_, 4, v_options_571_);
lean_ctor_set(v_reuseFailAlloc_584_, 5, v_currNamespace_572_);
lean_ctor_set(v_reuseFailAlloc_584_, 6, v_openDecls_573_);
lean_ctor_set(v_reuseFailAlloc_584_, 7, v_ngen_574_);
v___x_580_ = v_reuseFailAlloc_584_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_580_);
v___x_582_ = v___x_566_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2___boxed(lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_618_; 
v___x_608_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2(v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_618_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_618_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v_a_609_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0___boxed(lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___lam__0(v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_628_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(32u);
v___x_630_ = lean_mk_empty_array_with_capacity(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_632_ = ((size_t)5ULL);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_unsigned_to_nat(32u);
v___x_635_ = lean_mk_empty_array_with_capacity(v___x_634_);
v___x_636_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_637_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
lean_ctor_set(v___x_637_, 2, v___x_633_);
lean_ctor_set(v___x_637_, 3, v___x_633_);
lean_ctor_set_usize(v___x_637_, 4, v___x_632_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg(lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; lean_object* v_infoState_641_; lean_object* v_trees_642_; lean_object* v___x_643_; lean_object* v_infoState_644_; lean_object* v_env_645_; lean_object* v_nextMacroScope_646_; lean_object* v_ngen_647_; lean_object* v_auxDeclNGen_648_; lean_object* v_traceState_649_; lean_object* v_cache_650_; lean_object* v_recordedDeps_651_; lean_object* v_messages_652_; lean_object* v_snapshotTasks_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_674_; 
v___x_640_ = lean_st_ref_get(v___y_638_);
v_infoState_641_ = lean_ctor_get(v___x_640_, 8);
lean_inc_ref(v_infoState_641_);
lean_dec(v___x_640_);
v_trees_642_ = lean_ctor_get(v_infoState_641_, 2);
lean_inc_ref(v_trees_642_);
lean_dec_ref(v_infoState_641_);
v___x_643_ = lean_st_ref_take(v___y_638_);
v_infoState_644_ = lean_ctor_get(v___x_643_, 8);
v_env_645_ = lean_ctor_get(v___x_643_, 0);
v_nextMacroScope_646_ = lean_ctor_get(v___x_643_, 1);
v_ngen_647_ = lean_ctor_get(v___x_643_, 2);
v_auxDeclNGen_648_ = lean_ctor_get(v___x_643_, 3);
v_traceState_649_ = lean_ctor_get(v___x_643_, 4);
v_cache_650_ = lean_ctor_get(v___x_643_, 5);
v_recordedDeps_651_ = lean_ctor_get(v___x_643_, 6);
v_messages_652_ = lean_ctor_get(v___x_643_, 7);
v_snapshotTasks_653_ = lean_ctor_get(v___x_643_, 9);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_674_ == 0)
{
v___x_655_ = v___x_643_;
v_isShared_656_ = v_isSharedCheck_674_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_snapshotTasks_653_);
lean_inc(v_infoState_644_);
lean_inc(v_messages_652_);
lean_inc(v_recordedDeps_651_);
lean_inc(v_cache_650_);
lean_inc(v_traceState_649_);
lean_inc(v_auxDeclNGen_648_);
lean_inc(v_ngen_647_);
lean_inc(v_nextMacroScope_646_);
lean_inc(v_env_645_);
lean_dec(v___x_643_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_674_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
uint8_t v_enabled_657_; lean_object* v_assignment_658_; lean_object* v_lazyAssignment_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_672_; 
v_enabled_657_ = lean_ctor_get_uint8(v_infoState_644_, sizeof(void*)*3);
v_assignment_658_ = lean_ctor_get(v_infoState_644_, 0);
v_lazyAssignment_659_ = lean_ctor_get(v_infoState_644_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_infoState_644_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v_infoState_644_, 2);
lean_dec(v_unused_673_);
v___x_661_ = v_infoState_644_;
v_isShared_662_ = v_isSharedCheck_672_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_lazyAssignment_659_);
lean_inc(v_assignment_658_);
lean_dec(v_infoState_644_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_672_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_665_; 
v___x_663_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___closed__1);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 2, v___x_663_);
v___x_665_ = v___x_661_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_assignment_658_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_lazyAssignment_659_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v___x_663_);
lean_ctor_set_uint8(v_reuseFailAlloc_671_, sizeof(void*)*3, v_enabled_657_);
v___x_665_ = v_reuseFailAlloc_671_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 8, v___x_665_);
v___x_667_ = v___x_655_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_env_645_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_nextMacroScope_646_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_ngen_647_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_auxDeclNGen_648_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_traceState_649_);
lean_ctor_set(v_reuseFailAlloc_670_, 5, v_cache_650_);
lean_ctor_set(v_reuseFailAlloc_670_, 6, v_recordedDeps_651_);
lean_ctor_set(v_reuseFailAlloc_670_, 7, v_messages_652_);
lean_ctor_set(v_reuseFailAlloc_670_, 8, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_670_, 9, v_snapshotTasks_653_);
v___x_667_ = v_reuseFailAlloc_670_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_st_ref_put(v___y_638_, v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v_trees_642_);
return v___x_669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg(v___y_675_);
lean_dec(v___y_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__10(lean_object* v___x_678_, lean_object* v_ctx_x3f_679_, size_t v_sz_680_, size_t v_i_681_, lean_object* v_bs_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = lean_usize_dec_lt(v_i_681_, v_sz_680_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_dec_ref(v_ctx_x3f_679_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_bs_682_);
return v___x_693_;
}
else
{
lean_object* v_assignment_694_; lean_object* v_v_695_; lean_object* v___x_696_; lean_object* v_bs_x27_697_; lean_object* v_a_699_; lean_object* v_tree_704_; lean_object* v___x_705_; 
v_assignment_694_ = lean_ctor_get(v___x_678_, 0);
v_v_695_ = lean_array_uget(v_bs_682_, v_i_681_);
v___x_696_ = lean_unsigned_to_nat(0u);
v_bs_x27_697_ = lean_array_uset(v_bs_682_, v_i_681_, v___x_696_);
v_tree_704_ = l_Lean_Elab_InfoTree_substitute(v_v_695_, v_assignment_694_);
lean_inc_ref(v_ctx_x3f_679_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc_ref(v___y_685_);
lean_inc(v___y_684_);
lean_inc_ref(v___y_683_);
v___x_705_ = lean_apply_9(v_ctx_x3f_679_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, lean_box(0));
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
if (lean_obj_tag(v_a_706_) == 0)
{
v_a_699_ = v_tree_704_;
goto v___jp_698_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_708_; 
v_val_707_ = lean_ctor_get(v_a_706_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v_a_706_, 1);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_val_707_);
lean_ctor_set(v___x_708_, 1, v_tree_704_);
v_a_699_ = v___x_708_;
goto v___jp_698_;
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_tree_704_);
lean_dec_ref(v_bs_x27_697_);
lean_dec_ref(v_ctx_x3f_679_);
v_a_709_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_705_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_705_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
v___jp_698_:
{
size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; 
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_add(v_i_681_, v___x_700_);
v___x_702_ = lean_array_uset(v_bs_x27_697_, v_i_681_, v_a_699_);
v_i_681_ = v___x_701_;
v_bs_682_ = v___x_702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__10___boxed(lean_object* v___x_717_, lean_object* v_ctx_x3f_718_, lean_object* v_sz_719_, lean_object* v_i_720_, lean_object* v_bs_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
size_t v_sz_boxed_731_; size_t v_i_boxed_732_; lean_object* v_res_733_; 
v_sz_boxed_731_ = lean_unbox_usize(v_sz_719_);
lean_dec(v_sz_719_);
v_i_boxed_732_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__10(v___x_717_, v_ctx_x3f_718_, v_sz_boxed_731_, v_i_boxed_732_, v_bs_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec_ref(v___x_717_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9(lean_object* v___x_734_, lean_object* v_ctx_x3f_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
if (lean_obj_tag(v_x_736_) == 0)
{
lean_object* v_cs_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_772_; 
v_cs_746_ = lean_ctor_get(v_x_736_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_736_);
if (v_isSharedCheck_772_ == 0)
{
v___x_748_ = v_x_736_;
v_isShared_749_ = v_isSharedCheck_772_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_cs_746_);
lean_dec(v_x_736_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_772_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
size_t v_sz_750_; size_t v___x_751_; lean_object* v___x_752_; 
v_sz_750_ = lean_array_size(v_cs_746_);
v___x_751_ = ((size_t)0ULL);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9_spec__12(v___x_734_, v_ctx_x3f_735_, v_sz_750_, v___x_751_, v_cs_746_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_763_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_763_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_763_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_763_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v_a_753_);
v___x_758_ = v___x_748_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_758_);
v___x_760_ = v___x_755_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_del_object(v___x_748_);
v_a_764_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_752_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_752_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
else
{
lean_object* v_vs_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_799_; 
v_vs_773_ = lean_ctor_get(v_x_736_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_736_);
if (v_isSharedCheck_799_ == 0)
{
v___x_775_ = v_x_736_;
v_isShared_776_ = v_isSharedCheck_799_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_vs_773_);
lean_dec(v_x_736_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_799_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
size_t v_sz_777_; size_t v___x_778_; lean_object* v___x_779_; 
v_sz_777_ = lean_array_size(v_vs_773_);
v___x_778_ = ((size_t)0ULL);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__10(v___x_734_, v_ctx_x3f_735_, v_sz_777_, v___x_778_, v_vs_773_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_790_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_790_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v_a_780_);
v___x_785_ = v___x_775_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_785_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_del_object(v___x_775_);
v_a_791_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_779_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_779_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9_spec__12(lean_object* v___x_800_, lean_object* v_ctx_x3f_801_, size_t v_sz_802_, size_t v_i_803_, lean_object* v_bs_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = lean_usize_dec_lt(v_i_803_, v_sz_802_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_dec_ref(v_ctx_x3f_801_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v_bs_804_);
return v___x_815_;
}
else
{
lean_object* v_v_816_; lean_object* v___x_817_; lean_object* v_bs_x27_818_; lean_object* v___x_819_; 
v_v_816_ = lean_array_uget(v_bs_804_, v_i_803_);
v___x_817_ = lean_unsigned_to_nat(0u);
v_bs_x27_818_ = lean_array_uset(v_bs_804_, v_i_803_, v___x_817_);
lean_inc_ref(v_ctx_x3f_801_);
v___x_819_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9(v___x_800_, v_ctx_x3f_801_, v_v_816_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_803_, v___x_821_);
v___x_823_ = lean_array_uset(v_bs_x27_818_, v_i_803_, v_a_820_);
v_i_803_ = v___x_822_;
v_bs_804_ = v___x_823_;
goto _start;
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v_bs_x27_818_);
lean_dec_ref(v_ctx_x3f_801_);
v_a_825_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_819_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_819_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9_spec__12___boxed(lean_object* v___x_833_, lean_object* v_ctx_x3f_834_, lean_object* v_sz_835_, lean_object* v_i_836_, lean_object* v_bs_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
size_t v_sz_boxed_847_; size_t v_i_boxed_848_; lean_object* v_res_849_; 
v_sz_boxed_847_ = lean_unbox_usize(v_sz_835_);
lean_dec(v_sz_835_);
v_i_boxed_848_ = lean_unbox_usize(v_i_836_);
lean_dec(v_i_836_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9_spec__12(v___x_833_, v_ctx_x3f_834_, v_sz_boxed_847_, v_i_boxed_848_, v_bs_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec_ref(v___x_833_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9___boxed(lean_object* v___x_850_, lean_object* v_ctx_x3f_851_, lean_object* v_x_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9(v___x_850_, v_ctx_x3f_851_, v_x_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec_ref(v___x_850_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(lean_object* v___x_863_, lean_object* v_ctx_x3f_864_, lean_object* v_t_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_root_875_; lean_object* v_tail_876_; lean_object* v_size_877_; size_t v_shift_878_; lean_object* v_tailOff_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_915_; 
v_root_875_ = lean_ctor_get(v_t_865_, 0);
v_tail_876_ = lean_ctor_get(v_t_865_, 1);
v_size_877_ = lean_ctor_get(v_t_865_, 2);
v_shift_878_ = lean_ctor_get_usize(v_t_865_, 4);
v_tailOff_879_ = lean_ctor_get(v_t_865_, 3);
v_isSharedCheck_915_ = !lean_is_exclusive(v_t_865_);
if (v_isSharedCheck_915_ == 0)
{
v___x_881_ = v_t_865_;
v_isShared_882_ = v_isSharedCheck_915_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_tailOff_879_);
lean_inc(v_size_877_);
lean_inc(v_tail_876_);
lean_inc(v_root_875_);
lean_dec(v_t_865_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_915_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; 
lean_inc_ref(v_ctx_x3f_864_);
v___x_883_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__9(v___x_863_, v_ctx_x3f_864_, v_root_875_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; size_t v_sz_885_; size_t v___x_886_; lean_object* v___x_887_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v_sz_885_ = lean_array_size(v_tail_876_);
v___x_886_ = ((size_t)0ULL);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7_spec__10(v___x_863_, v_ctx_x3f_864_, v_sz_885_, v___x_886_, v_tail_876_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_898_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_898_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_898_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_898_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_a_888_);
lean_ctor_set(v___x_881_, 0, v_a_884_);
v___x_893_ = v___x_881_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_884_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_888_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_size_877_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_tailOff_879_);
lean_ctor_set_usize(v_reuseFailAlloc_897_, 4, v_shift_878_);
v___x_893_ = v_reuseFailAlloc_897_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_893_);
v___x_895_ = v___x_890_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec(v_a_884_);
lean_del_object(v___x_881_);
lean_dec(v_tailOff_879_);
lean_dec(v_size_877_);
v_a_899_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_887_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_887_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_del_object(v___x_881_);
lean_dec(v_tailOff_879_);
lean_dec(v_size_877_);
lean_dec_ref(v_tail_876_);
lean_dec_ref(v_ctx_x3f_864_);
v_a_907_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_883_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_883_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7___boxed(lean_object* v___x_916_, lean_object* v_ctx_x3f_917_, lean_object* v_t_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v___x_916_, v_ctx_x3f_917_, v_t_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec_ref(v___x_916_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(lean_object* v___y_929_, lean_object* v_ctx_x3f_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v_a_938_, lean_object* v_a_x3f_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_infoState_942_; lean_object* v_trees_943_; lean_object* v___x_944_; 
v___x_941_ = lean_st_ref_get(v___y_929_);
v_infoState_942_ = lean_ctor_get(v___x_941_, 8);
lean_inc_ref(v_infoState_942_);
lean_dec(v___x_941_);
v_trees_943_ = lean_ctor_get(v_infoState_942_, 2);
lean_inc_ref(v_trees_943_);
v___x_944_ = l_Lean_PersistentArray_mapM___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__7(v_infoState_942_, v_ctx_x3f_930_, v_trees_943_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_929_);
lean_dec_ref(v_infoState_942_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_984_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_984_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_984_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_984_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v_infoState_950_; lean_object* v_env_951_; lean_object* v_nextMacroScope_952_; lean_object* v_ngen_953_; lean_object* v_auxDeclNGen_954_; lean_object* v_traceState_955_; lean_object* v_cache_956_; lean_object* v_recordedDeps_957_; lean_object* v_messages_958_; lean_object* v_snapshotTasks_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_983_; 
v___x_949_ = lean_st_ref_take(v___y_929_);
v_infoState_950_ = lean_ctor_get(v___x_949_, 8);
v_env_951_ = lean_ctor_get(v___x_949_, 0);
v_nextMacroScope_952_ = lean_ctor_get(v___x_949_, 1);
v_ngen_953_ = lean_ctor_get(v___x_949_, 2);
v_auxDeclNGen_954_ = lean_ctor_get(v___x_949_, 3);
v_traceState_955_ = lean_ctor_get(v___x_949_, 4);
v_cache_956_ = lean_ctor_get(v___x_949_, 5);
v_recordedDeps_957_ = lean_ctor_get(v___x_949_, 6);
v_messages_958_ = lean_ctor_get(v___x_949_, 7);
v_snapshotTasks_959_ = lean_ctor_get(v___x_949_, 9);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_983_ == 0)
{
v___x_961_ = v___x_949_;
v_isShared_962_ = v_isSharedCheck_983_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_snapshotTasks_959_);
lean_inc(v_infoState_950_);
lean_inc(v_messages_958_);
lean_inc(v_recordedDeps_957_);
lean_inc(v_cache_956_);
lean_inc(v_traceState_955_);
lean_inc(v_auxDeclNGen_954_);
lean_inc(v_ngen_953_);
lean_inc(v_nextMacroScope_952_);
lean_inc(v_env_951_);
lean_dec(v___x_949_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_983_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v_enabled_963_; lean_object* v_assignment_964_; lean_object* v_lazyAssignment_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_981_; 
v_enabled_963_ = lean_ctor_get_uint8(v_infoState_950_, sizeof(void*)*3);
v_assignment_964_ = lean_ctor_get(v_infoState_950_, 0);
v_lazyAssignment_965_ = lean_ctor_get(v_infoState_950_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_infoState_950_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v_infoState_950_, 2);
lean_dec(v_unused_982_);
v___x_967_ = v_infoState_950_;
v_isShared_968_ = v_isSharedCheck_981_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_lazyAssignment_965_);
lean_inc(v_assignment_964_);
lean_dec(v_infoState_950_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_981_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_969_ = lean_box(0);
v___x_970_ = l_Lean_PersistentArray_append___redArg(v_a_938_, v_a_945_);
lean_dec(v_a_945_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 2, v___x_970_);
v___x_972_ = v___x_967_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_assignment_964_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_lazyAssignment_965_);
lean_ctor_set(v_reuseFailAlloc_980_, 2, v___x_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_980_, sizeof(void*)*3, v_enabled_963_);
v___x_972_ = v_reuseFailAlloc_980_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_974_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 8, v___x_972_);
v___x_974_ = v___x_961_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_env_951_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_nextMacroScope_952_);
lean_ctor_set(v_reuseFailAlloc_979_, 2, v_ngen_953_);
lean_ctor_set(v_reuseFailAlloc_979_, 3, v_auxDeclNGen_954_);
lean_ctor_set(v_reuseFailAlloc_979_, 4, v_traceState_955_);
lean_ctor_set(v_reuseFailAlloc_979_, 5, v_cache_956_);
lean_ctor_set(v_reuseFailAlloc_979_, 6, v_recordedDeps_957_);
lean_ctor_set(v_reuseFailAlloc_979_, 7, v_messages_958_);
lean_ctor_set(v_reuseFailAlloc_979_, 8, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_979_, 9, v_snapshotTasks_959_);
v___x_974_ = v_reuseFailAlloc_979_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_975_ = lean_st_ref_put(v___y_929_, v___x_974_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_969_);
v___x_977_ = v___x_947_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_969_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_a_938_);
v_a_985_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_944_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_944_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0___boxed(lean_object* v___y_993_, lean_object* v_ctx_x3f_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v_a_1002_, lean_object* v_a_x3f_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_993_, v_ctx_x3f_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v_a_1002_, v_a_x3f_1003_);
lean_dec(v_a_x3f_1003_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_993_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(lean_object* v_x_1006_, lean_object* v_ctx_x3f_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___x_1017_; lean_object* v_infoState_1018_; uint8_t v_enabled_1019_; 
v___x_1017_ = lean_st_ref_get(v___y_1015_);
v_infoState_1018_ = lean_ctor_get(v___x_1017_, 8);
lean_inc_ref(v_infoState_1018_);
lean_dec(v___x_1017_);
v_enabled_1019_ = lean_ctor_get_uint8(v_infoState_1018_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1018_);
if (v_enabled_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref(v_ctx_x3f_1007_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
v___x_1020_ = lean_apply_9(v_x_1006_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, lean_box(0));
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v_r_1023_; 
v___x_1021_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg(v___y_1015_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
v_r_1023_ = lean_apply_9(v_x_1006_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, lean_box(0));
if (lean_obj_tag(v_r_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1048_; 
v_a_1024_ = lean_ctor_get(v_r_1023_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_r_1023_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1026_ = v_r_1023_;
v_isShared_1027_ = v_isSharedCheck_1048_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v_r_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1048_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
lean_inc(v_a_1024_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 1);
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
v___x_1030_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1015_, v_ctx_x3f_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v_a_1022_, v___x_1029_);
lean_dec_ref(v___x_1029_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v___x_1030_, 0);
lean_dec(v_unused_1038_);
v___x_1032_ = v___x_1030_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_dec(v___x_1030_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v_a_1024_);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1024_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_a_1024_);
v_a_1039_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1030_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1030_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_a_1049_ = lean_ctor_get(v_r_1023_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v_r_1023_, 1);
v___x_1050_ = lean_box(0);
v___x_1051_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___lam__0(v___y_1015_, v_ctx_x3f_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v_a_1022_, v___x_1050_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v___x_1051_, 0);
lean_dec(v_unused_1059_);
v___x_1053_ = v___x_1051_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v___x_1051_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 1);
lean_ctor_set(v___x_1053_, 0, v_a_1049_);
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1049_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_dec(v_a_1049_);
v_a_1060_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1051_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1051_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg___boxed(lean_object* v_x_1068_, lean_object* v_ctx_x3f_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1068_, v_ctx_x3f_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; 
v___f_1091_ = ((lean_object*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___closed__0));
v___x_1092_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1081_, v___f_1091_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg___boxed(lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(lean_object* v_00_u03b1_1104_, lean_object* v_x_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___redArg(v_x_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_x_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1(v_00_u03b1_1116_, v_x_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical(lean_object* v_stx_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Tactic_evalClassical___closed__0));
v___x_1141_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0___boxed), 13, 4);
lean_closure_set(v___x_1141_, 0, lean_box(0));
lean_closure_set(v___x_1141_, 1, v___x_1139_);
lean_closure_set(v___x_1141_, 2, v___x_1140_);
lean_closure_set(v___x_1141_, 3, v_stx_1129_);
v___x_1142_ = lean_alloc_closure((void*)(l_Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1___boxed), 11, 2);
lean_closure_set(v___x_1142_, 0, lean_box(0));
lean_closure_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v___x_1142_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalClassical___boxed(lean_object* v_stx_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Elab_Tactic_evalClassical(v_stx_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec_ref(v_a_1145_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(lean_object* v_00_u03b1_1155_, lean_object* v_t_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg(v_t_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___boxed(lean_object* v_00_u03b1_1167_, lean_object* v_t_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2(v_00_u03b1_1167_, v_t_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1179_, lean_object* v_stx_1180_, lean_object* v_act_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___redArg(v_stx_1180_, v_act_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_stx_1193_, lean_object* v_act_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Elab_Term_withReuseContext___at___00Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0_spec__1(v_00_u03b1_1192_, v_stx_1193_, v_act_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(lean_object* v_00_u03b1_1205_, lean_object* v_split_1206_, lean_object* v_act_1207_, lean_object* v_stx_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___redArg(v_split_1206_, v_act_1207_, v_stx_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_split_1220_, lean_object* v_act_1221_, lean_object* v_stx_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Elab_Term_withNarrowedTacticReuse___at___00Lean_Elab_Term_withNarrowedArgTacticReuse___at___00Lean_Elab_Tactic_evalClassical_spec__0_spec__0(v_00_u03b1_1219_, v_split_1220_, v_act_1221_, v_stx_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4(lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___redArg(v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4___boxed(lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__2_spec__4(v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6(lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___redArg(v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6___boxed(lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3_spec__6(v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(lean_object* v_00_u03b1_1273_, lean_object* v_x_1274_, lean_object* v_ctx_x3f_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___redArg(v_x_1274_, v_ctx_x3f_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1286_, lean_object* v_x_1287_, lean_object* v_ctx_x3f_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___00Lean_Elab_withSaveInfoContext___at___00Lean_Elab_Tactic_evalClassical_spec__1_spec__3(v_00_u03b1_1286_, v_x_1287_, v_ctx_x3f_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5___redArg(){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5___redArg___boxed(lean_object* v___dummy_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5___redArg();
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2_spec__5(lean_object* v_00_u03b2_1305_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_obj_once(&l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2, &l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_classical___at___00Lean_Elab_Tactic_evalClassical_spec__2___redArg___closed__2);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1(){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1324_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__4));
v___x_1326_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1327_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalClassical___boxed), 10, 0);
v___x_1328_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1324_, v___x_1325_, v___x_1326_, v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___boxed(lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1();
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3(){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__1___closed__7));
v___x_1333_ = l_Lean_Elab_addBuiltinIncrementalElab(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3___boxed(lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_Elab_Tactic_Classical_0__Lean_Elab_Tactic_evalClassical___regBuiltin_Lean_Elab_Tactic_evalClassical__3();
return v_res_1335_;
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
