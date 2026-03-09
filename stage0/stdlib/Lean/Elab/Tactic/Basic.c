// Lean compiler output
// Module: Lean.Elab.Tactic.Basic
// Imports: public import Lean.Meta.Tactic.Util public import Lean.Elab.Term import Init.Omega
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_goalsToMessageData_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_goalsToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n\n"};
static const lean_object* l_Lean_Elab_goalsToMessageData___closed__0 = (const lean_object*)&l_Lean_Elab_goalsToMessageData___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Elab_goalsToMessageData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__7_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___closed__0_value;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Term_reportUnsolvedGoals___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l_Lean_Elab_Term_reportUnsolvedGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_reportUnsolvedGoals___closed__0_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(83, 55, 102, 232, 177, 170, 100, 130)}};
static const lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__0 = (const lean_object*)&l_Lean_Elab_Term_reportUnsolvedGoals___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_reportUnsolvedGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "unsolved goals\n"};
static const lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__1 = (const lean_object*)&l_Lean_Elab_Term_reportUnsolvedGoals___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Term_reportUnsolvedGoals___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_instMonadTacticM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_instMonadTacticM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instMonadTacticM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadTacticM___closed__2_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instMonadTacticM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadTacticM___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instMonadTacticM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadTacticM___closed__4_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instMonadTacticM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadTacticM___closed__5_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instMonadTacticM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadTacticM___closed__6_value;
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instMonadTacticM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadTacticM___closed__7_value;
static const lean_closure_object l_Lean_Elab_Tactic_instMonadTacticM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadTacticM___closed__8_value;
static const lean_closure_object l_Lean_Elab_Tactic_instMonadTacticM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadTacticM___closed__9_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM;
extern lean_object* l_Lean_instInhabitedMessageData_default;
static lean_once_cell_t l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instInhabitedTacticM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_instInhabitedTacticM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_run___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_run___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_run___lam__1___closed__0_value;
uint8_t l_Lean_Elab_isAbortTacticException(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withRestoreOrSaveFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "builtin_tactic"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 157, 68, 106, 181, 20, 206, 204)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "tacticElabAttribute"};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 89, 192, 126, 5, 198, 173, 31)}};
static const lean_object* l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value;
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static const lean_string_object l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 386, .m_capacity = 386, .m_length = 383, .m_data = "Registers a tactic elaborator for the given syntax node kind.\n\nA tactic elaborator should have type `Lean.Elab.Tactic.Tactic` (which is\n`Lean.Syntax → Lean.Elab.Tactic.TacticM Unit`), i.e. should take syntax of the given syntax\nnode kind as a parameter and alter the tactic state.\n\nThe `elab_rules` and `elab` commands should usually be preferred over using this attribute\ndirectly.\n"};
static const lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1___closed__0_value;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(135) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(147) << 1) | 1)),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(146) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(146) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0_value;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1_value;
extern lean_object* l_Lean_Core_instMonadInfoTreeCoreM;
lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7;
lean_object* l_instMonadFinallyEST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__8_value;
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__8_value)} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__9_value;
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__9_value)} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__10_value;
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__10_value)} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__11_value;
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__11_value)} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__12_value;
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__12_value)} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__13_value;
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__13_value)} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__14_value;
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__14_value)} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__15_value;
static const lean_closure_object l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_tryFinally___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__15_value)} };
static const lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__16_value;
lean_object* l_Lean_Elab_withInfoTreeContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unexpected syntax"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__1;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "backtrack"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 80, 147, 42, 129, 120, 92, 28)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 5, 110, 95, 173, 122, 172, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1_value;
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__2_value;
lean_object* l_Lean_isTracingEnabledFor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
lean_object* l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___boxed(lean_object**);
extern lean_object* l_Lean_Core_instMonadTraceCoreM;
lean_object* l_Lean_instMonadTraceOfMonadLift___redArg(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__5;
lean_object* l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadOptionsCoreM___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__6_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__6_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__7_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__7_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__8_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__8_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__9_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__9_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__10_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__10_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__11_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__11_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__13;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__14;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__15;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
lean_object* l_Lean_Core_getMessageLog___redArg(lean_object*);
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_builtinIncrementalElabs;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_incrementalAttr;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 30, 230, 20, 64, 162, 204, 1)}};
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 17, 142, 189, 192, 166, 31, 124)}};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "reuse stopped: guard failed at "};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__2_value;
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__1_value;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__0_value;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__1_value;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__21_value;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__3_value;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_instInhabitedTacticParsedSnapshot_default;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__0___boxed(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__2;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___boxed(lean_object**);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_evalTactic___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__1___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tactic execution"};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_evalTactic___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Tactic `"};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_evalTactic___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` has not been implemented"};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_evalTactic___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalTactic___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_evalTactic___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "step"};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_evalTactic___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_evalTactic___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(217, 235, 194, 189, 11, 11, 236, 225)}};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalTactic___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_evalTactic___lam__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_evalTactic_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_evalTactic___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unexpected tactic"};
static const lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_evalTactic___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__16;
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expandEval"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "evalTactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__1_value),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__2_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__3_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 221, 231, 157, 132, 214, 191, 251)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__6_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(211, 214, 12, 135, 134, 172, 207, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 183, 137, 37, 46, 197, 119, 226)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__8_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 171, 216, 167, 180, 6, 218, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__9_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 66, 105, 167, 96, 16, 185, 63)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(88, 11, 60, 85, 34, 82, 218, 163)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(21, 227, 109, 164, 11, 217, 220, 147)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__15;
extern lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__17;
static const lean_array_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__18_value;
lean_object* l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go(lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__19_value;
lean_object* lean_io_promise_new();
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_evalTactic_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "No goals to be solved"};
static const lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_done___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__1;
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatchRestore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatchRestore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatchRestore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatchRestore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_tryCatchRestore___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM = (const lean_object*)&l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRecover___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRecover___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRecover(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRecover___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSuppressedMessages(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCapturedMessages___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCapturedMessages___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCapturedMessages(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCapturedMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_hasErrorMessages___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_hasErrorMessages___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_hasErrorMessages___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_hasErrorMessages___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_hasErrorMessages___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_hasErrorMessages___closed__0_value;
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_hasErrorMessages(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_hasErrorMessages___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwOrLogErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwOrLogErrorAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwOrLogError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwOrLogError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_instOrElseTacticM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_orElse___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_instOrElseTacticM___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_instOrElseTacticM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instOrElseTacticM(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Failed"};
static const lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__1;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__0;
lean_object* l_StateRefT_x27_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3;
lean_object* l_ReaderT_instMonadExceptOf___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__12;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__13;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__15;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__16;
static lean_once_cell_t l_Lean_Elab_Tactic_instAlternativeTacticM___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__17;
static const lean_closure_object l_Lean_Elab_Tactic_instAlternativeTacticM___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_orElse___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__18_value;
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_saveTacticInfoForToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_saveTacticInfoForToken___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_saveTacticInfoForToken___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadLCtxMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadLCtxMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__1_value)} };
static const lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__2_value)} };
static const lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__3_value)} };
static const lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__4_value;
lean_object* l_Lean_Elab_withMacroExpansionInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoals___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoals___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_popMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_popMainGoal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_popMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_popMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAtRaw(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAtRaw___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "Tactic failed: Resulting expression contains metavariables"};
static const lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__1;
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "attempting to close the goal using"};
static const lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "\nthis is often due occurs-check failure"};
static const lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__3;
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isAnonymousMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_setMVarUserName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1_value;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 80, 147, 42, 129, 120, 92, 28)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 94, 177, 149, 139, 182, 114, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 10, 243, 10, 127, 148, 195, 73)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 248, 229, 170, 72, 192, 85, 130)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__5_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 198, 105, 238, 201, 105, 236, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(83, 132, 204, 196, 65, 182, 127, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(140, 62, 37, 30, 58, 192, 122, 79)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__10_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__10_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__10_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__11_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__11_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__12_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__12_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__12_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__13_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__13_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__14_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__14_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),((lean_object*)(((size_t)(778036212) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(197, 183, 253, 224, 69, 113, 149, 84)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__10_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 68, 53, 201, 145, 56, 50, 137)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__12_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 124, 135, 212, 134, 112, 60, 253)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(19, 239, 178, 44, 225, 249, 105, 29)}};
static const lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
x_9 = lean_ctor_get(x_8, 0);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
x_10 = x_8;
x_11 = x_16;
goto block_15;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_8, 0);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
x_18 = x_8;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = l_Lean_instBEqMVarId_beq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = l_Lean_instBEqMVarId_beq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableMVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableMVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_37; 
x_5 = lean_st_ref_take(x_3);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
x_11 = x_5;
x_12 = x_37;
goto block_36;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_35; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_ctor_get(x_6, 5);
x_19 = lean_ctor_get(x_6, 6);
x_20 = lean_ctor_get(x_6, 7);
x_21 = lean_ctor_get(x_6, 8);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_22 = x_6;
x_23 = x_35;
goto block_34;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0___redArg(x_20, x_1, x_2);
if (x_23 == 0)
{
lean_ctor_set(x_22, 7, x_24);
x_25 = x_22;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set(x_33, 2, x_15);
lean_ctor_set(x_33, 3, x_16);
lean_ctor_set(x_33, 4, x_17);
lean_ctor_set(x_33, 5, x_18);
lean_ctor_set(x_33, 6, x_19);
lean_ctor_set(x_33, 7, x_24);
lean_ctor_set(x_33, 8, x_21);
x_25 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_26; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_25);
x_26 = x_11;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_7);
lean_ctor_set(x_31, 2, x_8);
lean_ctor_set(x_31, 3, x_9);
lean_ctor_set(x_31, 4, x_10);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_st_ref_set(x_3, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
lean_inc(x_5);
x_12 = l_Lean_Meta_mkLabeledSorry(x_10, x_2, x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___redArg(x_3, x_13, x_5);
lean_dec(x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_3);
x_15 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_16 = x_12;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_23 = lean_ctor_get(x_9, 0);
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
x_24 = x_9;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Elab_admitGoal___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_8 = l_Lean_mkMVar(x_1);
x_9 = lean_box(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_admitGoal___lam__0___boxed), 8, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_1);
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_admitGoal_spec__1___redArg(x_1, x_10, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_admitGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Elab_admitGoal(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__4(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_goalsToMessageData_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_goalsToMessageData___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_goalsToMessageData___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_goalsToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at___00Lean_Elab_goalsToMessageData_spec__0(x_1, x_2);
x_4 = lean_obj_once(&l_Lean_Elab_goalsToMessageData___closed__1, &l_Lean_Elab_goalsToMessageData___closed__1_once, _init_l_Lean_Elab_goalsToMessageData___closed__1);
x_5 = l_Lean_MessageData_joinSep(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__2));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__3));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__4));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__5));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__6));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__7));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; uint8_t x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; uint8_t x_103; uint8_t x_119; 
x_94 = 2;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_94);
if (x_119 == 0)
{
x_103 = x_119;
goto block_118;
}
else
{
uint8_t x_120; 
lean_inc_ref(x_2);
x_120 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_103 = x_120;
goto block_118;
}
block_45:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_44; 
x_19 = lean_st_ref_take(x_18);
x_20 = lean_ctor_get(x_17, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 7);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 2);
x_25 = lean_ctor_get(x_19, 3);
x_26 = lean_ctor_get(x_19, 4);
x_27 = lean_ctor_get(x_19, 5);
x_28 = lean_ctor_get(x_19, 6);
x_29 = lean_ctor_get(x_19, 7);
x_30 = lean_ctor_get(x_19, 8);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
x_31 = x_19;
x_32 = x_44;
goto block_43;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
x_31 = lean_box(0);
x_32 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_15);
x_35 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_35, 0, x_14);
lean_ctor_set(x_35, 1, x_12);
lean_ctor_set(x_35, 2, x_10);
lean_ctor_set(x_35, 3, x_11);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_16);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 2, x_4);
x_36 = l_Lean_MessageLog_add(x_35, x_28);
if (x_32 == 0)
{
lean_ctor_set(x_31, 6, x_36);
x_37 = x_31;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_23);
lean_ctor_set(x_42, 2, x_24);
lean_ctor_set(x_42, 3, x_25);
lean_ctor_set(x_42, 4, x_26);
lean_ctor_set(x_42, 5, x_27);
lean_ctor_set(x_42, 6, x_36);
lean_ctor_set(x_42, 7, x_29);
lean_ctor_set(x_42, 8, x_30);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_st_ref_set(x_18, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
block_70:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_69; 
x_54 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_55 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3(x_54, x_5, x_6, x_7, x_8);
x_56 = lean_ctor_get(x_55, 0);
x_69 = !lean_is_exclusive(x_55);
if (x_69 == 0)
{
x_57 = x_55;
x_58 = x_69;
goto block_68;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_47);
x_59 = l_Lean_FileMap_toPosition(x_47, x_48);
lean_dec(x_48);
x_60 = l_Lean_FileMap_toPosition(x_47, x_53);
lean_dec(x_53);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___closed__0));
if (x_50 == 0)
{
lean_del_object(x_57);
lean_dec_ref(x_46);
x_10 = x_61;
x_11 = x_62;
x_12 = x_59;
x_13 = x_49;
x_14 = x_51;
x_15 = x_56;
x_16 = x_52;
x_17 = x_7;
x_18 = x_8;
goto block_45;
}
else
{
uint8_t x_63; 
lean_inc(x_56);
x_63 = l_Lean_MessageData_hasTag(x_46, x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_61);
lean_dec_ref(x_59);
lean_dec(x_56);
lean_dec_ref(x_51);
lean_dec_ref(x_7);
x_64 = lean_box(0);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_64);
x_65 = x_57;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
else
{
lean_del_object(x_57);
x_10 = x_61;
x_11 = x_62;
x_12 = x_59;
x_13 = x_49;
x_14 = x_51;
x_15 = x_56;
x_16 = x_52;
x_17 = x_7;
x_18 = x_8;
goto block_45;
}
}
}
}
block_81:
{
lean_object* x_79; 
x_79 = l_Lean_Syntax_getTailPos_x3f(x_77, x_76);
lean_dec(x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_inc(x_78);
x_46 = x_71;
x_47 = x_72;
x_48 = x_78;
x_49 = x_73;
x_50 = x_74;
x_51 = x_75;
x_52 = x_76;
x_53 = x_78;
goto block_70;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_46 = x_71;
x_47 = x_72;
x_48 = x_78;
x_49 = x_73;
x_50 = x_74;
x_51 = x_75;
x_52 = x_76;
x_53 = x_80;
goto block_70;
}
}
block_93:
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_replaceRef(x_1, x_84);
lean_dec(x_84);
x_90 = l_Lean_Syntax_getPos_x3f(x_89, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_unsigned_to_nat(0u);
x_71 = x_82;
x_72 = x_83;
x_73 = x_88;
x_74 = x_85;
x_75 = x_86;
x_76 = x_87;
x_77 = x_89;
x_78 = x_91;
goto block_81;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec_ref(x_90);
x_71 = x_82;
x_72 = x_83;
x_73 = x_88;
x_74 = x_85;
x_75 = x_86;
x_76 = x_87;
x_77 = x_89;
x_78 = x_92;
goto block_81;
}
}
block_102:
{
if (x_101 == 0)
{
x_82 = x_98;
x_83 = x_95;
x_84 = x_96;
x_85 = x_97;
x_86 = x_99;
x_87 = x_100;
x_88 = x_3;
goto block_93;
}
else
{
x_82 = x_98;
x_83 = x_95;
x_84 = x_96;
x_85 = x_97;
x_86 = x_99;
x_87 = x_100;
x_88 = x_94;
goto block_93;
}
}
block_118:
{
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; 
x_104 = lean_ctor_get(x_7, 0);
x_105 = lean_ctor_get(x_7, 1);
x_106 = lean_ctor_get(x_7, 2);
x_107 = lean_ctor_get(x_7, 5);
x_108 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_109 = lean_box(x_103);
x_110 = lean_box(x_108);
x_111 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
x_112 = 1;
x_113 = l_Lean_instBEqMessageSeverity_beq(x_3, x_112);
if (x_113 == 0)
{
lean_inc_ref(x_104);
lean_inc(x_107);
lean_inc_ref(x_105);
x_95 = x_105;
x_96 = x_107;
x_97 = x_108;
x_98 = x_111;
x_99 = x_104;
x_100 = x_103;
x_101 = x_113;
goto block_102;
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = l_Lean_warningAsError;
x_115 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(x_106, x_114);
lean_inc_ref(x_104);
lean_inc(x_107);
lean_inc_ref(x_105);
x_95 = x_105;
x_96 = x_107;
x_97 = x_108;
x_98 = x_111;
x_99 = x_104;
x_100 = x_103;
x_101 = x_115;
goto block_102;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 2;
x_8 = 0;
x_9 = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0(x_1, x_7, x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = 1;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_12 = l_Lean_Elab_admitGoal(x_9, x_11, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_dec_ref(x_12);
x_1 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forM___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Term_reportUnsolvedGoals___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = ((lean_object*)(l_Lean_Elab_Term_reportUnsolvedGoals___closed__0));
x_8 = lean_obj_once(&l_Lean_Elab_Term_reportUnsolvedGoals___closed__2, &l_Lean_Elab_Term_reportUnsolvedGoals___closed__2_once, _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__2);
lean_inc(x_1);
x_9 = l_Lean_Elab_goalsToMessageData(x_1);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_inc_ref(x_4);
x_12 = l_Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0(x_11, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
x_13 = l_List_forM___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__1(x_1, x_2, x_3, x_4, x_5);
return x_13;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_reportUnsolvedGoals(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_instMonadTacticM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = lean_apply_9(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_apply_10(x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_17 = lean_ctor_get(x_14, 0);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
x_18 = x_14;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_instMonadTacticM___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadTacticM___closed__0, &l_Lean_Elab_Tactic_instMonadTacticM___closed__0_once, _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__0);
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_119; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadTacticM___closed__1, &l_Lean_Elab_Tactic_instMonadTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
x_2 = lean_ctor_get(x_1, 0);
x_119 = !lean_is_exclusive(x_1);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_1, 1);
lean_dec(x_120);
x_3 = x_1;
x_4 = x_119;
goto block_118;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_116; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_2, 4);
x_116 = !lean_is_exclusive(x_2);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_2, 1);
lean_dec(x_117);
x_9 = x_2;
x_10 = x_116;
goto block_115;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__2));
x_12 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__3));
lean_inc_ref(x_5);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_5);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_8);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_17, 0, x_7);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_18, 0, x_6);
if (x_10 == 0)
{
lean_ctor_set(x_9, 4, x_16);
lean_ctor_set(x_9, 3, x_17);
lean_ctor_set(x_9, 2, x_18);
lean_ctor_set(x_9, 1, x_11);
lean_ctor_set(x_9, 0, x_15);
x_19 = x_9;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_15);
lean_ctor_set(x_114, 1, x_11);
lean_ctor_set(x_114, 2, x_18);
lean_ctor_set(x_114, 3, x_17);
lean_ctor_set(x_114, 4, x_16);
x_19 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_20; 
if (x_4 == 0)
{
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_19);
x_20 = x_3;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_19);
lean_ctor_set(x_112, 1, x_12);
x_20 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_109; 
x_21 = l_ReaderT_instMonad___redArg(x_20);
x_22 = lean_ctor_get(x_21, 0);
x_109 = !lean_is_exclusive(x_21);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_21, 1);
lean_dec(x_110);
x_23 = x_21;
x_24 = x_109;
goto block_108;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_106; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 2);
x_27 = lean_ctor_get(x_22, 3);
x_28 = lean_ctor_get(x_22, 4);
x_106 = !lean_is_exclusive(x_22);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_22, 1);
lean_dec(x_107);
x_29 = x_22;
x_30 = x_106;
goto block_105;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__4));
x_32 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__5));
lean_inc_ref(x_25);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_33, 0, x_25);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_28);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_37, 0, x_27);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_38, 0, x_26);
if (x_30 == 0)
{
lean_ctor_set(x_29, 4, x_36);
lean_ctor_set(x_29, 3, x_37);
lean_ctor_set(x_29, 2, x_38);
lean_ctor_set(x_29, 1, x_31);
lean_ctor_set(x_29, 0, x_35);
x_39 = x_29;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_35);
lean_ctor_set(x_104, 1, x_31);
lean_ctor_set(x_104, 2, x_38);
lean_ctor_set(x_104, 3, x_37);
lean_ctor_set(x_104, 4, x_36);
x_39 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_40; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 1, x_32);
lean_ctor_set(x_23, 0, x_39);
x_40 = x_23;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_39);
lean_ctor_set(x_102, 1, x_32);
x_40 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_99; 
x_41 = l_ReaderT_instMonad___redArg(x_40);
x_42 = lean_ctor_get(x_41, 0);
x_99 = !lean_is_exclusive(x_41);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_41, 1);
lean_dec(x_100);
x_43 = x_41;
x_44 = x_99;
goto block_98;
}
else
{
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_96; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 2);
x_47 = lean_ctor_get(x_42, 3);
x_48 = lean_ctor_get(x_42, 4);
x_96 = !lean_is_exclusive(x_42);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_42, 1);
lean_dec(x_97);
x_49 = x_42;
x_50 = x_96;
goto block_95;
}
else
{
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_42);
x_49 = lean_box(0);
x_50 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__6));
x_52 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__7));
lean_inc_ref(x_45);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_53, 0, x_45);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_54, 0, x_45);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_48);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_57, 0, x_47);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_58, 0, x_46);
if (x_50 == 0)
{
lean_ctor_set(x_49, 4, x_56);
lean_ctor_set(x_49, 3, x_57);
lean_ctor_set(x_49, 2, x_58);
lean_ctor_set(x_49, 1, x_51);
lean_ctor_set(x_49, 0, x_55);
x_59 = x_49;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_94, 0, x_55);
lean_ctor_set(x_94, 1, x_51);
lean_ctor_set(x_94, 2, x_58);
lean_ctor_set(x_94, 3, x_57);
lean_ctor_set(x_94, 4, x_56);
x_59 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_60; 
if (x_44 == 0)
{
lean_ctor_set(x_43, 1, x_52);
lean_ctor_set(x_43, 0, x_59);
x_60 = x_43;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_59);
lean_ctor_set(x_92, 1, x_52);
x_60 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_89; 
x_61 = l_ReaderT_instMonad___redArg(x_60);
x_62 = lean_ctor_get(x_61, 0);
x_89 = !lean_is_exclusive(x_61);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_61, 1);
lean_dec(x_90);
x_63 = x_61;
x_64 = x_89;
goto block_88;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_86; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_ctor_get(x_62, 2);
x_67 = lean_ctor_get(x_62, 3);
x_68 = lean_ctor_get(x_62, 4);
x_86 = !lean_is_exclusive(x_62);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_62, 1);
lean_dec(x_87);
x_69 = x_62;
x_70 = x_86;
goto block_85;
}
else
{
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_62);
x_69 = lean_box(0);
x_70 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__8));
x_72 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__9));
lean_inc_ref(x_65);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_73, 0, x_65);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_74, 0, x_65);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_76, 0, x_68);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_77, 0, x_67);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_78, 0, x_66);
if (x_70 == 0)
{
lean_ctor_set(x_69, 4, x_76);
lean_ctor_set(x_69, 3, x_77);
lean_ctor_set(x_69, 2, x_78);
lean_ctor_set(x_69, 1, x_71);
lean_ctor_set(x_69, 0, x_75);
x_79 = x_69;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_75);
lean_ctor_set(x_84, 1, x_71);
lean_ctor_set(x_84, 2, x_78);
lean_ctor_set(x_84, 3, x_77);
lean_ctor_set(x_84, 4, x_76);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_64 == 0)
{
lean_ctor_set(x_63, 1, x_72);
lean_ctor_set(x_63, 0, x_79);
x_80 = x_63;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_72);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedMessageData_default;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_obj_once(&l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___closed__0, &l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___closed__0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_instInhabitedTacticM___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getGoals___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getGoals___redArg(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_take(x_2);
lean_dec(x_4);
x_5 = lean_st_ref_set(x_2, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_setGoals___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_setGoals___redArg(x_1, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_setGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_27; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
x_15 = x_1;
x_16 = x_27;
goto block_26;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___redArg(x_13, x_8);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
goto block_21;
}
else
{
lean_del_object(x_15);
lean_dec(x_13);
x_1 = x_14;
goto _start;
}
block_21:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_2);
x_17 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_2);
x_17 = x_20;
goto block_19;
}
block_19:
{
x_1 = x_14;
x_2 = x_17;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_filterAuxM___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Elab_Tactic_getGoals___redArg(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_box(0);
x_13 = l_List_filterAuxM___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__1(x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_List_reverse___redArg(x_14);
x_16 = l_Lean_Elab_Tactic_setGoals___redArg(x_15, x_2);
return x_16;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec_ref(x_13);
x_18 = l_Lean_Elab_Tactic_setGoals___redArg(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_19 = lean_ctor_get(x_13, 0);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_20 = x_13;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___redArg(x_1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = l_Lean_Elab_Tactic_getGoals___redArg(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_13 = x_10;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_mk_ref(x_3);
lean_inc(x_11);
x_12 = lean_apply_9(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_13 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_14 = x_12;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_st_ref_get(x_11);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_11);
x_23 = lean_ctor_get(x_12, 0);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
x_24 = x_12;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_st_mk_ref(x_4);
lean_inc(x_12);
x_13 = lean_apply_9(x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_23; 
x_14 = lean_ctor_get(x_13, 0);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
x_15 = x_13;
x_16 = x_23;
goto block_22;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_st_ref_get(x_12);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_12);
x_24 = lean_ctor_get(x_13, 0);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
x_25 = x_13;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_mk_ref(x_3);
lean_inc(x_11);
x_12 = lean_apply_9(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
x_14 = x_12;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_st_ref_get(x_11);
lean_dec(x_11);
lean_dec(x_16);
if (x_15 == 0)
{
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_13);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_dec(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_st_mk_ref(x_4);
lean_inc(x_12);
x_13 = lean_apply_9(x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
x_15 = x_13;
x_16 = x_22;
goto block_21;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_st_ref_get(x_12);
lean_dec(x_12);
lean_dec(x_17);
if (x_16 == 0)
{
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_11, 0);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
x_13 = x_11;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_21; 
x_5 = lean_st_ref_take(x_1);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 3);
x_9 = lean_ctor_get(x_5, 4);
x_10 = lean_ctor_get(x_5, 5);
x_11 = lean_ctor_get(x_5, 6);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_5, 2);
lean_dec(x_22);
x_12 = x_5;
x_13 = x_21;
goto block_20;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 2, x_2);
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 3, x_8);
lean_ctor_set(x_19, 4, x_9);
lean_ctor_set(x_19, 5, x_10);
lean_ctor_set(x_19, 6, x_11);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_st_ref_set(x_1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_run___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_71; 
x_10 = lean_st_ref_get(x_4);
x_11 = lean_st_ref_take(x_4);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_16 = lean_ctor_get(x_11, 5);
x_17 = lean_ctor_get(x_11, 6);
x_71 = !lean_is_exclusive(x_11);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_11, 2);
lean_dec(x_72);
x_18 = x_11;
x_19 = x_71;
goto block_70;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_20);
x_21 = x_18;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 2, x_20);
lean_ctor_set(x_69, 3, x_14);
lean_ctor_set(x_69, 4, x_15);
lean_ctor_set(x_69, 5, x_16);
lean_ctor_set(x_69, 6, x_17);
x_21 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_38; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_59; lean_object* x_63; 
x_22 = lean_st_ref_set(x_4, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_st_mk_ref(x_23);
x_25 = lean_ctor_get(x_10, 2);
lean_inc(x_25);
lean_dec(x_10);
x_51 = ((lean_object*)(l_Lean_Elab_Tactic_run___lam__1___closed__0));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_24);
x_63 = lean_apply_9(x_2, x_51, x_24, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec_ref(x_63);
x_64 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_51, x_24, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_38 = x_65;
goto block_50;
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec_ref(x_64);
x_59 = x_66;
goto block_62;
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec_ref(x_63);
x_59 = x_67;
goto block_62;
}
block_37:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_run___lam__0(x_4, x_25, x_27);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_29 = x_28;
x_30 = x_35;
goto block_34;
}
else
{
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_26);
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_26);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
block_50:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
x_39 = lean_st_ref_get(x_24);
lean_dec(x_24);
lean_dec(x_39);
lean_inc(x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = l_Lean_Elab_Tactic_run___lam__0(x_4, x_25, x_40);
lean_dec_ref(x_40);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_41, 0);
lean_dec(x_49);
x_42 = x_41;
x_43 = x_48;
goto block_47;
}
else
{
lean_dec(x_41);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_38);
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_38);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
block_58:
{
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Elab_isAbortTacticException(x_52);
if (x_54 == 0)
{
lean_dec(x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_26 = x_52;
goto block_37;
}
else
{
lean_object* x_55; 
lean_dec_ref(x_52);
x_55 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_51, x_24, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_38 = x_56;
goto block_50;
}
else
{
lean_object* x_57; 
lean_dec(x_24);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec_ref(x_55);
x_26 = x_57;
goto block_37;
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_26 = x_52;
goto block_37;
}
}
block_62:
{
uint8_t x_60; 
x_60 = l_Lean_Exception_isInterrupt(x_59);
if (x_60 == 0)
{
uint8_t x_61; 
lean_inc_ref(x_59);
x_61 = l_Lean_Exception_isRuntime(x_59);
x_52 = x_59;
x_53 = x_61;
goto block_58;
}
else
{
x_52 = x_59;
x_53 = x_60;
goto block_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_run___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___lam__1___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_run_spec__0___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_saveState___redArg(x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_7 = lean_ctor_get(x_6, 0);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
x_8 = x_6;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_st_ref_get(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_6, 0);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
x_18 = x_6;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_saveState___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_saveState___redArg(x_2, x_4, x_6, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_saveState(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = l_Lean_Elab_Term_SavedState_restore(x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_14 = x_13;
x_15 = x_21;
goto block_20;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_st_ref_set(x_3, x_12);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SavedState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_ctor_get(x_80, 1);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_st_ref_set(x_5, x_82);
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
goto block_79;
}
else
{
x_51 = x_4;
x_52 = x_5;
x_53 = x_6;
x_54 = x_7;
x_55 = x_8;
x_56 = x_9;
x_57 = x_10;
x_58 = x_11;
goto block_79;
}
block_50:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Term_withRestoreOrSaveFull___redArg(x_21, x_2, x_17, x_15, x_16, x_18, x_19, x_20, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_41; 
x_23 = lean_ctor_get(x_22, 0);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
x_24 = x_22;
x_25 = x_41;
goto block_40;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_39; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
x_28 = x_23;
x_29 = x_39;
goto block_38;
}
else
{
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
if (x_29 == 0)
{
lean_ctor_set(x_28, 1, x_31);
x_32 = x_28;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_31);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_32);
x_33 = x_24;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_13);
x_42 = lean_ctor_get(x_22, 0);
x_49 = !lean_is_exclusive(x_22);
if (x_49 == 0)
{
x_43 = x_22;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_22);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
block_79:
{
lean_object* x_59; 
lean_inc(x_52);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_59, 0, x_3);
lean_closure_set(x_59, 1, x_51);
lean_closure_set(x_59, 2, x_52);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_60; 
x_60 = lean_box(0);
x_13 = x_52;
x_14 = x_58;
x_15 = x_53;
x_16 = x_54;
x_17 = x_59;
x_18 = x_55;
x_19 = x_56;
x_20 = x_57;
x_21 = x_60;
goto block_50;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_78; 
x_61 = lean_ctor_get(x_1, 0);
x_78 = !lean_is_exclusive(x_1);
if (x_78 == 0)
{
x_62 = x_1;
x_63 = x_78;
goto block_77;
}
else
{
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_76; 
x_64 = lean_ctor_get(x_61, 1);
x_65 = lean_ctor_get(x_61, 0);
x_76 = !lean_is_exclusive(x_61);
if (x_76 == 0)
{
x_66 = x_61;
x_67 = x_76;
goto block_75;
}
else
{
lean_inc(x_64);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_box(0);
x_67 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_68);
lean_dec(x_64);
if (x_67 == 0)
{
lean_ctor_set(x_66, 1, x_68);
x_69 = x_66;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_68);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_63 == 0)
{
lean_ctor_set(x_62, 0, x_69);
x_70 = x_62;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_69);
x_70 = x_72;
goto block_71;
}
block_71:
{
x_13 = x_52;
x_14 = x_58;
x_15 = x_53;
x_16 = x_54;
x_17 = x_59;
x_18 = x_55;
x_19 = x_56;
x_20 = x_57;
x_21 = x_70;
goto block_50;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_withRestoreOrSaveFull___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRestoreOrSaveFull___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_withRestoreOrSaveFull(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 11);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getCurrMacroScope___redArg(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getCurrMacroScope___redArg(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getCurrMacroScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_mainModule(x_4);
lean_dec_ref(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getMainModule___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainModule___redArg(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainModule(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__1));
x_2 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___closed__0));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__4_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_));
x_4 = l_Lean_Name_mkStr4(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__1_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__2_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_));
x_4 = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_));
x_5 = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__6_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_));
x_6 = lean_obj_once(&l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_initFn___closed__7_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_);
x_7 = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_));
x_8 = l_Lean_Elab_mkElabAttribute___redArg(x_2, x_4, x_5, x_6, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1___closed__0));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_st_ref_get(x_9);
x_14 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_37; 
x_15 = lean_ctor_get(x_14, 0);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
x_16 = x_14;
x_17 = x_37;
goto block_36;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_31; 
x_18 = lean_ctor_get(x_13, 0);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_13, 4);
lean_dec(x_32);
x_33 = lean_ctor_get(x_13, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_13, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_13, 1);
lean_dec(x_35);
x_19 = x_13;
x_20 = x_31;
goto block_30;
}
else
{
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
if (x_20 == 0)
{
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 0, x_22);
x_23 = x_19;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_2);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_15);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_24);
x_25 = x_16;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_14, 0);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
x_39 = x_14;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkTacticInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_mkTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_ref_get(x_7);
x_12 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_13 = lean_ctor_get(x_12, 0);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
x_14 = x_12;
x_15 = x_22;
goto block_21;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_16);
lean_dec(x_11);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkTacticInfo___boxed), 12, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_1);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_1);
x_23 = lean_ctor_get(x_12, 0);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
x_24 = x_12;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
x_14 = x_12;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_2);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_12, 0);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
x_23 = x_12;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withTacticInfoContext___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadInfoTreeCoreM;
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_3 = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__2, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__2);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_3 = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__3, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__3);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_3 = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__4, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__4_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_3 = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__5, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__5);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_3 = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__6, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__6_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__6);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_3 = l_Lean_Elab_instMonadInfoTreeOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_145; 
x_12 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadTacticM___closed__1, &l_Lean_Elab_Tactic_instMonadTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
x_13 = lean_ctor_get(x_12, 0);
x_145 = !lean_is_exclusive(x_12);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_12, 1);
lean_dec(x_146);
x_14 = x_12;
x_15 = x_145;
goto block_144;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_142; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_142 = !lean_is_exclusive(x_13);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_13, 1);
lean_dec(x_143);
x_20 = x_13;
x_21 = x_142;
goto block_141;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = x_142;
goto block_141;
}
block_141:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__2));
x_23 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__3));
lean_inc_ref(x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_19);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_18);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_29, 0, x_17);
if (x_21 == 0)
{
lean_ctor_set(x_20, 4, x_27);
lean_ctor_set(x_20, 3, x_28);
lean_ctor_set(x_20, 2, x_29);
lean_ctor_set(x_20, 1, x_22);
lean_ctor_set(x_20, 0, x_26);
x_30 = x_20;
goto block_139;
}
else
{
lean_object* x_140; 
x_140 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_140, 0, x_26);
lean_ctor_set(x_140, 1, x_22);
lean_ctor_set(x_140, 2, x_29);
lean_ctor_set(x_140, 3, x_28);
lean_ctor_set(x_140, 4, x_27);
x_30 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_31; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_30);
x_31 = x_14;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_30);
lean_ctor_set(x_138, 1, x_23);
x_31 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_135; 
x_32 = l_ReaderT_instMonad___redArg(x_31);
x_33 = lean_ctor_get(x_32, 0);
x_135 = !lean_is_exclusive(x_32);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_32, 1);
lean_dec(x_136);
x_34 = x_32;
x_35 = x_135;
goto block_134;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_132; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 2);
x_38 = lean_ctor_get(x_33, 3);
x_39 = lean_ctor_get(x_33, 4);
x_132 = !lean_is_exclusive(x_33);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_33, 1);
lean_dec(x_133);
x_40 = x_33;
x_41 = x_132;
goto block_131;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__4));
x_43 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__5));
lean_inc_ref(x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_39);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_48, 0, x_38);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_49, 0, x_37);
if (x_41 == 0)
{
lean_ctor_set(x_40, 4, x_47);
lean_ctor_set(x_40, 3, x_48);
lean_ctor_set(x_40, 2, x_49);
lean_ctor_set(x_40, 1, x_42);
lean_ctor_set(x_40, 0, x_46);
x_50 = x_40;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_46);
lean_ctor_set(x_130, 1, x_42);
lean_ctor_set(x_130, 2, x_49);
lean_ctor_set(x_130, 3, x_48);
lean_ctor_set(x_130, 4, x_47);
x_50 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_51; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 1, x_43);
lean_ctor_set(x_34, 0, x_50);
x_51 = x_34;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_50);
lean_ctor_set(x_128, 1, x_43);
x_51 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_125; 
x_52 = l_ReaderT_instMonad___redArg(x_51);
x_53 = lean_ctor_get(x_52, 0);
x_125 = !lean_is_exclusive(x_52);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_52, 1);
lean_dec(x_126);
x_54 = x_52;
x_55 = x_125;
goto block_124;
}
else
{
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_122; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 2);
x_58 = lean_ctor_get(x_53, 3);
x_59 = lean_ctor_get(x_53, 4);
x_122 = !lean_is_exclusive(x_53);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_53, 1);
lean_dec(x_123);
x_60 = x_53;
x_61 = x_122;
goto block_121;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_53);
x_60 = lean_box(0);
x_61 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__6));
x_63 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__7));
lean_inc_ref(x_56);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_64, 0, x_56);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_65, 0, x_56);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_67, 0, x_59);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_68, 0, x_58);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_69, 0, x_57);
if (x_61 == 0)
{
lean_ctor_set(x_60, 4, x_67);
lean_ctor_set(x_60, 3, x_68);
lean_ctor_set(x_60, 2, x_69);
lean_ctor_set(x_60, 1, x_62);
lean_ctor_set(x_60, 0, x_66);
x_70 = x_60;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_120, 0, x_66);
lean_ctor_set(x_120, 1, x_62);
lean_ctor_set(x_120, 2, x_69);
lean_ctor_set(x_120, 3, x_68);
lean_ctor_set(x_120, 4, x_67);
x_70 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_71; 
if (x_55 == 0)
{
lean_ctor_set(x_54, 1, x_63);
lean_ctor_set(x_54, 0, x_70);
x_71 = x_54;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_70);
lean_ctor_set(x_118, 1, x_63);
x_71 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_115; 
x_72 = l_ReaderT_instMonad___redArg(x_71);
x_73 = lean_ctor_get(x_72, 0);
x_115 = !lean_is_exclusive(x_72);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_72, 1);
lean_dec(x_116);
x_74 = x_72;
x_75 = x_115;
goto block_114;
}
else
{
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_112; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_73, 2);
x_78 = lean_ctor_get(x_73, 3);
x_79 = lean_ctor_get(x_73, 4);
x_112 = !lean_is_exclusive(x_73);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_73, 1);
lean_dec(x_113);
x_80 = x_73;
x_81 = x_112;
goto block_111;
}
else
{
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_73);
x_80 = lean_box(0);
x_81 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__8));
x_83 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__9));
lean_inc_ref(x_76);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_84, 0, x_76);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_85, 0, x_76);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_87, 0, x_79);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_88, 0, x_78);
x_89 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_89, 0, x_77);
if (x_81 == 0)
{
lean_ctor_set(x_80, 4, x_87);
lean_ctor_set(x_80, 3, x_88);
lean_ctor_set(x_80, 2, x_89);
lean_ctor_set(x_80, 1, x_82);
lean_ctor_set(x_80, 0, x_86);
x_90 = x_80;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_86);
lean_ctor_set(x_110, 1, x_82);
lean_ctor_set(x_110, 2, x_89);
lean_ctor_set(x_110, 3, x_88);
lean_ctor_set(x_110, 4, x_87);
x_90 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_91; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 1, x_83);
lean_ctor_set(x_74, 0, x_90);
x_91 = x_74;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_90);
lean_ctor_set(x_108, 1, x_83);
x_91 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7);
x_93 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__16));
x_96 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_96, 0, x_94);
x_97 = l_Lean_Elab_withInfoTreeContext___redArg(x_91, x_92, x_95, x_2, x_96);
x_98 = lean_apply_9(x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec_ref(x_91);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_99 = lean_ctor_get(x_93, 0);
x_106 = !lean_is_exclusive(x_93);
if (x_106 == 0)
{
x_100 = x_93;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withTacticInfoContext___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_146; 
x_13 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadTacticM___closed__1, &l_Lean_Elab_Tactic_instMonadTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
x_14 = lean_ctor_get(x_13, 0);
x_146 = !lean_is_exclusive(x_13);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_13, 1);
lean_dec(x_147);
x_15 = x_13;
x_16 = x_146;
goto block_145;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_143; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_ctor_get(x_14, 3);
x_20 = lean_ctor_get(x_14, 4);
x_143 = !lean_is_exclusive(x_14);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_14, 1);
lean_dec(x_144);
x_21 = x_14;
x_22 = x_143;
goto block_142;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__2));
x_24 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__3));
lean_inc_ref(x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_20);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_19);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_30, 0, x_18);
if (x_22 == 0)
{
lean_ctor_set(x_21, 4, x_28);
lean_ctor_set(x_21, 3, x_29);
lean_ctor_set(x_21, 2, x_30);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_27);
x_31 = x_21;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_27);
lean_ctor_set(x_141, 1, x_23);
lean_ctor_set(x_141, 2, x_30);
lean_ctor_set(x_141, 3, x_29);
lean_ctor_set(x_141, 4, x_28);
x_31 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_32; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_31);
x_32 = x_15;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_31);
lean_ctor_set(x_139, 1, x_24);
x_32 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_136; 
x_33 = l_ReaderT_instMonad___redArg(x_32);
x_34 = lean_ctor_get(x_33, 0);
x_136 = !lean_is_exclusive(x_33);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_33, 1);
lean_dec(x_137);
x_35 = x_33;
x_36 = x_136;
goto block_135;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_136;
goto block_135;
}
block_135:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_133; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 2);
x_39 = lean_ctor_get(x_34, 3);
x_40 = lean_ctor_get(x_34, 4);
x_133 = !lean_is_exclusive(x_34);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_34, 1);
lean_dec(x_134);
x_41 = x_34;
x_42 = x_133;
goto block_132;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_34);
x_41 = lean_box(0);
x_42 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__4));
x_44 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__5));
lean_inc_ref(x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_40);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_49, 0, x_39);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_50, 0, x_38);
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_48);
lean_ctor_set(x_41, 3, x_49);
lean_ctor_set(x_41, 2, x_50);
lean_ctor_set(x_41, 1, x_43);
lean_ctor_set(x_41, 0, x_47);
x_51 = x_41;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_47);
lean_ctor_set(x_131, 1, x_43);
lean_ctor_set(x_131, 2, x_50);
lean_ctor_set(x_131, 3, x_49);
lean_ctor_set(x_131, 4, x_48);
x_51 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_52; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 1, x_44);
lean_ctor_set(x_35, 0, x_51);
x_52 = x_35;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_51);
lean_ctor_set(x_129, 1, x_44);
x_52 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_126; 
x_53 = l_ReaderT_instMonad___redArg(x_52);
x_54 = lean_ctor_get(x_53, 0);
x_126 = !lean_is_exclusive(x_53);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_53, 1);
lean_dec(x_127);
x_55 = x_53;
x_56 = x_126;
goto block_125;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_126;
goto block_125;
}
block_125:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_123; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 2);
x_59 = lean_ctor_get(x_54, 3);
x_60 = lean_ctor_get(x_54, 4);
x_123 = !lean_is_exclusive(x_54);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_54, 1);
lean_dec(x_124);
x_61 = x_54;
x_62 = x_123;
goto block_122;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
x_61 = lean_box(0);
x_62 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__6));
x_64 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__7));
lean_inc_ref(x_57);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_66, 0, x_57);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_68, 0, x_60);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_69, 0, x_59);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_70, 0, x_58);
if (x_62 == 0)
{
lean_ctor_set(x_61, 4, x_68);
lean_ctor_set(x_61, 3, x_69);
lean_ctor_set(x_61, 2, x_70);
lean_ctor_set(x_61, 1, x_63);
lean_ctor_set(x_61, 0, x_67);
x_71 = x_61;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_121, 0, x_67);
lean_ctor_set(x_121, 1, x_63);
lean_ctor_set(x_121, 2, x_70);
lean_ctor_set(x_121, 3, x_69);
lean_ctor_set(x_121, 4, x_68);
x_71 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_72; 
if (x_56 == 0)
{
lean_ctor_set(x_55, 1, x_64);
lean_ctor_set(x_55, 0, x_71);
x_72 = x_55;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_71);
lean_ctor_set(x_119, 1, x_64);
x_72 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_116; 
x_73 = l_ReaderT_instMonad___redArg(x_72);
x_74 = lean_ctor_get(x_73, 0);
x_116 = !lean_is_exclusive(x_73);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_73, 1);
lean_dec(x_117);
x_75 = x_73;
x_76 = x_116;
goto block_115;
}
else
{
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_box(0);
x_76 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_113; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 2);
x_79 = lean_ctor_get(x_74, 3);
x_80 = lean_ctor_get(x_74, 4);
x_113 = !lean_is_exclusive(x_74);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_74, 1);
lean_dec(x_114);
x_81 = x_74;
x_82 = x_113;
goto block_112;
}
else
{
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_74);
x_81 = lean_box(0);
x_82 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_83 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__8));
x_84 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__9));
lean_inc_ref(x_77);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_85, 0, x_77);
x_86 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_86, 0, x_77);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_88, 0, x_80);
x_89 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_89, 0, x_79);
x_90 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_90, 0, x_78);
if (x_82 == 0)
{
lean_ctor_set(x_81, 4, x_88);
lean_ctor_set(x_81, 3, x_89);
lean_ctor_set(x_81, 2, x_90);
lean_ctor_set(x_81, 1, x_83);
lean_ctor_set(x_81, 0, x_87);
x_91 = x_81;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_111, 0, x_87);
lean_ctor_set(x_111, 1, x_83);
lean_ctor_set(x_111, 2, x_90);
lean_ctor_set(x_111, 3, x_89);
lean_ctor_set(x_111, 4, x_88);
x_91 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_92; 
if (x_76 == 0)
{
lean_ctor_set(x_75, 1, x_84);
lean_ctor_set(x_75, 0, x_91);
x_92 = x_75;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_91);
lean_ctor_set(x_109, 1, x_84);
x_92 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7);
x_94 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__16));
x_97 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_97, 0, x_95);
x_98 = l_Lean_Elab_withInfoTreeContext___redArg(x_92, x_93, x_96, x_3, x_97);
x_99 = lean_apply_9(x_98, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
lean_dec_ref(x_92);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_100 = lean_ctor_get(x_94, 0);
x_107 = !lean_is_exclusive(x_94);
if (x_107 == 0)
{
x_101 = x_94;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_94);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_withTacticInfoContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_36; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 2);
x_15 = lean_ctor_get(x_9, 3);
x_16 = lean_ctor_get(x_9, 4);
x_17 = lean_ctor_get(x_9, 5);
x_18 = lean_ctor_get(x_9, 6);
x_19 = lean_ctor_get(x_9, 7);
x_20 = lean_ctor_get(x_9, 8);
x_21 = lean_ctor_get(x_9, 9);
x_22 = lean_ctor_get(x_9, 10);
x_23 = lean_ctor_get(x_9, 11);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_25 = lean_ctor_get(x_9, 12);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_27 = lean_ctor_get(x_9, 13);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
x_28 = x_9;
x_29 = x_36;
goto block_35;
}
else
{
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
if (x_29 == 0)
{
lean_ctor_set(x_28, 5, x_30);
x_31 = x_28;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_13);
lean_ctor_set(x_34, 2, x_14);
lean_ctor_set(x_34, 3, x_15);
lean_ctor_set(x_34, 4, x_16);
lean_ctor_set(x_34, 5, x_30);
lean_ctor_set(x_34, 6, x_18);
lean_ctor_set(x_34, 7, x_19);
lean_ctor_set(x_34, 8, x_20);
lean_ctor_set(x_34, 9, x_21);
lean_ctor_set(x_34, 10, x_22);
lean_ctor_set(x_34, 11, x_23);
lean_ctor_set(x_34, 12, x_25);
lean_ctor_set(x_34, 13, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*14, x_24);
lean_ctor_set_uint8(x_34, sizeof(void*)*14 + 1, x_26);
x_31 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_32; 
x_32 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_2, x_7, x_8, x_31, x_10);
lean_dec_ref(x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__1, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___closed__1);
lean_inc(x_1);
x_16 = l_Lean_MessageData_ofSyntax(x_1);
x_17 = l_Lean_indentD(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_13, x_20);
x_22 = lean_array_fget_borrowed(x_2, x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_24, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_26 = x_25;
x_27 = x_32;
goto block_31;
}
else
{
lean_dec(x_25);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
lean_inc_ref(x_23);
if (x_27 == 0)
{
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_23);
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_23);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1));
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_22 = l_Lean_isTracingEnabledFor___redArg(x_1, x_2, x_3, x_21);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_23 = lean_apply_9(x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_64; 
x_24 = lean_ctor_get(x_23, 0);
x_64 = !lean_is_exclusive(x_23);
if (x_64 == 0)
{
x_25 = x_23;
x_26 = x_64;
goto block_63;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_64;
goto block_63;
}
block_63:
{
uint8_t x_27; 
x_27 = lean_unbox(x_24);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_4);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_28);
x_29 = x_25;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_del_object(x_25);
x_32 = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
x_34 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__2));
lean_inc(x_5);
x_35 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_34, x_5, x_33);
lean_inc(x_6);
x_36 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_34, x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_9, 4);
lean_inc(x_38);
lean_dec_ref(x_9);
x_39 = l_Lean_Meta_instAddMessageContextMetaM;
x_40 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_7);
x_41 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_8);
x_42 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_5);
x_43 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_6);
x_44 = l_Lean_addTrace___redArg(x_1, x_2, x_37, x_43, x_21, x_38);
x_45 = lean_apply_9(x_44, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, lean_box(0));
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; uint8_t x_53; 
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_45, 0);
lean_dec(x_54);
x_46 = x_45;
x_47 = x_53;
goto block_52;
}
else
{
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_4);
if (x_47 == 0)
{
lean_ctor_set(x_46, 0, x_48);
x_49 = x_46;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
x_55 = lean_ctor_get(x_45, 0);
x_62 = !lean_is_exclusive(x_45);
if (x_62 == 0)
{
x_56 = x_45;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = lean_ctor_get(x_23, 0);
x_72 = !lean_is_exclusive(x_23);
if (x_72 == 0)
{
x_66 = x_23;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_23);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
lean_object* x_21; 
x_21 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadTraceCoreM;
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_3 = l_Lean_instMonadTraceOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__0, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__0_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__0);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_3 = l_Lean_instMonadTraceOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__1, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__1_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__1);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_3 = l_Lean_instMonadTraceOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__2, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__2_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__2);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_3 = l_Lean_instMonadTraceOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__3, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__3_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__3);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_3 = l_Lean_instMonadTraceOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__4, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__4_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__4);
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_3 = l_Lean_instMonadTraceOfMonadLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_2 = l_Lean_Meta_instAddMessageContextMetaM;
x_3 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_2 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__13, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__13_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__13);
x_3 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_2 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__14, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__14_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__14);
x_3 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_2 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__15, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__15_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__15);
x_3 = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_221; 
x_38 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadTacticM___closed__1, &l_Lean_Elab_Tactic_instMonadTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
x_39 = lean_ctor_get(x_38, 0);
x_221 = !lean_is_exclusive(x_38);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_38, 1);
lean_dec(x_222);
x_40 = x_38;
x_41 = x_221;
goto block_220;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_221;
goto block_220;
}
block_37:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_saveState___redArg(x_15, x_17, x_19, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = 1;
x_25 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_1, x_24, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_array_push(x_2, x_26);
x_28 = lean_apply_10(x_4, x_27, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, lean_box(0));
return x_28;
}
else
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_25;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_22, 0);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
x_30 = x_22;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
block_220:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_218; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 2);
x_44 = lean_ctor_get(x_39, 3);
x_45 = lean_ctor_get(x_39, 4);
x_218 = !lean_is_exclusive(x_39);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_39, 1);
lean_dec(x_219);
x_46 = x_39;
x_47 = x_218;
goto block_217;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__2));
x_49 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__3));
lean_inc_ref(x_42);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_50, 0, x_42);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_51, 0, x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_53, 0, x_45);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_54, 0, x_44);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_55, 0, x_43);
if (x_47 == 0)
{
lean_ctor_set(x_46, 4, x_53);
lean_ctor_set(x_46, 3, x_54);
lean_ctor_set(x_46, 2, x_55);
lean_ctor_set(x_46, 1, x_48);
lean_ctor_set(x_46, 0, x_52);
x_56 = x_46;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_216, 0, x_52);
lean_ctor_set(x_216, 1, x_48);
lean_ctor_set(x_216, 2, x_55);
lean_ctor_set(x_216, 3, x_54);
lean_ctor_set(x_216, 4, x_53);
x_56 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_57; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 1, x_49);
lean_ctor_set(x_40, 0, x_56);
x_57 = x_40;
goto block_213;
}
else
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_56);
lean_ctor_set(x_214, 1, x_49);
x_57 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_211; 
x_58 = l_ReaderT_instMonad___redArg(x_57);
x_59 = lean_ctor_get(x_58, 0);
x_211 = !lean_is_exclusive(x_58);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_58, 1);
lean_dec(x_212);
x_60 = x_58;
x_61 = x_211;
goto block_210;
}
else
{
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_208; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 2);
x_64 = lean_ctor_get(x_59, 3);
x_65 = lean_ctor_get(x_59, 4);
x_208 = !lean_is_exclusive(x_59);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_59, 1);
lean_dec(x_209);
x_66 = x_59;
x_67 = x_208;
goto block_207;
}
else
{
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_59);
x_66 = lean_box(0);
x_67 = x_208;
goto block_207;
}
block_207:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__4));
x_69 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__5));
lean_inc_ref(x_62);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_70, 0, x_62);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_62);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_73, 0, x_65);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_74, 0, x_64);
x_75 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_75, 0, x_63);
if (x_67 == 0)
{
lean_ctor_set(x_66, 4, x_73);
lean_ctor_set(x_66, 3, x_74);
lean_ctor_set(x_66, 2, x_75);
lean_ctor_set(x_66, 1, x_68);
lean_ctor_set(x_66, 0, x_72);
x_76 = x_66;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_206, 0, x_72);
lean_ctor_set(x_206, 1, x_68);
lean_ctor_set(x_206, 2, x_75);
lean_ctor_set(x_206, 3, x_74);
lean_ctor_set(x_206, 4, x_73);
x_76 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_77; 
if (x_61 == 0)
{
lean_ctor_set(x_60, 1, x_69);
lean_ctor_set(x_60, 0, x_76);
x_77 = x_60;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_76);
lean_ctor_set(x_204, 1, x_69);
x_77 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_201; 
x_78 = l_ReaderT_instMonad___redArg(x_77);
x_79 = lean_ctor_get(x_78, 0);
x_201 = !lean_is_exclusive(x_78);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_78, 1);
lean_dec(x_202);
x_80 = x_78;
x_81 = x_201;
goto block_200;
}
else
{
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_box(0);
x_81 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_198; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 2);
x_84 = lean_ctor_get(x_79, 3);
x_85 = lean_ctor_get(x_79, 4);
x_198 = !lean_is_exclusive(x_79);
if (x_198 == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_79, 1);
lean_dec(x_199);
x_86 = x_79;
x_87 = x_198;
goto block_197;
}
else
{
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_79);
x_86 = lean_box(0);
x_87 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_88 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__6));
x_89 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__7));
lean_inc_ref(x_82);
x_90 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_90, 0, x_82);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_91, 0, x_82);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_93, 0, x_85);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_94, 0, x_84);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_95, 0, x_83);
if (x_87 == 0)
{
lean_ctor_set(x_86, 4, x_93);
lean_ctor_set(x_86, 3, x_94);
lean_ctor_set(x_86, 2, x_95);
lean_ctor_set(x_86, 1, x_88);
lean_ctor_set(x_86, 0, x_92);
x_96 = x_86;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_196, 0, x_92);
lean_ctor_set(x_196, 1, x_88);
lean_ctor_set(x_196, 2, x_95);
lean_ctor_set(x_196, 3, x_94);
lean_ctor_set(x_196, 4, x_93);
x_96 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_97; 
if (x_81 == 0)
{
lean_ctor_set(x_80, 1, x_89);
lean_ctor_set(x_80, 0, x_96);
x_97 = x_80;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_96);
lean_ctor_set(x_194, 1, x_89);
x_97 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_191; 
x_98 = l_ReaderT_instMonad___redArg(x_97);
x_99 = lean_ctor_get(x_98, 0);
x_191 = !lean_is_exclusive(x_98);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_98, 1);
lean_dec(x_192);
x_100 = x_98;
x_101 = x_191;
goto block_190;
}
else
{
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
x_101 = x_191;
goto block_190;
}
block_190:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_188; 
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_ctor_get(x_99, 2);
x_104 = lean_ctor_get(x_99, 3);
x_105 = lean_ctor_get(x_99, 4);
x_188 = !lean_is_exclusive(x_99);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_99, 1);
lean_dec(x_189);
x_106 = x_99;
x_107 = x_188;
goto block_187;
}
else
{
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_99);
x_106 = lean_box(0);
x_107 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__8));
x_109 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__9));
lean_inc_ref(x_102);
x_110 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_110, 0, x_102);
x_111 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_111, 0, x_102);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_113, 0, x_105);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_114, 0, x_104);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_115, 0, x_103);
if (x_107 == 0)
{
lean_ctor_set(x_106, 4, x_113);
lean_ctor_set(x_106, 3, x_114);
lean_ctor_set(x_106, 2, x_115);
lean_ctor_set(x_106, 1, x_108);
lean_ctor_set(x_106, 0, x_112);
x_116 = x_106;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_186, 0, x_112);
lean_ctor_set(x_186, 1, x_108);
lean_ctor_set(x_186, 2, x_115);
lean_ctor_set(x_186, 3, x_114);
lean_ctor_set(x_186, 4, x_113);
x_116 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_117; 
if (x_101 == 0)
{
lean_ctor_set(x_100, 1, x_109);
lean_ctor_set(x_100, 0, x_116);
x_117 = x_100;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_116);
lean_ctor_set(x_184, 1, x_109);
x_117 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_119 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_120 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__5, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__5_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__5);
x_121 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__12));
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1));
lean_inc_ref(x_117);
x_123 = l_Lean_isTracingEnabledFor___redArg(x_117, x_120, x_121, x_122);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_124 = lean_apply_9(x_123, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_dec_ref(x_117);
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
goto block_37;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_127 = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
x_128 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_128);
x_129 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__2));
x_130 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_129, x_119, x_128);
x_131 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_129, x_118, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc_ref(x_132);
lean_dec_ref(x_131);
x_133 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16);
lean_inc_ref(x_3);
x_134 = l_Lean_Exception_toMessageData(x_3);
x_135 = l_Lean_addTrace___redArg(x_117, x_120, x_132, x_133, x_122, x_134);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_136 = lean_apply_9(x_135, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_136) == 0)
{
lean_dec_ref(x_136);
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
goto block_37;
}
else
{
lean_dec_ref(x_3);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_144; 
lean_dec_ref(x_3);
lean_dec_ref(x_117);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_137 = lean_ctor_get(x_124, 0);
x_144 = !lean_is_exclusive(x_124);
if (x_144 == 0)
{
x_138 = x_124;
x_139 = x_144;
goto block_143;
}
else
{
lean_inc(x_137);
lean_dec(x_124);
x_138 = lean_box(0);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_139 == 0)
{
x_140 = x_138;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_137);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_3, 0);
x_146 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_147 = l_Lean_instBEqInternalExceptionId_beq(x_145, x_146);
x_148 = 1;
if (x_147 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = l_Lean_Elab_abortTacticExceptionId;
x_150 = l_Lean_instBEqInternalExceptionId_beq(x_145, x_149);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec_ref(x_117);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_3);
return x_151;
}
else
{
lean_object* x_152; 
x_152 = l_Lean_Core_getMessageLog___redArg(x_12);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = l_Lean_MessageLog_toList(x_153);
lean_dec(x_153);
x_155 = lean_box(0);
lean_inc_ref(x_117);
x_156 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___boxed), 20, 8);
lean_closure_set(x_156, 0, x_117);
lean_closure_set(x_156, 1, x_120);
lean_closure_set(x_156, 2, x_121);
lean_closure_set(x_156, 3, x_155);
lean_closure_set(x_156, 4, x_119);
lean_closure_set(x_156, 5, x_118);
lean_closure_set(x_156, 6, x_119);
lean_closure_set(x_156, 7, x_118);
x_157 = l_List_forIn_x27_loop___redArg(x_117, x_156, x_154, x_155);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_158 = lean_apply_9(x_157, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
lean_dec_ref(x_158);
x_159 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_12);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_1, x_148, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec_ref(x_161);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_3);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_array_push(x_2, x_162);
x_164 = lean_apply_10(x_4, x_163, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_164;
}
else
{
lean_dec(x_160);
lean_dec_ref(x_3);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_161;
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_dec_ref(x_3);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_159, 0);
x_172 = !lean_is_exclusive(x_159);
if (x_172 == 0)
{
x_166 = x_159;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_dec(x_159);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_165);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_158;
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_180; 
lean_dec_ref(x_3);
lean_dec_ref(x_117);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_173 = lean_ctor_get(x_152, 0);
x_180 = !lean_is_exclusive(x_152);
if (x_180 == 0)
{
x_174 = x_152;
x_175 = x_180;
goto block_179;
}
else
{
lean_inc(x_173);
lean_dec(x_152);
x_174 = lean_box(0);
x_175 = x_180;
goto block_179;
}
block_179:
{
lean_object* x_176; 
if (x_175 == 0)
{
x_176 = x_174;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_173);
x_176 = x_178;
goto block_177;
}
block_177:
{
return x_176;
}
}
}
}
}
else
{
lean_object* x_181; 
lean_dec_ref(x_3);
lean_dec_ref(x_117);
x_181 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_1, x_148, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
lean_dec_ref(x_181);
x_182 = lean_apply_10(x_4, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_182;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_181;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg___closed__0));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(x_1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Elab_builtinIncrementalElabs;
x_5 = lean_st_ref_get(x_4);
x_6 = l_Lean_NameSet_contains(x_5, x_1);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_incrementalAttr;
x_10 = l_Lean_TagAttribute_hasTag(x_9, x_8, x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_box(x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___redArg(x_1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__0(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_70; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
x_20 = lean_ctor_get(x_5, 5);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 3);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 4);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 5);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 6);
x_26 = lean_ctor_get(x_5, 6);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 7);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 8);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 9);
x_30 = lean_ctor_get(x_5, 7);
x_70 = !lean_is_exclusive(x_5);
if (x_70 == 0)
{
x_31 = x_5;
x_32 = x_70;
goto block_69;
}
else
{
lean_inc(x_30);
lean_inc(x_26);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_31 = lean_box(0);
x_32 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_33; uint8_t x_39; 
if (lean_obj_tag(x_26) == 0)
{
x_33 = x_26;
goto block_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_box(x_1);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_45, 0, x_44);
if (lean_obj_tag(x_43) == 1)
{
if (x_1 == 0)
{
lean_dec_ref(x_45);
goto block_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_12, 0);
x_51 = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__1));
x_52 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_50, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_45);
goto block_48;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
if (lean_obj_tag(x_53) == 1)
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_53, 0);
lean_dec_ref(x_53);
if (x_54 == 0)
{
lean_dec_ref(x_45);
goto block_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_56, 0, x_45);
x_57 = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___closed__2));
x_58 = lean_box(0);
x_59 = 0;
lean_inc(x_55);
x_60 = l_Lean_Syntax_formatStx(x_55, x_58, x_59);
x_61 = l_Std_Format_defWidth;
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Std_Format_pretty(x_60, x_61, x_62, x_62);
x_64 = lean_string_append(x_57, x_63);
lean_dec_ref(x_63);
x_65 = lean_dbg_trace(x_64, x_56);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
x_39 = x_66;
goto block_41;
}
}
else
{
lean_dec(x_53);
lean_dec_ref(x_45);
goto block_48;
}
}
}
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_dec_ref(x_45);
x_67 = lean_box(0);
x_68 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__0(x_1, x_67);
x_39 = x_68;
goto block_41;
}
block_48:
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___lam__0(x_1, x_46);
x_39 = x_47;
goto block_41;
}
}
block_38:
{
lean_object* x_34; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 6, x_33);
x_34 = x_31;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 2, x_17);
lean_ctor_set(x_37, 3, x_18);
lean_ctor_set(x_37, 4, x_19);
lean_ctor_set(x_37, 5, x_20);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_15);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 1, x_16);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 2, x_21);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 3, x_22);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 4, x_23);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 5, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 6, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 7, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 8, x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 9, x_29);
x_34 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_35; 
x_35 = lean_apply_9(x_2, x_3, x_4, x_34, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_35;
}
}
block_41:
{
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_26);
x_40 = lean_box(0);
x_33 = x_40;
goto block_38;
}
else
{
x_33 = x_26;
goto block_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqExtraModUse_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_admitGoal_spec__0_spec__0_spec__2___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqExtraModUse_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableExtraModUse_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___closed__0));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__1));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__1));
x_2 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__0));
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__3(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__3);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__4);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_65; uint8_t x_66; 
x_13 = lean_st_ref_get(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*8);
lean_dec_ref(x_14);
x_16 = lean_st_ref_get(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__2);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*1 + 1, x_2);
x_20 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_21 = lean_box(1);
x_22 = lean_box(0);
x_65 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_18, x_20, x_17, x_21, x_22);
x_66 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___redArg(x_65, x_19);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_75; lean_object* x_76; uint8_t x_89; 
x_67 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__8));
x_68 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(x_67, x_10);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_89 = lean_unbox(x_69);
lean_dec(x_69);
if (x_89 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_23 = x_9;
x_24 = x_11;
goto block_64;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__15);
if (x_15 == 0)
{
lean_object* x_99; 
x_99 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__20));
x_91 = x_99;
goto block_98;
}
else
{
lean_object* x_100; 
x_100 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__21));
x_91 = x_100;
goto block_98;
}
block_98:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = l_Lean_stringToMessageData(x_91);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__17);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
if (x_2 == 0)
{
lean_object* x_96; 
x_96 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__18));
x_75 = x_95;
x_76 = x_96;
goto block_88;
}
else
{
lean_object* x_97; 
x_97 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__19));
x_75 = x_95;
x_76 = x_97;
goto block_88;
}
}
}
block_74:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(x_67, x_72, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_73) == 0)
{
lean_dec_ref(x_73);
x_23 = x_9;
x_24 = x_11;
goto block_64;
}
else
{
lean_dec_ref(x_19);
return x_73;
}
}
block_88:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_77 = l_Lean_stringToMessageData(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__10);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_MessageData_ofName(x_1);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Name_isAnonymous(x_3);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__12);
x_85 = l_Lean_MessageData_ofName(x_3);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_70 = x_82;
x_71 = x_86;
goto block_74;
}
else
{
lean_object* x_87; 
lean_dec(x_3);
x_87 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__13);
x_70 = x_82;
x_71 = x_87;
goto block_74;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_19);
lean_dec(x_3);
lean_dec(x_1);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
block_64:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_62; 
x_25 = lean_st_ref_take(x_24);
x_26 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 2);
x_30 = lean_ctor_get(x_25, 3);
x_31 = lean_ctor_get(x_25, 4);
x_32 = lean_ctor_get(x_25, 6);
x_33 = lean_ctor_get(x_25, 7);
x_34 = lean_ctor_get(x_25, 8);
x_62 = !lean_is_exclusive(x_25);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_25, 5);
lean_dec(x_63);
x_35 = x_25;
x_36 = x_62;
goto block_61;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_35 = lean_box(0);
x_36 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_26, 2);
lean_inc(x_37);
lean_dec_ref(x_26);
x_38 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_20, x_27, x_19, x_37, x_22);
lean_dec(x_37);
x_39 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__5);
if (x_36 == 0)
{
lean_ctor_set(x_35, 5, x_39);
lean_ctor_set(x_35, 0, x_38);
x_40 = x_35;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_60, 0, x_38);
lean_ctor_set(x_60, 1, x_28);
lean_ctor_set(x_60, 2, x_29);
lean_ctor_set(x_60, 3, x_30);
lean_ctor_set(x_60, 4, x_31);
lean_ctor_set(x_60, 5, x_39);
lean_ctor_set(x_60, 6, x_32);
lean_ctor_set(x_60, 7, x_33);
lean_ctor_set(x_60, 8, x_34);
x_40 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_57; 
x_41 = lean_st_ref_set(x_24, x_40);
x_42 = lean_st_ref_take(x_23);
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_ctor_get(x_42, 2);
x_45 = lean_ctor_get(x_42, 3);
x_46 = lean_ctor_get(x_42, 4);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_42, 1);
lean_dec(x_58);
x_47 = x_42;
x_48 = x_57;
goto block_56;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___closed__6);
if (x_48 == 0)
{
lean_ctor_set(x_47, 1, x_49);
x_50 = x_47;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_49);
lean_ctor_set(x_55, 2, x_44);
lean_ctor_set(x_55, 3, x_45);
lean_ctor_set(x_55, 4, x_46);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_st_ref_set(x_23, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_18 = l_Lean_Environment_header(x_1);
x_19 = lean_ctor_get(x_18, 3);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_instInhabitedEffectiveImport_default;
x_21 = lean_array_uget_borrowed(x_3, x_5);
x_22 = lean_array_get(x_20, x_19, x_21);
lean_dec_ref(x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = 0;
lean_inc(x_2);
x_26 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4(x_24, x_25, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec_ref(x_26);
x_27 = lean_box(0);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_6 = x_27;
goto _start;
}
else
{
lean_dec(x_2);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__5(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___redArg(x_2, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__1));
x_2 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_31; 
x_12 = lean_st_ref_get(x_10);
x_16 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_16);
lean_dec(x_12);
x_31 = l_Lean_Environment_getModuleIdxFor_x3f(x_16, x_1);
if (lean_obj_tag(x_31) == 0)
{
lean_dec_ref(x_16);
lean_dec(x_1);
goto block_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Environment_header(x_16);
x_34 = lean_ctor_get(x_33, 3);
lean_inc_ref(x_34);
lean_dec_ref(x_33);
x_35 = lean_array_get_size(x_34);
x_36 = lean_nat_dec_lt(x_32, x_35);
if (x_36 == 0)
{
lean_dec_ref(x_34);
lean_dec(x_32);
lean_dec_ref(x_16);
lean_dec(x_1);
goto block_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_st_ref_get(x_10);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
lean_dec(x_37);
x_39 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__2);
x_40 = lean_array_fget(x_34, x_32);
lean_dec(x_32);
lean_dec_ref(x_34);
if (x_2 == 0)
{
lean_dec_ref(x_38);
x_41 = x_2;
goto block_52;
}
else
{
uint8_t x_53; 
lean_inc(x_1);
x_53 = l_Lean_isMarkedMeta(x_38, x_1);
if (x_53 == 0)
{
x_41 = x_2;
goto block_52;
}
else
{
uint8_t x_54; 
x_54 = 0;
x_41 = x_54;
goto block_52;
}
}
block_52:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_1);
x_44 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4(x_43, x_41, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_44);
x_45 = l_Lean_indirectModUseExt;
x_46 = lean_box(1);
x_47 = lean_box(0);
lean_inc_ref(x_16);
x_48 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_39, x_45, x_16, x_46, x_47);
x_49 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg(x_48, x_1);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___closed__3));
x_17 = x_50;
goto block_30;
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec_ref(x_49);
x_17 = x_51;
goto block_30;
}
}
else
{
lean_dec_ref(x_16);
lean_dec(x_1);
return x_44;
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_30:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_box(0);
x_19 = lean_array_size(x_17);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__5(x_16, x_1, x_17, x_19, x_20, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_22 = x_21;
x_23 = x_28;
goto block_27;
}
else
{
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_18);
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_18);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = lean_apply_10(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_24; 
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_15 = x_14;
x_16 = x_24;
goto block_23;
}
else
{
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = x_24;
goto block_23;
}
block_23:
{
if (x_3 == 0)
{
uint8_t x_17; lean_object* x_18; 
lean_del_object(x_15);
x_17 = 1;
x_18 = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4(x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_19 = lean_box(0);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__0(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
x_14 = x_12;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_2);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_12, 0);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
x_23 = x_12;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_get(x_1);
x_14 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_14);
lean_inc(x_1);
x_16 = lean_apply_10(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_55; 
x_17 = lean_ctor_get(x_16, 0);
x_55 = !lean_is_exclusive(x_16);
if (x_55 == 0)
{
x_18 = x_16;
x_19 = x_55;
goto block_54;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_53; 
x_20 = lean_st_ref_take(x_1);
x_21 = lean_ctor_get(x_20, 7);
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_20, 2);
x_25 = lean_ctor_get(x_20, 3);
x_26 = lean_ctor_get(x_20, 4);
x_27 = lean_ctor_get(x_20, 5);
x_28 = lean_ctor_get(x_20, 6);
x_29 = lean_ctor_get(x_20, 8);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
x_30 = x_20;
x_31 = x_53;
goto block_52;
}
else
{
lean_inc(x_29);
lean_inc(x_21);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = x_53;
goto block_52;
}
block_52:
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_50; 
x_32 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
x_50 = !lean_is_exclusive(x_21);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_21, 2);
lean_dec(x_51);
x_35 = x_21;
x_36 = x_50;
goto block_49;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = lean_box(0);
x_36 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_PersistentArray_push___redArg(x_10, x_17);
if (x_36 == 0)
{
lean_ctor_set(x_35, 2, x_37);
x_38 = x_35;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_34);
lean_ctor_set(x_48, 2, x_37);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_32);
x_38 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_39; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 7, x_38);
x_39 = x_30;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_22);
lean_ctor_set(x_46, 1, x_23);
lean_ctor_set(x_46, 2, x_24);
lean_ctor_set(x_46, 3, x_25);
lean_ctor_set(x_46, 4, x_26);
lean_ctor_set(x_46, 5, x_27);
lean_ctor_set(x_46, 6, x_28);
lean_ctor_set(x_46, 7, x_38);
lean_ctor_set(x_46, 8, x_29);
x_39 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_st_ref_set(x_1, x_39);
lean_dec(x_1);
x_41 = lean_box(0);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_41);
x_42 = x_18;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec_ref(x_10);
lean_dec(x_1);
x_56 = lean_ctor_get(x_16, 0);
x_63 = !lean_is_exclusive(x_16);
if (x_63 == 0)
{
x_57 = x_16;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_16);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__1(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__0);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_36; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 7);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = lean_ctor_get(x_6, 7);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
x_12 = lean_ctor_get(x_6, 4);
x_13 = lean_ctor_get(x_6, 5);
x_14 = lean_ctor_get(x_6, 6);
x_15 = lean_ctor_get(x_6, 8);
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
x_16 = x_6;
x_17 = x_36;
goto block_35;
}
else
{
lean_inc(x_15);
lean_inc(x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_33; 
x_18 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_7, 2);
lean_dec(x_34);
x_21 = x_7;
x_22 = x_33;
goto block_32;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___closed__1);
if (x_22 == 0)
{
lean_ctor_set(x_21, 2, x_23);
x_24 = x_21;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_18);
x_24 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_25; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 7, x_24);
x_25 = x_16;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_10);
lean_ctor_set(x_29, 3, x_11);
lean_ctor_set(x_29, 4, x_12);
lean_ctor_set(x_29, 5, x_13);
lean_ctor_set(x_29, 6, x_14);
lean_ctor_set(x_29, 7, x_24);
lean_ctor_set(x_29, 8, x_15);
x_25 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_st_ref_set(x_1, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_5);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_st_ref_get(x_10);
x_13 = lean_ctor_get(x_12, 7);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
lean_dec_ref(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_2);
x_15 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_18 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_43; 
x_19 = lean_ctor_get(x_18, 0);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
x_20 = x_18;
x_21 = x_43;
goto block_42;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_22; 
lean_inc(x_19);
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 1);
x_22 = x_20;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_19);
x_22 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_23; 
x_23 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_22);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_30; 
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
x_24 = x_23;
x_25 = x_30;
goto block_29;
}
else
{
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_19);
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_19);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_19);
x_32 = lean_ctor_get(x_23, 0);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
x_33 = x_23;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_18, 0);
lean_inc(x_44);
lean_dec_ref(x_18);
x_45 = lean_box(0);
x_46 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___lam__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_46, 0);
lean_dec(x_54);
x_47 = x_46;
x_48 = x_53;
goto block_52;
}
else
{
lean_dec(x_46);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_44);
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_44);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec(x_44);
x_55 = lean_ctor_get(x_46, 0);
x_62 = !lean_is_exclusive(x_46);
if (x_62 == 0)
{
x_56 = x_46;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_32; 
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
x_14 = x_4;
x_15 = x_32;
goto block_31;
}
else
{
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_1);
x_16 = x_14;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_13);
x_16 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_2, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__1___boxed), 11, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_3, x_19, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_21 = lean_ctor_get(x_17, 0);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
x_22 = x_17;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1));
x_16 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(x_15, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_box(0);
x_19 = lean_unbox(x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_dec(x_13);
x_1 = x_14;
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 4);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(x_15, x_21, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
x_1 = x_14;
x_2 = x_18;
goto _start;
}
else
{
lean_dec(x_14);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_2);
x_14 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_129; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_129 = !lean_is_exclusive(x_3);
if (x_129 == 0)
{
x_17 = x_3;
x_18 = x_129;
goto block_128;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_99; lean_object* x_100; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_106 = lean_ctor_get(x_15, 1);
lean_inc(x_106);
lean_dec(x_15);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec_ref(x_104);
lean_inc(x_107);
x_108 = l_Lean_Elab_isIncrementalElab___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__3___redArg(x_107, x_12);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_117; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_box(x_105);
lean_inc(x_107);
lean_inc(x_1);
x_111 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__0___boxed), 13, 4);
lean_closure_set(x_111, 0, x_106);
lean_closure_set(x_111, 1, x_1);
lean_closure_set(x_111, 2, x_110);
lean_closure_set(x_111, 3, x_107);
lean_inc(x_1);
x_112 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__2___boxed), 12, 3);
lean_closure_set(x_112, 0, x_107);
lean_closure_set(x_112, 1, x_1);
lean_closure_set(x_112, 2, x_111);
x_117 = lean_unbox(x_109);
lean_dec(x_109);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = 1;
x_113 = x_118;
goto block_116;
}
else
{
uint8_t x_119; 
x_119 = 0;
x_113 = x_119;
goto block_116;
}
block_116:
{
lean_object* x_114; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_114 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg(x_113, x_112, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_114) == 0)
{
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_114;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_99 = x_114;
x_100 = x_115;
goto block_103;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_127; 
lean_dec(x_107);
lean_dec(x_106);
x_120 = lean_ctor_get(x_108, 0);
x_127 = !lean_is_exclusive(x_108);
if (x_127 == 0)
{
x_121 = x_108;
x_122 = x_127;
goto block_126;
}
else
{
lean_inc(x_120);
lean_dec(x_108);
x_121 = lean_box(0);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
lean_inc(x_120);
if (x_122 == 0)
{
x_123 = x_121;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
x_123 = x_125;
goto block_124;
}
block_124:
{
x_99 = x_123;
x_100 = x_120;
goto block_103;
}
}
}
block_45:
{
lean_object* x_28; 
x_28 = l_Lean_Elab_Tactic_saveState___redArg(x_21, x_23, x_25, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = 1;
lean_inc_ref(x_2);
x_31 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_2, x_30, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec_ref(x_31);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 1, x_29);
lean_ctor_set(x_17, 0, x_19);
x_32 = x_17;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_29);
x_32 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_33; 
x_33 = lean_array_push(x_4, x_32);
x_3 = x_16;
x_4 = x_33;
x_5 = x_20;
x_6 = x_21;
x_7 = x_22;
x_8 = x_23;
x_9 = x_24;
x_10 = x_25;
x_11 = x_26;
x_12 = x_27;
goto _start;
}
}
else
{
lean_dec(x_29);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_del_object(x_17);
lean_dec(x_16);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_31;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_del_object(x_17);
lean_dec(x_16);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_28, 0);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
x_38 = x_28;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
block_98:
{
if (x_48 == 0)
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_46);
x_49 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1));
x_50 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(x_49, x_11);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
x_19 = x_47;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
goto block_45;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_inc_ref(x_47);
x_53 = l_Lean_Exception_toMessageData(x_47);
x_54 = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(x_49, x_53, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_19 = x_47;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
goto block_45;
}
else
{
lean_dec_ref(x_47);
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_47);
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_50, 0);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
x_56 = x_50;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_50);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
lean_del_object(x_17);
x_63 = lean_ctor_get(x_47, 0);
x_64 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_65 = l_Lean_instBEqInternalExceptionId_beq(x_63, x_64);
x_66 = 1;
if (x_65 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = l_Lean_Elab_abortTacticExceptionId;
x_68 = l_Lean_instBEqInternalExceptionId_beq(x_63, x_67);
if (x_68 == 0)
{
lean_dec_ref(x_47);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_46;
}
else
{
lean_object* x_69; 
lean_dec_ref(x_46);
x_69 = l_Lean_Core_getMessageLog___redArg(x_12);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_MessageLog_toList(x_70);
lean_dec(x_70);
x_72 = lean_box(0);
x_73 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___redArg(x_71, x_72, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_dec_ref(x_73);
x_74 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_12);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
lean_inc_ref(x_2);
x_76 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_2, x_66, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_47);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_4, x_77);
x_3 = x_16;
x_4 = x_78;
goto _start;
}
else
{
lean_dec(x_75);
lean_dec_ref(x_47);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_76;
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_dec_ref(x_47);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_74, 0);
x_87 = !lean_is_exclusive(x_74);
if (x_87 == 0)
{
x_81 = x_74;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
else
{
lean_dec_ref(x_47);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_73;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec_ref(x_47);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_88 = lean_ctor_get(x_69, 0);
x_95 = !lean_is_exclusive(x_69);
if (x_95 == 0)
{
x_89 = x_69;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_69);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
}
else
{
lean_object* x_96; 
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_inc_ref(x_2);
x_96 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_2, x_66, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_96) == 0)
{
lean_dec_ref(x_96);
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_96;
}
}
}
}
else
{
lean_dec_ref(x_47);
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_46;
}
}
block_103:
{
uint8_t x_101; 
x_101 = l_Lean_Exception_isInterrupt(x_100);
if (x_101 == 0)
{
uint8_t x_102; 
lean_inc_ref(x_100);
x_102 = l_Lean_Exception_isRuntime(x_100);
x_46 = x_99;
x_47 = x_100;
x_48 = x_102;
goto block_98;
}
else
{
x_46 = x_99;
x_47 = x_100;
x_48 = x_101;
goto block_98;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___redArg(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__6_spec__9(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4_spec__4_spec__6_spec__9_spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_instInhabitedTacticParsedSnapshot_default;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_apply_8(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = l_Lean_profileitIOUnsafe___redArg(x_1, x_2, x_14, x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__0);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_34; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = lean_ctor_get(x_6, 4);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_ctor_get(x_6, 6);
x_14 = lean_ctor_get(x_6, 7);
x_15 = lean_ctor_get(x_6, 8);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
x_16 = x_6;
x_17 = x_34;
goto block_33;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_34;
goto block_33;
}
block_33:
{
uint64_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_31; 
x_18 = lean_ctor_get_uint64(x_7, sizeof(void*)*1);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_7, 0);
lean_dec(x_32);
x_19 = x_7;
x_20 = x_31;
goto block_30;
}
else
{
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set_uint64(x_29, sizeof(void*)*1, x_18);
x_22 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_23; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_22);
x_23 = x_16;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_10);
lean_ctor_set(x_27, 3, x_11);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_12);
lean_ctor_set(x_27, 6, x_13);
lean_ctor_set(x_27, 7, x_14);
lean_ctor_set(x_27, 8, x_15);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_st_ref_set(x_1, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__1___boxed), 11, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_16 = lean_ctor_get(x_12, 0);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
x_17 = x_12;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTactic___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__9(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
x_4 = x_1;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_12 = x_1;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7_spec__10(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7_spec__10(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_80; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 8);
x_19 = lean_ctor_get(x_7, 9);
x_20 = lean_ctor_get(x_7, 10);
x_21 = lean_ctor_get(x_7, 11);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_7, 13);
x_80 = !lean_is_exclusive(x_7);
if (x_80 == 0)
{
x_26 = x_7;
x_27 = x_80;
goto block_79;
}
else
{
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_st_ref_get(x_8);
x_29 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_replaceRef(x_3, x_15);
lean_dec(x_15);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_31);
x_32 = x_26;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_11);
lean_ctor_set(x_78, 2, x_12);
lean_ctor_set(x_78, 3, x_13);
lean_ctor_set(x_78, 4, x_14);
lean_ctor_set(x_78, 5, x_31);
lean_ctor_set(x_78, 6, x_16);
lean_ctor_set(x_78, 7, x_17);
lean_ctor_set(x_78, 8, x_18);
lean_ctor_set(x_78, 9, x_19);
lean_ctor_set(x_78, 10, x_20);
lean_ctor_set(x_78, 11, x_21);
lean_ctor_set(x_78, 12, x_23);
lean_ctor_set(x_78, 13, x_25);
lean_ctor_set_uint8(x_78, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_78, sizeof(void*)*14 + 1, x_24);
x_32 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_76; 
x_33 = l_Lean_PersistentArray_toArray___redArg(x_30);
lean_dec_ref(x_30);
x_34 = lean_array_size(x_33);
x_35 = 0;
x_36 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7_spec__10(x_34, x_35, x_33);
x_37 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3(x_37, x_5, x_6, x_32, x_8);
lean_dec_ref(x_32);
x_39 = lean_ctor_get(x_38, 0);
x_76 = !lean_is_exclusive(x_38);
if (x_76 == 0)
{
x_40 = x_38;
x_41 = x_76;
goto block_75;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_74; 
x_42 = lean_st_ref_take(x_8);
x_43 = lean_ctor_get(x_42, 4);
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_42, 2);
x_47 = lean_ctor_get(x_42, 3);
x_48 = lean_ctor_get(x_42, 5);
x_49 = lean_ctor_get(x_42, 6);
x_50 = lean_ctor_get(x_42, 7);
x_51 = lean_ctor_get(x_42, 8);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
x_52 = x_42;
x_53 = x_74;
goto block_73;
}
else
{
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_43);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = x_74;
goto block_73;
}
block_73:
{
uint64_t x_54; lean_object* x_55; uint8_t x_56; uint8_t x_71; 
x_54 = lean_ctor_get_uint64(x_43, sizeof(void*)*1);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_43, 0);
lean_dec(x_72);
x_55 = x_43;
x_56 = x_71;
goto block_70;
}
else
{
lean_dec(x_43);
x_55 = lean_box(0);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_39);
x_58 = l_Lean_PersistentArray_push___redArg(x_1, x_57);
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_58);
x_59 = x_55;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_54);
x_59 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_60; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 4, x_59);
x_60 = x_52;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_44);
lean_ctor_set(x_67, 1, x_45);
lean_ctor_set(x_67, 2, x_46);
lean_ctor_set(x_67, 3, x_47);
lean_ctor_set(x_67, 4, x_59);
lean_ctor_set(x_67, 5, x_48);
lean_ctor_set(x_67, 6, x_49);
lean_ctor_set(x_67, 7, x_50);
lean_ctor_set(x_67, 8, x_51);
x_60 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_st_ref_set(x_8, x_60);
x_62 = lean_box(0);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_62);
x_63 = x_40;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__2(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_59; double x_90; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec_ref(x_8);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_dec(x_19);
x_44 = l_Lean_trace_profiler;
x_45 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(x_4, x_44);
if (x_45 == 0)
{
x_59 = x_45;
goto block_89;
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = l_Lean_trace_profiler_useHeartbeats;
x_97 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(x_4, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; double x_100; double x_101; double x_102; 
x_98 = l_Lean_trace_profiler_threshold;
x_99 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__9(x_4, x_98);
x_100 = lean_float_of_nat(x_99);
x_101 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__2);
x_102 = lean_float_div(x_100, x_101);
x_90 = x_102;
goto block_95;
}
else
{
lean_object* x_103; lean_object* x_104; double x_105; 
x_103 = l_Lean_trace_profiler_threshold;
x_104 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__9(x_4, x_103);
x_105 = lean_float_of_nat(x_104);
x_90 = x_105;
goto block_95;
}
}
block_41:
{
lean_object* x_31; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
x_31 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___redArg(x_6, x_22, x_20, x_21, x_27, x_28, x_29, x_30);
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec_ref(x_31);
x_32 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___redArg(x_18);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_18);
x_33 = lean_ctor_get(x_31, 0);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
x_34 = x_31;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
block_53:
{
double x_48; lean_object* x_49; 
x_48 = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg___closed__0);
lean_inc_ref(x_3);
lean_inc(x_1);
x_49 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set_float(x_49, sizeof(void*)*2, x_48);
lean_ctor_set_float(x_49, sizeof(void*)*2 + 8, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2 + 16, x_2);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_3);
lean_dec(x_1);
x_20 = x_46;
x_21 = x_47;
x_22 = x_49;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
x_29 = x_15;
x_30 = x_16;
goto block_41;
}
else
{
lean_object* x_50; double x_51; double x_52; 
lean_dec_ref(x_49);
x_50 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_3);
x_51 = lean_unbox_float(x_42);
lean_dec(x_42);
lean_ctor_set_float(x_50, sizeof(void*)*2, x_51);
x_52 = lean_unbox_float(x_43);
lean_dec(x_43);
lean_ctor_set_float(x_50, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_50, sizeof(void*)*2 + 16, x_2);
x_20 = x_46;
x_21 = x_47;
x_22 = x_50;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
x_29 = x_15;
x_30 = x_16;
goto block_41;
}
}
block_58:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_15, 5);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_18);
x_55 = lean_apply_10(x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, lean_box(0));
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_54);
x_46 = x_54;
x_47 = x_56;
goto block_53;
}
else
{
lean_object* x_57; 
lean_dec_ref(x_55);
x_57 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___closed__1);
lean_inc(x_54);
x_46 = x_54;
x_47 = x_57;
goto block_53;
}
}
block_89:
{
if (x_5 == 0)
{
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_88; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_60 = lean_st_ref_take(x_16);
x_61 = lean_ctor_get(x_60, 4);
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
x_64 = lean_ctor_get(x_60, 2);
x_65 = lean_ctor_get(x_60, 3);
x_66 = lean_ctor_get(x_60, 5);
x_67 = lean_ctor_get(x_60, 6);
x_68 = lean_ctor_get(x_60, 7);
x_69 = lean_ctor_get(x_60, 8);
x_88 = !lean_is_exclusive(x_60);
if (x_88 == 0)
{
x_70 = x_60;
x_71 = x_88;
goto block_87;
}
else
{
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_61);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_70 = lean_box(0);
x_71 = x_88;
goto block_87;
}
block_87:
{
uint64_t x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_86; 
x_72 = lean_ctor_get_uint64(x_61, sizeof(void*)*1);
x_73 = lean_ctor_get(x_61, 0);
x_86 = !lean_is_exclusive(x_61);
if (x_86 == 0)
{
x_74 = x_61;
x_75 = x_86;
goto block_85;
}
else
{
lean_inc(x_73);
lean_dec(x_61);
x_74 = lean_box(0);
x_75 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_PersistentArray_append___redArg(x_6, x_73);
lean_dec_ref(x_73);
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_76);
x_77 = x_74;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set_uint64(x_84, sizeof(void*)*1, x_72);
x_77 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_78; 
if (x_71 == 0)
{
lean_ctor_set(x_70, 4, x_77);
x_78 = x_70;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_82, 0, x_62);
lean_ctor_set(x_82, 1, x_63);
lean_ctor_set(x_82, 2, x_64);
lean_ctor_set(x_82, 3, x_65);
lean_ctor_set(x_82, 4, x_77);
lean_ctor_set(x_82, 5, x_66);
lean_ctor_set(x_82, 6, x_67);
lean_ctor_set(x_82, 7, x_68);
lean_ctor_set(x_82, 8, x_69);
x_78 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_st_ref_set(x_16, x_78);
lean_dec(x_16);
x_80 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___redArg(x_18);
return x_80;
}
}
}
}
}
else
{
goto block_58;
}
}
else
{
goto block_58;
}
}
block_95:
{
double x_91; double x_92; double x_93; uint8_t x_94; 
x_91 = lean_unbox_float(x_43);
x_92 = lean_unbox_float(x_42);
x_93 = lean_float_sub(x_91, x_92);
x_94 = lean_float_decLt(x_90, x_93);
x_59 = x_94;
goto block_89;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_2);
x_19 = lean_unbox(x_5);
x_20 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg(x_1, x_18, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_4);
return x_20;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__3);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_MessageData_ofSyntax(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTactic___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_8 = x_5;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_7);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_45; 
x_17 = lean_ctor_get(x_6, 0);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
x_18 = x_6;
x_19 = x_45;
goto block_44;
}
else
{
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
lean_del_object(x_18);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec_ref(x_5);
x_22 = lean_ctor_get(x_20, 0);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
x_23 = x_20;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___redArg(x_25, x_21);
lean_dec_ref(x_25);
return x_26;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_20, 0);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
x_33 = x_20;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_32);
x_35 = x_18;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_32);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_35);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___redArg(x_36, x_31);
lean_dec_ref(x_36);
return x_37;
}
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
x_48 = x_5;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_Environment_setExporting(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_6, x_2);
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Environment_contains(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_privateToUserName(x_2);
x_11 = l_Lean_Environment_contains(x_6, x_10, x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__3(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = 1;
x_16 = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4(x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = lean_box(0);
x_1 = x_14;
x_2 = x_17;
goto _start;
}
else
{
lean_dec(x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_26; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_11);
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(x_11, x_4);
x_14 = lean_ctor_get(x_13, 0);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
x_15 = x_13;
x_16 = x_26;
goto block_25;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_26;
goto block_25;
}
block_25:
{
uint8_t x_17; 
x_17 = lean_unbox(x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_del_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_1 = x_10;
goto _start;
}
else
{
lean_object* x_19; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 0, x_12);
x_19 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_12);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_MessageData_ofFormat(x_19);
x_21 = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(x_11, x_20, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
x_1 = x_10;
goto _start;
}
else
{
lean_dec(x_10);
return x_21;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_11 = lean_st_ref_get(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_ctor_get(x_8, 3);
x_15 = lean_ctor_get(x_8, 4);
x_16 = lean_ctor_get(x_8, 5);
x_17 = lean_ctor_get(x_8, 6);
x_18 = lean_ctor_get(x_8, 7);
x_19 = lean_ctor_get(x_8, 10);
x_20 = lean_ctor_get(x_8, 11);
x_21 = lean_st_ref_get(x_9);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc_ref(x_12);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_23, 0, x_12);
lean_inc_ref(x_12);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_24, 0, x_12);
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_12);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(x_25, 0, x_12);
lean_closure_set(x_25, 1, x_17);
lean_closure_set(x_25, 2, x_18);
lean_inc(x_17);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_26, 0, x_17);
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_13);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_27, 0, x_12);
lean_closure_set(x_27, 1, x_13);
lean_closure_set(x_27, 2, x_17);
lean_closure_set(x_27, 3, x_18);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_27);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_20);
lean_inc(x_19);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_20);
lean_ctor_set(x_29, 3, x_14);
lean_ctor_set(x_29, 4, x_15);
lean_ctor_set(x_29, 5, x_16);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_apply_2(x_1, x_29, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 2);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___redArg(x_37, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_74; 
lean_dec_ref(x_39);
x_40 = lean_st_ref_take(x_9);
x_41 = lean_ctor_get(x_40, 0);
x_42 = lean_ctor_get(x_40, 2);
x_43 = lean_ctor_get(x_40, 3);
x_44 = lean_ctor_get(x_40, 4);
x_45 = lean_ctor_get(x_40, 5);
x_46 = lean_ctor_get(x_40, 6);
x_47 = lean_ctor_get(x_40, 7);
x_48 = lean_ctor_get(x_40, 8);
x_74 = !lean_is_exclusive(x_40);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_40, 1);
lean_dec(x_75);
x_49 = x_40;
x_50 = x_74;
goto block_73;
}
else
{
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_40);
x_49 = lean_box(0);
x_50 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_51; 
if (x_50 == 0)
{
lean_ctor_set(x_49, 1, x_35);
x_51 = x_49;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_72, 0, x_41);
lean_ctor_set(x_72, 1, x_35);
lean_ctor_set(x_72, 2, x_42);
lean_ctor_set(x_72, 3, x_43);
lean_ctor_set(x_72, 4, x_44);
lean_ctor_set(x_72, 5, x_45);
lean_ctor_set(x_72, 6, x_46);
lean_ctor_set(x_72, 7, x_47);
lean_ctor_set(x_72, 8, x_48);
x_51 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_st_ref_set(x_9, x_51);
x_53 = l_List_reverse___redArg(x_36);
x_54 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_53, x_6, x_7, x_8, x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; uint8_t x_61; 
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_54, 0);
lean_dec(x_62);
x_55 = x_54;
x_56 = x_61;
goto block_60;
}
else
{
lean_dec(x_54);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_34);
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_34);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec(x_34);
x_63 = lean_ctor_get(x_54, 0);
x_70 = !lean_is_exclusive(x_54);
if (x_70 == 0)
{
x_64 = x_54;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_54);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_8);
x_76 = lean_ctor_get(x_39, 0);
x_83 = !lean_is_exclusive(x_39);
if (x_83 == 0)
{
x_77 = x_39;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_39);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_32, 0);
lean_inc(x_84);
lean_dec_ref(x_32);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc_ref(x_86);
lean_dec_ref(x_84);
x_87 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___closed__0));
x_88 = lean_string_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_86);
x_90 = l_Lean_MessageData_ofFormat(x_89);
x_91 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_85, x_90, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_85);
return x_91;
}
else
{
lean_object* x_92; 
lean_dec_ref(x_86);
lean_dec_ref(x_8);
x_92 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg(x_85);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec_ref(x_8);
x_93 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg();
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___lam__2___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__8(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalTactic___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_evalTactic_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_15);
x_16 = l_Lean_Elab_Tactic_evalTactic(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_17;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_16;
}
}
else
{
lean_object* x_21; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_nat_dec_lt(x_1, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_2, x_2);
if (x_16 == 0)
{
if (x_14 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_2);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_evalTactic_spec__4(x_3, x_18, x_19, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_2);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_evalTactic_spec__4(x_3, x_21, x_22, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalTactic___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___lam__2___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_1, 1);
x_75 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___lam__2___closed__5));
x_76 = lean_name_eq(x_74, x_75);
x_77 = 1;
if (x_76 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_9, 2);
x_79 = lean_ctor_get_uint8(x_78, sizeof(void*)*1);
if (x_79 == 0)
{
lean_dec_ref(x_8);
x_54 = x_2;
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_9;
x_61 = x_10;
goto block_73;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___lam__2___closed__7));
x_81 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(x_80, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_221; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
lean_inc_ref(x_1);
x_83 = l_Lean_Syntax_getKind(x_1);
lean_inc(x_83);
x_84 = l_Lean_Name_toString(x_83, x_77);
x_221 = lean_unbox(x_82);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = l_Lean_trace_profiler;
x_223 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(x_78, x_222);
if (x_223 == 0)
{
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_8);
x_54 = x_2;
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
x_60 = x_9;
x_61 = x_10;
goto block_73;
}
else
{
lean_inc_ref(x_78);
goto block_220;
}
}
else
{
lean_inc_ref(x_78);
goto block_220;
}
block_97:
{
lean_object* x_88; double x_89; double x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_88 = lean_io_get_num_heartbeats();
x_89 = lean_float_of_nat(x_85);
x_90 = lean_float_of_nat(x_88);
x_91 = lean_box_float(x_89);
x_92 = lean_box_float(x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_87);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_unbox(x_82);
lean_dec(x_82);
x_96 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg(x_80, x_77, x_84, x_78, x_95, x_86, x_8, x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10);
lean_dec_ref(x_78);
return x_96;
}
block_117:
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
x_101 = lean_ctor_get(x_100, 0);
x_108 = !lean_is_exclusive(x_100);
if (x_108 == 0)
{
x_102 = x_100;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
lean_ctor_set_tag(x_102, 1);
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
x_85 = x_98;
x_86 = x_99;
x_87 = x_104;
goto block_97;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
x_109 = lean_ctor_get(x_100, 0);
x_116 = !lean_is_exclusive(x_100);
if (x_116 == 0)
{
x_110 = x_100;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_100);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
lean_ctor_set_tag(x_110, 0);
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
x_85 = x_98;
x_86 = x_99;
x_87 = x_112;
goto block_97;
}
}
}
}
block_132:
{
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_83);
lean_dec_ref(x_1);
x_122 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_123 = lean_apply_10(x_118, x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, lean_box(0));
x_98 = x_119;
x_99 = x_120;
x_100 = x_123;
goto block_117;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_obj_once(&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1, &l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1);
x_125 = l_Lean_MessageData_ofName(x_83);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_obj_once(&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3, &l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_inc_ref(x_9);
x_129 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_1, x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_131 = lean_apply_10(x_118, x_130, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, lean_box(0));
x_98 = x_119;
x_99 = x_120;
x_100 = x_131;
goto block_117;
}
else
{
lean_dec_ref(x_118);
x_98 = x_119;
x_99 = x_120;
x_100 = x_129;
goto block_117;
}
}
}
block_148:
{
lean_object* x_136; double x_137; double x_138; double x_139; double x_140; double x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_136 = lean_io_mono_nanos_now();
x_137 = lean_float_of_nat(x_133);
x_138 = lean_float_once(&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__8, &l_Lean_Elab_Tactic_evalTactic___lam__2___closed__8_once, _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__8);
x_139 = lean_float_div(x_137, x_138);
x_140 = lean_float_of_nat(x_136);
x_141 = lean_float_div(x_140, x_138);
x_142 = lean_box_float(x_139);
x_143 = lean_box_float(x_141);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_unbox(x_82);
lean_dec(x_82);
x_147 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg(x_80, x_77, x_84, x_78, x_146, x_134, x_8, x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10);
lean_dec_ref(x_78);
return x_147;
}
block_168:
{
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_159; 
x_152 = lean_ctor_get(x_151, 0);
x_159 = !lean_is_exclusive(x_151);
if (x_159 == 0)
{
x_153 = x_151;
x_154 = x_159;
goto block_158;
}
else
{
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_box(0);
x_154 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_155; 
if (x_154 == 0)
{
lean_ctor_set_tag(x_153, 1);
x_155 = x_153;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_152);
x_155 = x_157;
goto block_156;
}
block_156:
{
x_133 = x_149;
x_134 = x_150;
x_135 = x_155;
goto block_148;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_167; 
x_160 = lean_ctor_get(x_151, 0);
x_167 = !lean_is_exclusive(x_151);
if (x_167 == 0)
{
x_161 = x_151;
x_162 = x_167;
goto block_166;
}
else
{
lean_inc(x_160);
lean_dec(x_151);
x_161 = lean_box(0);
x_162 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_163; 
if (x_162 == 0)
{
lean_ctor_set_tag(x_161, 0);
x_163 = x_161;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_160);
x_163 = x_165;
goto block_164;
}
block_164:
{
x_133 = x_149;
x_134 = x_150;
x_135 = x_163;
goto block_148;
}
}
}
}
block_183:
{
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_83);
lean_dec_ref(x_1);
x_173 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_174 = lean_apply_10(x_171, x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, lean_box(0));
x_149 = x_169;
x_150 = x_170;
x_151 = x_174;
goto block_168;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_obj_once(&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1, &l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1);
x_176 = l_Lean_MessageData_ofName(x_83);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_obj_once(&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3, &l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
lean_inc_ref(x_9);
x_180 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_1, x_179, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_182 = lean_apply_10(x_171, x_181, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, lean_box(0));
x_149 = x_169;
x_150 = x_170;
x_151 = x_182;
goto block_168;
}
else
{
lean_dec_ref(x_171);
x_149 = x_169;
x_150 = x_170;
x_151 = x_180;
goto block_168;
}
}
}
block_220:
{
lean_object* x_184; 
x_184 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg(x_10);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = l_Lean_trace_profiler_useHeartbeats;
x_187 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(x_78, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_188 = lean_io_mono_nanos_now();
x_189 = lean_st_ref_get(x_10);
x_190 = lean_st_ref_get(x_10);
x_191 = lean_ctor_get(x_189, 0);
lean_inc_ref(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_190, 0);
lean_inc_ref(x_192);
lean_dec(x_190);
x_193 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_194 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_193, x_191, x_83);
x_195 = l_Lean_Elab_macroAttribute;
x_196 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_195, x_192, x_83);
lean_inc(x_194);
lean_inc(x_196);
lean_inc_ref(x_1);
x_197 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lam__1___boxed), 13, 3);
lean_closure_set(x_197, 0, x_1);
lean_closure_set(x_197, 1, x_196);
lean_closure_set(x_197, 2, x_194);
x_198 = l_List_isEmpty___redArg(x_194);
lean_dec(x_194);
if (x_198 == 0)
{
lean_dec(x_196);
x_169 = x_188;
x_170 = x_185;
x_171 = x_197;
x_172 = x_198;
goto block_183;
}
else
{
uint8_t x_199; 
x_199 = l_List_isEmpty___redArg(x_196);
lean_dec(x_196);
x_169 = x_188;
x_170 = x_185;
x_171 = x_197;
x_172 = x_199;
goto block_183;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_200 = lean_io_get_num_heartbeats();
x_201 = lean_st_ref_get(x_10);
x_202 = lean_st_ref_get(x_10);
x_203 = lean_ctor_get(x_201, 0);
lean_inc_ref(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_202, 0);
lean_inc_ref(x_204);
lean_dec(x_202);
x_205 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_206 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_205, x_203, x_83);
x_207 = l_Lean_Elab_macroAttribute;
x_208 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_207, x_204, x_83);
lean_inc(x_206);
lean_inc(x_208);
lean_inc_ref(x_1);
x_209 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lam__1___boxed), 13, 3);
lean_closure_set(x_209, 0, x_1);
lean_closure_set(x_209, 1, x_208);
lean_closure_set(x_209, 2, x_206);
x_210 = l_List_isEmpty___redArg(x_206);
lean_dec(x_206);
if (x_210 == 0)
{
lean_dec(x_208);
x_118 = x_209;
x_119 = x_200;
x_120 = x_185;
x_121 = x_210;
goto block_132;
}
else
{
uint8_t x_211; 
x_211 = l_List_isEmpty___redArg(x_208);
lean_dec(x_208);
x_118 = x_209;
x_119 = x_200;
x_120 = x_185;
x_121 = x_211;
goto block_132;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_219; 
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec_ref(x_78);
lean_dec_ref(x_1);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_212 = lean_ctor_get(x_184, 0);
x_219 = !lean_is_exclusive(x_184);
if (x_219 == 0)
{
x_213 = x_184;
x_214 = x_219;
goto block_218;
}
else
{
lean_inc(x_212);
lean_dec(x_184);
x_213 = lean_box(0);
x_214 = x_219;
goto block_218;
}
block_218:
{
lean_object* x_215; 
if (x_214 == 0)
{
x_215 = x_213;
goto block_216;
}
else
{
lean_object* x_217; 
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_212);
x_215 = x_217;
goto block_216;
}
block_216:
{
return x_215;
}
}
}
}
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_231; 
lean_dec_ref(x_1);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_224 = lean_ctor_get(x_81, 0);
x_231 = !lean_is_exclusive(x_81);
if (x_231 == 0)
{
x_225 = x_81;
x_226 = x_231;
goto block_230;
}
else
{
lean_inc(x_224);
lean_dec(x_81);
x_225 = lean_box(0);
x_226 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_227; 
if (x_226 == 0)
{
x_227 = x_225;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_224);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec_ref(x_8);
x_232 = l_Lean_Syntax_getArgs(x_1);
x_233 = lean_unsigned_to_nat(0u);
x_234 = lean_array_get_size(x_232);
x_235 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lam__3___boxed), 12, 3);
lean_closure_set(x_235, 0, x_233);
lean_closure_set(x_235, 1, x_234);
lean_closure_set(x_235, 2, x_232);
x_236 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lam__4___boxed), 11, 2);
lean_closure_set(x_236, 0, x_1);
lean_closure_set(x_236, 1, x_235);
x_237 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__6___redArg(x_77, x_236, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10);
return x_237;
}
}
case 0:
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_238 = lean_box(0);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
default: 
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_240 = lean_obj_once(&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__10, &l_Lean_Elab_Tactic_evalTactic___lam__2___closed__10_once, _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__10);
x_241 = l_Lean_MessageData_ofSyntax(x_1);
x_242 = l_Lean_indentD(x_241);
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_243, x_6, x_7, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_244;
}
}
block_34:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_saveState___redArg(x_15, x_17, x_19, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___lam__1___closed__0));
x_25 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval(x_1, x_23, x_12, x_13, x_24, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_26 = lean_ctor_get(x_22, 0);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
x_27 = x_22;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
block_53:
{
if (x_46 == 0)
{
lean_dec(x_44);
x_12 = x_37;
x_13 = x_41;
x_14 = x_43;
x_15 = x_45;
x_16 = x_38;
x_17 = x_40;
x_18 = x_36;
x_19 = x_39;
x_20 = x_42;
x_21 = x_35;
goto block_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_obj_once(&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1, &l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1_once, _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__1);
x_48 = l_Lean_MessageData_ofName(x_44);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_obj_once(&l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3, &l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3_once, _init_l_Lean_Elab_Tactic_evalTactic___lam__2___closed__3);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc_ref(x_42);
x_52 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_1, x_51, x_43, x_45, x_38, x_40, x_36, x_39, x_42, x_35);
if (lean_obj_tag(x_52) == 0)
{
lean_dec_ref(x_52);
x_12 = x_37;
x_13 = x_41;
x_14 = x_43;
x_15 = x_45;
x_16 = x_38;
x_17 = x_40;
x_18 = x_36;
x_19 = x_39;
x_20 = x_42;
x_21 = x_35;
goto block_34;
}
else
{
lean_dec(x_45);
lean_dec_ref(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec(x_1);
return x_52;
}
}
}
block_73:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_st_ref_get(x_61);
x_63 = lean_st_ref_get(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_65);
lean_dec(x_63);
x_66 = l_Lean_Elab_Tactic_tacticElabAttribute;
lean_inc(x_1);
x_67 = l_Lean_Syntax_getKind(x_1);
x_68 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_66, x_64, x_67);
x_69 = l_Lean_Elab_macroAttribute;
x_70 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_69, x_65, x_67);
x_71 = l_List_isEmpty___redArg(x_68);
if (x_71 == 0)
{
x_35 = x_61;
x_36 = x_58;
x_37 = x_70;
x_38 = x_56;
x_39 = x_59;
x_40 = x_57;
x_41 = x_68;
x_42 = x_60;
x_43 = x_54;
x_44 = x_67;
x_45 = x_55;
x_46 = x_71;
goto block_53;
}
else
{
uint8_t x_72; 
x_72 = l_List_isEmpty___redArg(x_70);
x_35 = x_61;
x_36 = x_58;
x_37 = x_70;
x_38 = x_56;
x_39 = x_59;
x_40 = x_57;
x_41 = x_68;
x_42 = x_60;
x_43 = x_54;
x_44 = x_67;
x_45 = x_55;
x_46 = x_72;
goto block_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTactic___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_41; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 2);
x_15 = lean_ctor_get(x_9, 3);
x_16 = lean_ctor_get(x_9, 4);
x_17 = lean_ctor_get(x_9, 5);
x_18 = lean_ctor_get(x_9, 6);
x_19 = lean_ctor_get(x_9, 7);
x_20 = lean_ctor_get(x_9, 8);
x_21 = lean_ctor_get(x_9, 9);
x_22 = lean_ctor_get(x_9, 10);
x_23 = lean_ctor_get(x_9, 11);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_25 = lean_ctor_get(x_9, 12);
x_26 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_27 = lean_ctor_get(x_9, 13);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
x_28 = x_9;
x_29 = x_41;
goto block_40;
}
else
{
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_31 = lean_nat_dec_eq(x_15, x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lam__2___boxed), 11, 8);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_3);
lean_closure_set(x_32, 2, x_4);
lean_closure_set(x_32, 3, x_5);
lean_closure_set(x_32, 4, x_6);
lean_closure_set(x_32, 5, x_7);
lean_closure_set(x_32, 6, x_8);
lean_closure_set(x_32, 7, x_2);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_15, x_33);
lean_dec(x_15);
if (x_29 == 0)
{
lean_ctor_set(x_28, 5, x_30);
lean_ctor_set(x_28, 3, x_34);
x_35 = x_28;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_13);
lean_ctor_set(x_38, 2, x_14);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_16);
lean_ctor_set(x_38, 5, x_30);
lean_ctor_set(x_38, 6, x_18);
lean_ctor_set(x_38, 7, x_19);
lean_ctor_set(x_38, 8, x_20);
lean_ctor_set(x_38, 9, x_21);
lean_ctor_set(x_38, 10, x_22);
lean_ctor_set(x_38, 11, x_23);
lean_ctor_set(x_38, 12, x_25);
lean_ctor_set(x_38, 13, x_27);
lean_ctor_set_uint8(x_38, sizeof(void*)*14, x_24);
lean_ctor_set_uint8(x_38, sizeof(void*)*14 + 1, x_26);
x_35 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_36; 
x_36 = l_Lean_Core_withFreshMacroScope___redArg(x_32, x_35, x_10);
return x_36;
}
}
else
{
lean_object* x_39; 
lean_del_object(x_28);
lean_dec_ref(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg(x_30);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTactic___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___closed__0));
x_12 = l_Lean_Core_checkSystem(x_11, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_13);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lam__0___boxed), 11, 1);
lean_closure_set(x_14, 0, x_1);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___lam__5___boxed), 11, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Syntax_getKind(x_1);
x_17 = l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___redArg(x_11, x_13, x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_13);
return x_17;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__16(void) {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg___closed__1);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__15(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__14));
x_3 = l_Lean_Name_toString(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__17(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__16, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__16_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__16);
x_3 = lean_box(0);
x_4 = l_Lean_Language_Snapshot_Diagnostics_empty;
x_5 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__15, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__15_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__15);
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc_ref(x_13);
x_16 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_153; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_58 = 1;
x_153 = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__4(x_2, x_58, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; uint8_t x_204; 
lean_dec_ref(x_153);
x_204 = l_List_isEmpty___redArg(x_5);
if (x_204 == 0)
{
x_154 = x_204;
goto block_203;
}
else
{
uint8_t x_205; 
x_205 = l_List_isEmpty___redArg(x_6);
x_154 = x_205;
goto block_203;
}
block_203:
{
if (x_154 == 0)
{
lean_object* x_155; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_155 = l_Lean_Elab_Tactic_evalTactic(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_155;
}
else
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_9, 6);
if (lean_obj_tag(x_156) == 1)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_156, 0);
x_158 = lean_st_ref_get(x_14);
x_159 = lean_st_ref_get(x_14);
x_160 = lean_ctor_get(x_157, 0);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_4);
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
x_162 = lean_box(0);
x_59 = x_162;
x_60 = x_161;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_11;
x_66 = x_12;
x_67 = x_13;
x_68 = x_14;
goto block_146;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_ctor_get(x_160, 0);
x_164 = lean_ctor_get(x_157, 1);
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_ctor_get(x_163, 1);
x_167 = l_Lean_Syntax_getKind(x_4);
lean_inc(x_165);
x_168 = l_Lean_Syntax_isOfKind(x_165, x_167);
lean_dec(x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_159);
lean_dec(x_158);
x_169 = lean_box(0);
lean_inc(x_164);
lean_inc(x_166);
x_147 = x_166;
x_148 = x_164;
x_149 = x_169;
goto block_152;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_inc(x_166);
x_170 = l_Lean_Language_SnapshotTask_get___redArg(x_166);
x_171 = lean_ctor_get(x_170, 3);
lean_inc_ref(x_171);
x_172 = l_Lean_Language_SnapshotTask_get___redArg(x_171);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
lean_dec(x_170);
lean_dec(x_159);
lean_dec(x_158);
x_174 = lean_box(0);
lean_inc(x_164);
lean_inc(x_166);
x_147 = x_166;
x_148 = x_164;
x_149 = x_174;
goto block_152;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_201; 
x_175 = lean_ctor_get(x_173, 0);
x_201 = !lean_is_exclusive(x_173);
if (x_201 == 0)
{
x_176 = x_173;
x_177 = x_201;
goto block_200;
}
else
{
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_box(0);
x_177 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_178 = lean_ctor_get(x_175, 0);
lean_inc_ref(x_178);
lean_dec(x_175);
x_179 = lean_ctor_get(x_178, 0);
lean_inc_ref(x_179);
lean_dec_ref(x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc_ref(x_180);
lean_dec_ref(x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc_ref(x_181);
lean_dec_ref(x_180);
x_182 = lean_ctor_get(x_158, 1);
lean_inc(x_182);
lean_dec(x_158);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 4);
lean_inc_ref(x_184);
lean_dec_ref(x_181);
x_185 = lean_nat_dec_eq(x_183, x_182);
lean_dec(x_182);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec_ref(x_184);
lean_del_object(x_176);
lean_dec(x_170);
lean_dec(x_159);
x_186 = lean_box(0);
lean_inc(x_164);
lean_inc(x_166);
x_147 = x_166;
x_148 = x_164;
x_149 = x_186;
goto block_152;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_184, 0);
lean_inc_ref(x_187);
lean_dec_ref(x_184);
x_188 = lean_ctor_get(x_187, 2);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = lean_unsigned_to_nat(0u);
x_190 = lean_nat_dec_eq(x_188, x_189);
lean_dec(x_188);
if (x_190 == 0)
{
lean_object* x_191; 
lean_del_object(x_176);
lean_dec(x_170);
lean_dec(x_159);
x_191 = lean_box(0);
lean_inc(x_164);
lean_inc(x_166);
x_147 = x_166;
x_148 = x_164;
x_149 = x_191;
goto block_152;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = lean_ctor_get(x_159, 4);
lean_inc_ref(x_192);
lean_dec(x_159);
x_193 = lean_ctor_get(x_192, 0);
lean_inc_ref(x_193);
lean_dec_ref(x_192);
x_194 = lean_ctor_get(x_193, 2);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = lean_nat_dec_eq(x_194, x_189);
lean_dec(x_194);
if (x_195 == 0)
{
lean_object* x_196; 
lean_del_object(x_176);
lean_dec(x_170);
x_196 = lean_box(0);
lean_inc(x_164);
lean_inc(x_166);
x_147 = x_166;
x_148 = x_164;
x_149 = x_196;
goto block_152;
}
else
{
lean_object* x_197; 
lean_inc(x_164);
if (x_177 == 0)
{
lean_ctor_set(x_176, 0, x_170);
x_197 = x_176;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_170);
x_197 = x_199;
goto block_198;
}
block_198:
{
x_59 = x_197;
x_60 = x_164;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_11;
x_66 = x_12;
x_67 = x_13;
x_68 = x_14;
goto block_146;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_202 = l_Lean_Elab_Tactic_evalTactic(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_202;
}
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_153;
}
block_57:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_32);
lean_ctor_set(x_46, 2, x_28);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_34);
lean_ctor_set(x_46, 5, x_20);
lean_ctor_set(x_46, 6, x_45);
lean_ctor_set(x_46, 7, x_33);
lean_ctor_set_uint8(x_46, sizeof(void*)*8, x_38);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 1, x_22);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 2, x_27);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 3, x_18);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 4, x_19);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 5, x_37);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 6, x_30);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 7, x_24);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 8, x_25);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 9, x_26);
x_47 = l_Lean_Elab_Tactic_evalTactic(x_17, x_23, x_21, x_46, x_31, x_36, x_42, x_41, x_35);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; uint8_t x_55; 
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_47, 0);
lean_dec(x_56);
x_48 = x_47;
x_49 = x_55;
goto block_54;
}
else
{
lean_dec(x_47);
x_48 = lean_box(0);
x_49 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
if (x_49 == 0)
{
lean_ctor_set(x_48, 0, x_50);
x_51 = x_48;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
else
{
return x_47;
}
}
block_146:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_io_promise_new();
x_70 = l_Lean_Elab_Tactic_saveState___redArg(x_62, x_64, x_66, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = lean_ctor_get(x_67, 12);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_box(0);
x_75 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__17, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__17_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__17);
lean_inc(x_17);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_17);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_71);
x_78 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__18));
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_78);
lean_inc_ref(x_76);
x_80 = l_Lean_Language_SnapshotTask_finished___redArg(x_76, x_79);
x_81 = l_Lean_Language_SnapshotTask_defaultReportingRange(x_76);
x_82 = lean_io_promise_result_opt(x_69);
x_83 = lean_task_map(x_3, x_82, x_73, x_58);
lean_inc(x_72);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_72);
lean_ctor_set(x_84, 3, x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_mk_empty_array_with_capacity(x_85);
x_87 = lean_array_push(x_86, x_84);
lean_inc(x_17);
x_88 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_88, 0, x_75);
lean_ctor_set(x_88, 1, x_17);
lean_ctor_set(x_88, 2, x_74);
lean_ctor_set(x_88, 3, x_80);
lean_ctor_set(x_88, 4, x_87);
x_89 = lean_io_promise_resolve(x_88, x_60);
lean_dec(x_60);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; 
x_90 = lean_ctor_get(x_63, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_63, 1);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_63, sizeof(void*)*8);
x_93 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 1);
x_94 = lean_ctor_get(x_63, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_63, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_63, 5);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 2);
x_99 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 3);
x_100 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 4);
x_101 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 5);
x_102 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 6);
x_103 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 7);
x_104 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 8);
x_105 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 9);
x_106 = lean_ctor_get(x_63, 7);
lean_inc_ref(x_106);
lean_dec_ref(x_63);
x_18 = x_99;
x_19 = x_100;
x_20 = x_97;
x_21 = x_62;
x_22 = x_93;
x_23 = x_61;
x_24 = x_103;
x_25 = x_104;
x_26 = x_105;
x_27 = x_98;
x_28 = x_94;
x_29 = x_69;
x_30 = x_102;
x_31 = x_64;
x_32 = x_91;
x_33 = x_106;
x_34 = x_96;
x_35 = x_68;
x_36 = x_65;
x_37 = x_101;
x_38 = x_92;
x_39 = x_90;
x_40 = x_95;
x_41 = x_67;
x_42 = x_66;
x_43 = x_74;
goto block_57;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_137; 
x_107 = lean_ctor_get(x_59, 0);
x_137 = !lean_is_exclusive(x_59);
if (x_137 == 0)
{
x_108 = x_59;
x_109 = x_137;
goto block_136;
}
else
{
lean_inc(x_107);
lean_dec(x_59);
x_108 = lean_box(0);
x_109 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_110 = lean_ctor_get(x_63, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_63, 1);
lean_inc(x_111);
x_112 = lean_ctor_get_uint8(x_63, sizeof(void*)*8);
x_113 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 1);
x_114 = lean_ctor_get(x_63, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_63, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_63, 5);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 2);
x_119 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 3);
x_120 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 4);
x_121 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 5);
x_122 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 6);
x_123 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 7);
x_124 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 8);
x_125 = lean_ctor_get_uint8(x_63, sizeof(void*)*8 + 9);
x_126 = lean_ctor_get(x_63, 7);
lean_inc_ref(x_126);
lean_dec_ref(x_63);
x_127 = lean_ctor_get(x_107, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_107, 4);
lean_inc_ref(x_128);
lean_dec(x_107);
x_129 = lean_array_get_size(x_128);
x_130 = lean_nat_dec_lt(x_73, x_129);
if (x_130 == 0)
{
lean_dec_ref(x_128);
lean_dec(x_127);
lean_del_object(x_108);
x_18 = x_119;
x_19 = x_120;
x_20 = x_117;
x_21 = x_62;
x_22 = x_113;
x_23 = x_61;
x_24 = x_123;
x_25 = x_124;
x_26 = x_125;
x_27 = x_118;
x_28 = x_114;
x_29 = x_69;
x_30 = x_122;
x_31 = x_64;
x_32 = x_111;
x_33 = x_126;
x_34 = x_116;
x_35 = x_68;
x_36 = x_65;
x_37 = x_121;
x_38 = x_112;
x_39 = x_110;
x_40 = x_115;
x_41 = x_67;
x_42 = x_66;
x_43 = x_74;
goto block_57;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_array_fget(x_128, x_73);
lean_dec_ref(x_128);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_131);
if (x_109 == 0)
{
lean_ctor_set(x_108, 0, x_132);
x_133 = x_108;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_132);
x_133 = x_135;
goto block_134;
}
block_134:
{
x_18 = x_119;
x_19 = x_120;
x_20 = x_117;
x_21 = x_62;
x_22 = x_113;
x_23 = x_61;
x_24 = x_123;
x_25 = x_124;
x_26 = x_125;
x_27 = x_118;
x_28 = x_114;
x_29 = x_69;
x_30 = x_122;
x_31 = x_64;
x_32 = x_111;
x_33 = x_126;
x_34 = x_116;
x_35 = x_68;
x_36 = x_65;
x_37 = x_121;
x_38 = x_112;
x_39 = x_110;
x_40 = x_115;
x_41 = x_67;
x_42 = x_66;
x_43 = x_133;
goto block_57;
}
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_17);
lean_dec_ref(x_3);
x_138 = lean_ctor_get(x_70, 0);
x_145 = !lean_is_exclusive(x_70);
if (x_145 == 0)
{
x_139 = x_70;
x_140 = x_145;
goto block_144;
}
else
{
lean_inc(x_138);
lean_dec(x_70);
x_139 = lean_box(0);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_140 == 0)
{
x_141 = x_139;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_138);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
block_152:
{
lean_object* x_150; lean_object* x_151; 
x_150 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___closed__19));
x_151 = l_Lean_Language_SnapshotTask_cancelRec___redArg(x_150, x_147);
x_59 = x_149;
x_60 = x_148;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_11;
x_66 = x_12;
x_67 = x_13;
x_68 = x_14;
goto block_146;
}
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; uint8_t x_213; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_206 = lean_ctor_get(x_16, 0);
x_213 = !lean_is_exclusive(x_16);
if (x_213 == 0)
{
x_207 = x_16;
x_208 = x_213;
goto block_212;
}
else
{
lean_inc(x_206);
lean_dec(x_16);
x_207 = lean_box(0);
x_208 = x_213;
goto block_212;
}
block_212:
{
lean_object* x_209; 
if (x_208 == 0)
{
x_209 = x_207;
goto block_210;
}
else
{
lean_object* x_211; 
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_206);
x_209 = x_211;
goto block_210;
}
block_210:
{
return x_209;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_127; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_127 = !lean_is_exclusive(x_3);
if (x_127 == 0)
{
x_18 = x_3;
x_19 = x_127;
goto block_126;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_100; lean_object* x_101; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_16, 1);
lean_inc(x_106);
lean_dec(x_16);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
lean_inc(x_1);
x_109 = lean_apply_1(x_106, x_1);
lean_inc(x_107);
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_108);
lean_inc(x_1);
x_111 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_110, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___closed__0));
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_1);
x_114 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___lam__1___boxed), 15, 6);
lean_closure_set(x_114, 0, x_109);
lean_closure_set(x_114, 1, x_107);
lean_closure_set(x_114, 2, x_113);
lean_closure_set(x_114, 3, x_1);
lean_closure_set(x_114, 4, x_4);
lean_closure_set(x_114, 5, x_17);
x_115 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval___lam__1___boxed), 11, 1);
lean_closure_set(x_115, 0, x_112);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_116 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_114, x_115, x_110, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_116) == 0)
{
lean_del_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_116;
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_100 = x_116;
x_101 = x_117;
goto block_104;
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_125; 
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_107);
x_118 = lean_ctor_get(x_111, 0);
x_125 = !lean_is_exclusive(x_111);
if (x_125 == 0)
{
x_119 = x_111;
x_120 = x_125;
goto block_124;
}
else
{
lean_inc(x_118);
lean_dec(x_111);
x_119 = lean_box(0);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
lean_inc(x_118);
if (x_120 == 0)
{
x_121 = x_119;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_118);
x_121 = x_123;
goto block_122;
}
block_122:
{
x_100 = x_121;
x_101 = x_118;
goto block_104;
}
}
}
block_46:
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Tactic_saveState___redArg(x_22, x_24, x_26, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = 1;
lean_inc_ref(x_2);
x_32 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_2, x_31, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_32);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_20);
x_33 = x_18;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_30);
x_33 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_34; 
x_34 = lean_array_push(x_5, x_33);
x_3 = x_17;
x_5 = x_34;
x_6 = x_21;
x_7 = x_22;
x_8 = x_23;
x_9 = x_24;
x_10 = x_25;
x_11 = x_26;
x_12 = x_27;
x_13 = x_28;
goto _start;
}
}
else
{
lean_dec(x_30);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_del_object(x_18);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_32;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_del_object(x_18);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_29, 0);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
x_39 = x_29;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
block_99:
{
if (x_49 == 0)
{
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_48);
x_50 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1));
x_51 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__0___redArg(x_50, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
x_20 = x_47;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
goto block_46;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_inc_ref(x_47);
x_54 = l_Lean_Exception_toMessageData(x_47);
x_55 = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__1___redArg(x_50, x_54, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_20 = x_47;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_12;
x_28 = x_13;
goto block_46;
}
else
{
lean_dec_ref(x_47);
lean_del_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec_ref(x_47);
lean_del_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_51, 0);
x_63 = !lean_is_exclusive(x_51);
if (x_63 == 0)
{
x_57 = x_51;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
lean_del_object(x_18);
x_64 = lean_ctor_get(x_47, 0);
x_65 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_66 = l_Lean_instBEqInternalExceptionId_beq(x_64, x_65);
x_67 = 1;
if (x_66 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Elab_abortTacticExceptionId;
x_69 = l_Lean_instBEqInternalExceptionId_beq(x_64, x_68);
if (x_69 == 0)
{
lean_dec_ref(x_47);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_48;
}
else
{
lean_object* x_70; 
lean_dec_ref(x_48);
x_70 = l_Lean_Core_getMessageLog___redArg(x_13);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Lean_MessageLog_toList(x_71);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__2___redArg(x_72, x_73, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec_ref(x_74);
x_75 = l_Lean_Elab_Tactic_saveState___redArg(x_7, x_9, x_11, x_13);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
lean_inc_ref(x_2);
x_77 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_2, x_67, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_77);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_47);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_array_push(x_5, x_78);
x_3 = x_17;
x_5 = x_79;
goto _start;
}
else
{
lean_dec(x_76);
lean_dec_ref(x_47);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_77;
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec_ref(x_47);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_81 = lean_ctor_get(x_75, 0);
x_88 = !lean_is_exclusive(x_75);
if (x_88 == 0)
{
x_82 = x_75;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
else
{
lean_dec_ref(x_47);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_74;
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec_ref(x_47);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_70, 0);
x_96 = !lean_is_exclusive(x_70);
if (x_96 == 0)
{
x_90 = x_70;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_70);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
}
else
{
lean_object* x_97; 
lean_dec_ref(x_47);
lean_dec_ref(x_48);
lean_inc_ref(x_2);
x_97 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_2, x_67, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_97) == 0)
{
lean_dec_ref(x_97);
x_3 = x_17;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_97;
}
}
}
}
else
{
lean_dec_ref(x_47);
lean_del_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_48;
}
}
block_104:
{
uint8_t x_102; 
x_102 = l_Lean_Exception_isInterrupt(x_101);
if (x_102 == 0)
{
uint8_t x_103; 
lean_inc_ref(x_101);
x_103 = l_Lean_Exception_isRuntime(x_101);
x_47 = x_101;
x_48 = x_100;
x_49 = x_103;
goto block_99;
}
else
{
x_47 = x_101;
x_48 = x_100;
x_49 = x_102;
goto block_99;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_saveState___redArg(x_6, x_8, x_10, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___lam__1___closed__0));
x_17 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval(x_1, x_15, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_14, 0);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
x_19 = x_14;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_evalTactic_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_evalTactic_spec__4(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___redArg(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_evalTactic_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___redArg(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_Tactic_evalTactic_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_profileitM___at___00Lean_Elab_Tactic_evalTactic_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___redArg(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_3);
x_20 = lean_unbox(x_6);
x_21 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3(x_1, x_2, x_19, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_1, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_evalTactic_spec__3_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_obj_once(&l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__1, &l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___closed__1);
x_7 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_abortTacticExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg___closed__0, &l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_done(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_22; 
x_11 = lean_ctor_get(x_10, 0);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
x_12 = x_10;
x_13 = x_22;
goto block_21;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_22;
goto block_21;
}
block_21:
{
uint8_t x_14; 
x_14 = l_List_isEmpty___redArg(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_del_object(x_12);
x_15 = l_Lean_Elab_Term_reportUnsolvedGoals(x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_done_spec__0___redArg();
return x_16;
}
else
{
return x_15;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = lean_box(0);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_17);
x_18 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_23 = lean_ctor_get(x_10, 0);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
x_24 = x_10;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_done___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_done(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_45; 
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_ctor_get(x_12, 1);
x_45 = !lean_is_exclusive(x_12);
if (x_45 == 0)
{
x_15 = x_12;
x_16 = x_45;
goto block_44;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_17);
x_18 = x_15;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_17);
x_18 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Elab_Tactic_setGoals___redArg(x_18, x_3);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_List_appendTR___redArg(x_23, x_14);
x_25 = l_Lean_Elab_Tactic_setGoals___redArg(x_24, x_3);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_26 = x_25;
x_27 = x_32;
goto block_31;
}
else
{
lean_dec(x_25);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_21);
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_21);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_3);
x_34 = lean_ctor_get(x_22, 0);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
x_35 = x_22;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_11, 0);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
x_48 = x_11;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_11);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_focus___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_focus___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_focus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Elab_Tactic_done(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_14 = x_13;
x_15 = x_20;
goto block_19;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_12);
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_23 = x_13;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_focusAndDone___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focusAndDone___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_focus___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_focusAndDone___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_focusAndDone___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_focusAndDone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_focusAndDone(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; uint8_t x_103; uint8_t x_119; 
x_94 = 2;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_94);
if (x_119 == 0)
{
x_103 = x_119;
goto block_118;
}
else
{
uint8_t x_120; 
lean_inc_ref(x_2);
x_120 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_103 = x_120;
goto block_118;
}
block_45:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_44; 
x_19 = lean_st_ref_take(x_18);
x_20 = lean_ctor_get(x_17, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 7);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 2);
x_25 = lean_ctor_get(x_19, 3);
x_26 = lean_ctor_get(x_19, 4);
x_27 = lean_ctor_get(x_19, 5);
x_28 = lean_ctor_get(x_19, 6);
x_29 = lean_ctor_get(x_19, 7);
x_30 = lean_ctor_get(x_19, 8);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
x_31 = x_19;
x_32 = x_44;
goto block_43;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
x_31 = lean_box(0);
x_32 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_14);
x_35 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_13);
lean_ctor_set(x_35, 2, x_16);
lean_ctor_set(x_35, 3, x_15);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 1, x_11);
lean_ctor_set_uint8(x_35, sizeof(void*)*5 + 2, x_4);
x_36 = l_Lean_MessageLog_add(x_35, x_28);
if (x_32 == 0)
{
lean_ctor_set(x_31, 6, x_36);
x_37 = x_31;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_23);
lean_ctor_set(x_42, 2, x_24);
lean_ctor_set(x_42, 3, x_25);
lean_ctor_set(x_42, 4, x_26);
lean_ctor_set(x_42, 5, x_27);
lean_ctor_set(x_42, 6, x_36);
lean_ctor_set(x_42, 7, x_29);
lean_ctor_set(x_42, 8, x_30);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_st_ref_set(x_18, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
block_70:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_69; 
x_54 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_55 = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__3(x_54, x_5, x_6, x_7, x_8);
x_56 = lean_ctor_get(x_55, 0);
x_69 = !lean_is_exclusive(x_55);
if (x_69 == 0)
{
x_57 = x_55;
x_58 = x_69;
goto block_68;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_51);
x_59 = l_Lean_FileMap_toPosition(x_51, x_48);
lean_dec(x_48);
x_60 = l_Lean_FileMap_toPosition(x_51, x_53);
lean_dec(x_53);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___closed__0));
if (x_52 == 0)
{
lean_del_object(x_57);
lean_dec_ref(x_46);
x_10 = x_47;
x_11 = x_49;
x_12 = x_50;
x_13 = x_59;
x_14 = x_56;
x_15 = x_62;
x_16 = x_61;
x_17 = x_7;
x_18 = x_8;
goto block_45;
}
else
{
uint8_t x_63; 
lean_inc(x_56);
x_63 = l_Lean_MessageData_hasTag(x_46, x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_61);
lean_dec_ref(x_59);
lean_dec(x_56);
lean_dec_ref(x_47);
lean_dec_ref(x_7);
x_64 = lean_box(0);
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_64);
x_65 = x_57;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
else
{
lean_del_object(x_57);
x_10 = x_47;
x_11 = x_49;
x_12 = x_50;
x_13 = x_59;
x_14 = x_56;
x_15 = x_62;
x_16 = x_61;
x_17 = x_7;
x_18 = x_8;
goto block_45;
}
}
}
}
block_81:
{
lean_object* x_79; 
x_79 = l_Lean_Syntax_getTailPos_x3f(x_73, x_75);
lean_dec(x_73);
if (lean_obj_tag(x_79) == 0)
{
lean_inc(x_78);
x_46 = x_71;
x_47 = x_72;
x_48 = x_78;
x_49 = x_74;
x_50 = x_75;
x_51 = x_76;
x_52 = x_77;
x_53 = x_78;
goto block_70;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_46 = x_71;
x_47 = x_72;
x_48 = x_78;
x_49 = x_74;
x_50 = x_75;
x_51 = x_76;
x_52 = x_77;
x_53 = x_80;
goto block_70;
}
}
block_93:
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_replaceRef(x_1, x_84);
lean_dec(x_84);
x_90 = l_Lean_Syntax_getPos_x3f(x_89, x_85);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_unsigned_to_nat(0u);
x_71 = x_82;
x_72 = x_83;
x_73 = x_89;
x_74 = x_88;
x_75 = x_85;
x_76 = x_86;
x_77 = x_87;
x_78 = x_91;
goto block_81;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec_ref(x_90);
x_71 = x_82;
x_72 = x_83;
x_73 = x_89;
x_74 = x_88;
x_75 = x_85;
x_76 = x_86;
x_77 = x_87;
x_78 = x_92;
goto block_81;
}
}
block_102:
{
if (x_101 == 0)
{
x_82 = x_99;
x_83 = x_95;
x_84 = x_96;
x_85 = x_100;
x_86 = x_97;
x_87 = x_98;
x_88 = x_3;
goto block_93;
}
else
{
x_82 = x_99;
x_83 = x_95;
x_84 = x_96;
x_85 = x_100;
x_86 = x_97;
x_87 = x_98;
x_88 = x_94;
goto block_93;
}
}
block_118:
{
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; 
x_104 = lean_ctor_get(x_7, 0);
x_105 = lean_ctor_get(x_7, 1);
x_106 = lean_ctor_get(x_7, 2);
x_107 = lean_ctor_get(x_7, 5);
x_108 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_109 = lean_box(x_103);
x_110 = lean_box(x_108);
x_111 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
x_112 = 1;
x_113 = l_Lean_instBEqMessageSeverity_beq(x_3, x_112);
if (x_113 == 0)
{
lean_inc_ref(x_105);
lean_inc(x_107);
lean_inc_ref(x_104);
x_95 = x_104;
x_96 = x_107;
x_97 = x_105;
x_98 = x_108;
x_99 = x_111;
x_100 = x_103;
x_101 = x_113;
goto block_102;
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = l_Lean_warningAsError;
x_115 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Term_reportUnsolvedGoals_spec__0_spec__0_spec__1_spec__4(x_106, x_114);
lean_inc_ref(x_105);
lean_inc(x_107);
lean_inc_ref(x_104);
x_95 = x_104;
x_96 = x_107;
x_97 = x_105;
x_98 = x_108;
x_99 = x_111;
x_100 = x_103;
x_101 = x_115;
goto block_102;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 2;
x_13 = 0;
x_14 = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_12, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1_spec__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 5);
lean_inc(x_13);
x_14 = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___redArg(x_13, x_1, x_2, x_3, x_8, x_9, x_10, x_11);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
x_14 = lean_unbox(x_3);
x_15 = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1_spec__3(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = 2;
x_12 = 0;
x_13 = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1_spec__3(x_1, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_38; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_38 = l_Lean_Elab_isAbortExceptionId(x_14);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Exception_isInterrupt(x_1);
lean_dec_ref(x_1);
x_15 = x_39;
goto block_37;
}
else
{
lean_dec_ref(x_1);
x_15 = x_38;
goto block_37;
}
block_37:
{
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_InternalExceptionId_getName(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___closed__1);
x_19 = l_Lean_MessageData_ofName(x_17);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__1(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_34; 
x_22 = lean_ctor_get(x_16, 0);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
x_23 = x_16;
x_24 = x_34;
goto block_33;
}
else
{
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_8, 5);
lean_inc(x_25);
lean_dec_ref(x_8);
x_26 = lean_io_error_to_string(x_22);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_MessageData_ofFormat(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_29);
x_30 = x_23;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_14);
lean_dec_ref(x_8);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_15 = l_Lean_Elab_Tactic_focusAndDone___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = l_Lean_Exception_isInterrupt(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_15);
lean_inc_ref(x_8);
x_19 = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_19);
x_20 = l_Lean_Elab_admitGoal(x_13, x_18, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_20);
x_21 = l_Lean_Elab_Tactic_setGoals___redArg(x_14, x_3);
lean_dec(x_3);
return x_21;
}
else
{
lean_dec(x_14);
lean_dec(x_3);
return x_20;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
return x_19;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_15;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_11, 0);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_24 = x_11;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_closeUsingOrAdmit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
x_15 = lean_unbox(x_4);
x_16 = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__1(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__0));
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_saveState___boxed), 9, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1, &l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_17 = l_Lean_Exception_isInterrupt(x_13);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc(x_13);
x_18 = l_Lean_Exception_isRuntime(x_13);
x_14 = x_18;
goto block_16;
}
else
{
x_14 = x_17;
goto block_16;
}
block_16:
{
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_12);
x_15 = lean_apply_10(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_15;
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_tryCatch___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_13 = lean_apply_9(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_18 = l_Lean_Exception_isInterrupt(x_14);
if (x_18 == 0)
{
uint8_t x_19; 
lean_inc(x_14);
x_19 = l_Lean_Exception_isRuntime(x_14);
x_15 = x_19;
goto block_17;
}
else
{
x_15 = x_18;
goto block_17;
}
block_17:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_13);
x_16 = lean_apply_10(x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_16;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_tryCatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatchRestore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_saveState___redArg(x_4, x_6, x_8, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; uint8_t x_28; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_28 = l_Lean_Exception_isInterrupt(x_15);
if (x_28 == 0)
{
uint8_t x_29; 
lean_inc(x_15);
x_29 = l_Lean_Exception_isRuntime(x_15);
x_16 = x_29;
goto block_27;
}
else
{
x_16 = x_28;
goto block_27;
}
block_27:
{
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_14);
x_17 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_13, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = lean_apply_10(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_17, 0);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
x_20 = x_17;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = lean_ctor_get(x_12, 0);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
x_31 = x_12;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_12);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatchRestore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_tryCatchRestore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatchRestore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_saveState___redArg(x_5, x_7, x_9, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_15 = lean_apply_9(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_29 = l_Lean_Exception_isInterrupt(x_16);
if (x_29 == 0)
{
uint8_t x_30; 
lean_inc(x_16);
x_30 = l_Lean_Exception_isRuntime(x_16);
x_17 = x_30;
goto block_28;
}
else
{
x_17 = x_29;
goto block_28;
}
block_28:
{
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_15);
x_18 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_14, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = lean_apply_10(x_3, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_20 = lean_ctor_get(x_18, 0);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
x_21 = x_18;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_13, 0);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
x_32 = x_13;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryCatchRestore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_tryCatchRestore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_11 = lean_ctor_get(x_2, 0);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
x_12 = x_2;
x_13 = x_20;
goto block_19;
}
else
{
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
if (x_13 == 0)
{
x_15 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_11);
x_15 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_16; 
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_apply_9(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_withoutRecover___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withoutRecover___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withoutRecover___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withoutRecover(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRecover___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
x_13 = x_3;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_12);
x_15 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_16; 
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_1);
x_16 = lean_apply_9(x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRecover___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Elab_Tactic_withRecover___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRecover(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_withRecover___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRecover___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Elab_Tactic_withRecover(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Core_getMessageLog___redArg(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
x_13 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Core_setMessageLog___redArg(x_12, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_16 = x_15;
x_17 = x_22;
goto block_21;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_14);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_14);
x_24 = lean_ctor_get(x_15, 0);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
x_25 = x_15;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec_ref(x_13);
x_33 = l_Lean_Core_setMessageLog___redArg(x_12, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_40; 
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_33, 0);
lean_dec(x_41);
x_34 = x_33;
x_35 = x_40;
goto block_39;
}
else
{
lean_dec(x_33);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_32);
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_32);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_32);
x_42 = lean_ctor_get(x_33, 0);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
x_43 = x_33;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_11, 0);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
x_51 = x_11;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_11);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_withSuppressedMessages___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSuppressedMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withSuppressedMessages___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withSuppressedMessages(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCapturedMessages___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Core_getMessageLog___redArg(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
x_13 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Core_getMessageLog___redArg(x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_MessageLog_toList(x_12);
x_18 = l_Lean_Core_setMessageLog___redArg(x_12, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_29; 
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_18, 0);
lean_dec(x_30);
x_19 = x_18;
x_20 = x_29;
goto block_28;
}
else
{
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l_List_lengthTR___redArg(x_17);
lean_dec(x_17);
x_22 = l_Lean_MessageLog_toList(x_16);
lean_dec(x_16);
x_23 = l_List_drop___redArg(x_21, x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_24);
x_25 = x_19;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
x_31 = lean_ctor_get(x_18, 0);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
x_32 = x_18;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
x_39 = lean_ctor_get(x_15, 0);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
x_40 = x_15;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_12);
lean_dec(x_9);
x_47 = lean_ctor_get(x_13, 0);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
x_48 = x_13;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_11, 0);
x_62 = !lean_is_exclusive(x_11);
if (x_62 == 0)
{
x_56 = x_11;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_11);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCapturedMessages___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_withCapturedMessages___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCapturedMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withCapturedMessages___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCapturedMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withCapturedMessages(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_hasErrorMessages___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_3 = 2;
x_4 = l_Lean_instBEqMessageSeverity_beq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_hasErrorMessages___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_hasErrorMessages___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_hasErrorMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_hasErrorMessages___closed__0));
x_3 = l_List_any___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_hasErrorMessages___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_hasErrorMessages(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwOrLogErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwOrLogErrorAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_throwOrLogErrorAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwOrLogError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 5);
lean_inc(x_11);
x_12 = l_Lean_Elab_Tactic_throwOrLogErrorAt(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_throwOrLogError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_throwOrLogError(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_saveState___redArg(x_4, x_6, x_8, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = l_Lean_Elab_Tactic_withoutRecover___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; uint8_t x_29; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_29 = l_Lean_Exception_isInterrupt(x_15);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_15);
x_16 = x_30;
goto block_28;
}
else
{
lean_dec(x_15);
x_16 = x_29;
goto block_28;
}
block_28:
{
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_14);
x_17 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_13, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_17);
x_18 = lean_box(0);
x_19 = lean_apply_10(x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_17, 0);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
x_21 = x_17;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_12, 0);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
x_32 = x_12;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_orElse___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_saveState___redArg(x_5, x_7, x_9, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_15 = l_Lean_Elab_Tactic_withoutRecover___redArg(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_30; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_30 = l_Lean_Exception_isInterrupt(x_16);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Exception_isRuntime(x_16);
x_17 = x_31;
goto block_29;
}
else
{
lean_dec(x_16);
x_17 = x_30;
goto block_29;
}
block_29:
{
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_15);
x_18 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_14, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_18);
x_19 = lean_box(0);
x_20 = lean_apply_10(x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_21 = lean_ctor_get(x_18, 0);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
x_22 = x_18;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_32 = lean_ctor_get(x_13, 0);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
x_33 = x_13;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_orElse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_orElse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instOrElseTacticM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Lean_Elab_Tactic_instOrElseTacticM___closed__0));
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__1, &l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___closed__1);
x_14 = l_Lean_throwError___redArg(x_1, x_2, x_13);
x_15 = lean_apply_9(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instMonadExceptOfExceptionCoreM;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instMonadExceptOfExceptionCoreM;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__1);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__0, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__0_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__2);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__4, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__4_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__4);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__3);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5);
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__5);
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__7, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__7_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__7);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__6, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__6_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__6);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__8);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__10, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__10_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__10);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__9, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__9_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__9);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11);
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__11);
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__13, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__13_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__13);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__12, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__12_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__12);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__14);
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadExceptOf___redArg___lam__2), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__16, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__16_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__16);
x_2 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__15, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__15_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__15);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instAlternativeTacticM(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_239; 
x_1 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadTacticM___closed__1, &l_Lean_Elab_Tactic_instMonadTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_239 = !lean_is_exclusive(x_2);
if (x_239 == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_2, 1);
lean_dec(x_240);
x_7 = x_2;
x_8 = x_239;
goto block_238;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_239;
goto block_238;
}
block_238:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__2));
x_10 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__3));
lean_inc_ref(x_3);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_12, 0, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_15, 0, x_5);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_16, 0, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 3, x_15);
lean_ctor_set(x_7, 2, x_16);
lean_ctor_set(x_7, 1, x_9);
lean_ctor_set(x_7, 0, x_13);
x_17 = x_7;
goto block_236;
}
else
{
lean_object* x_237; 
x_237 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_237, 0, x_13);
lean_ctor_set(x_237, 1, x_9);
lean_ctor_set(x_237, 2, x_16);
lean_ctor_set(x_237, 3, x_15);
lean_ctor_set(x_237, 4, x_14);
x_17 = x_237;
goto block_236;
}
block_236:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_234; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = l_ReaderT_instMonad___redArg(x_18);
x_20 = lean_ctor_get(x_19, 0);
x_234 = !lean_is_exclusive(x_19);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_19, 1);
lean_dec(x_235);
x_21 = x_19;
x_22 = x_234;
goto block_233;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_231; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 2);
x_25 = lean_ctor_get(x_20, 3);
x_26 = lean_ctor_get(x_20, 4);
x_231 = !lean_is_exclusive(x_20);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_20, 1);
lean_dec(x_232);
x_27 = x_20;
x_28 = x_231;
goto block_230;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__4));
x_30 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__5));
lean_inc_ref(x_23);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_31, 0, x_23);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_32, 0, x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_26);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_35, 0, x_25);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_36, 0, x_24);
if (x_28 == 0)
{
lean_ctor_set(x_27, 4, x_34);
lean_ctor_set(x_27, 3, x_35);
lean_ctor_set(x_27, 2, x_36);
lean_ctor_set(x_27, 1, x_29);
lean_ctor_set(x_27, 0, x_33);
x_37 = x_27;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_33);
lean_ctor_set(x_229, 1, x_29);
lean_ctor_set(x_229, 2, x_36);
lean_ctor_set(x_229, 3, x_35);
lean_ctor_set(x_229, 4, x_34);
x_37 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_38; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_30);
lean_ctor_set(x_21, 0, x_37);
x_38 = x_21;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_37);
lean_ctor_set(x_227, 1, x_30);
x_38 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_224; 
x_39 = l_ReaderT_instMonad___redArg(x_38);
x_40 = lean_ctor_get(x_39, 0);
x_224 = !lean_is_exclusive(x_39);
if (x_224 == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_39, 1);
lean_dec(x_225);
x_41 = x_39;
x_42 = x_224;
goto block_223;
}
else
{
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = x_224;
goto block_223;
}
block_223:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_221; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 2);
x_45 = lean_ctor_get(x_40, 3);
x_46 = lean_ctor_get(x_40, 4);
x_221 = !lean_is_exclusive(x_40);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_40, 1);
lean_dec(x_222);
x_47 = x_40;
x_48 = x_221;
goto block_220;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_40);
x_47 = lean_box(0);
x_48 = x_221;
goto block_220;
}
block_220:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__6));
x_50 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__7));
lean_inc_ref(x_43);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_51, 0, x_43);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_52, 0, x_43);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_54, 0, x_46);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_55, 0, x_45);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_56, 0, x_44);
if (x_48 == 0)
{
lean_ctor_set(x_47, 4, x_54);
lean_ctor_set(x_47, 3, x_55);
lean_ctor_set(x_47, 2, x_56);
lean_ctor_set(x_47, 1, x_49);
lean_ctor_set(x_47, 0, x_53);
x_57 = x_47;
goto block_218;
}
else
{
lean_object* x_219; 
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_53);
lean_ctor_set(x_219, 1, x_49);
lean_ctor_set(x_219, 2, x_56);
lean_ctor_set(x_219, 3, x_55);
lean_ctor_set(x_219, 4, x_54);
x_57 = x_219;
goto block_218;
}
block_218:
{
lean_object* x_58; 
if (x_42 == 0)
{
lean_ctor_set(x_41, 1, x_50);
lean_ctor_set(x_41, 0, x_57);
x_58 = x_41;
goto block_216;
}
else
{
lean_object* x_217; 
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_57);
lean_ctor_set(x_217, 1, x_50);
x_58 = x_217;
goto block_216;
}
block_216:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_214; 
x_59 = l_ReaderT_instMonad___redArg(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_60, 0);
x_62 = lean_ctor_get(x_60, 2);
x_63 = lean_ctor_get(x_60, 3);
x_64 = lean_ctor_get(x_60, 4);
x_214 = !lean_is_exclusive(x_60);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_60, 1);
lean_dec(x_215);
x_65 = x_60;
x_66 = x_214;
goto block_213;
}
else
{
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_60);
x_65 = lean_box(0);
x_66 = x_214;
goto block_213;
}
block_213:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_67, 0, x_64);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_68, 0, x_63);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_69, 0, x_62);
lean_inc_ref(x_61);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_70, 0, x_61);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_61);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_73, 0, lean_box(0));
lean_closure_set(x_73, 1, lean_box(0));
lean_closure_set(x_73, 2, x_59);
if (x_66 == 0)
{
lean_ctor_set(x_65, 4, x_67);
lean_ctor_set(x_65, 3, x_68);
lean_ctor_set(x_65, 2, x_69);
lean_ctor_set(x_65, 1, x_73);
lean_ctor_set(x_65, 0, x_72);
x_74 = x_65;
goto block_211;
}
else
{
lean_object* x_212; 
x_212 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_212, 0, x_72);
lean_ctor_set(x_212, 1, x_73);
lean_ctor_set(x_212, 2, x_69);
lean_ctor_set(x_212, 3, x_68);
lean_ctor_set(x_212, 4, x_67);
x_74 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_209; 
x_75 = lean_ctor_get(x_1, 0);
x_209 = !lean_is_exclusive(x_1);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_1, 1);
lean_dec(x_210);
x_76 = x_1;
x_77 = x_209;
goto block_208;
}
else
{
lean_inc(x_75);
lean_dec(x_1);
x_76 = lean_box(0);
x_77 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_206; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 2);
x_80 = lean_ctor_get(x_75, 3);
x_81 = lean_ctor_get(x_75, 4);
x_206 = !lean_is_exclusive(x_75);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_75, 1);
lean_dec(x_207);
x_82 = x_75;
x_83 = x_206;
goto block_205;
}
else
{
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_75);
x_82 = lean_box(0);
x_83 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_inc_ref(x_78);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_84, 0, x_78);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_85, 0, x_78);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_87, 0, x_81);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_88, 0, x_80);
x_89 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_89, 0, x_79);
if (x_83 == 0)
{
lean_ctor_set(x_82, 4, x_87);
lean_ctor_set(x_82, 3, x_88);
lean_ctor_set(x_82, 2, x_89);
lean_ctor_set(x_82, 1, x_9);
lean_ctor_set(x_82, 0, x_86);
x_90 = x_82;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_204, 0, x_86);
lean_ctor_set(x_204, 1, x_9);
lean_ctor_set(x_204, 2, x_89);
lean_ctor_set(x_204, 3, x_88);
lean_ctor_set(x_204, 4, x_87);
x_90 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_91; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 1, x_10);
lean_ctor_set(x_76, 0, x_90);
x_91 = x_76;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_90);
lean_ctor_set(x_202, 1, x_10);
x_91 = x_202;
goto block_201;
}
block_201:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_199; 
x_92 = l_ReaderT_instMonad___redArg(x_91);
x_93 = lean_ctor_get(x_92, 0);
x_199 = !lean_is_exclusive(x_92);
if (x_199 == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_92, 1);
lean_dec(x_200);
x_94 = x_92;
x_95 = x_199;
goto block_198;
}
else
{
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_box(0);
x_95 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_196; 
x_96 = lean_ctor_get(x_93, 0);
x_97 = lean_ctor_get(x_93, 2);
x_98 = lean_ctor_get(x_93, 3);
x_99 = lean_ctor_get(x_93, 4);
x_196 = !lean_is_exclusive(x_93);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_93, 1);
lean_dec(x_197);
x_100 = x_93;
x_101 = x_196;
goto block_195;
}
else
{
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_93);
x_100 = lean_box(0);
x_101 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_inc_ref(x_96);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_102, 0, x_96);
x_103 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_103, 0, x_96);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_105, 0, x_99);
x_106 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_106, 0, x_98);
x_107 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_107, 0, x_97);
if (x_101 == 0)
{
lean_ctor_set(x_100, 4, x_105);
lean_ctor_set(x_100, 3, x_106);
lean_ctor_set(x_100, 2, x_107);
lean_ctor_set(x_100, 1, x_29);
lean_ctor_set(x_100, 0, x_104);
x_108 = x_100;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_104);
lean_ctor_set(x_194, 1, x_29);
lean_ctor_set(x_194, 2, x_107);
lean_ctor_set(x_194, 3, x_106);
lean_ctor_set(x_194, 4, x_105);
x_108 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_109; 
if (x_95 == 0)
{
lean_ctor_set(x_94, 1, x_30);
lean_ctor_set(x_94, 0, x_108);
x_109 = x_94;
goto block_191;
}
else
{
lean_object* x_192; 
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_108);
lean_ctor_set(x_192, 1, x_30);
x_109 = x_192;
goto block_191;
}
block_191:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_189; 
x_110 = l_ReaderT_instMonad___redArg(x_109);
x_111 = lean_ctor_get(x_110, 0);
x_189 = !lean_is_exclusive(x_110);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_110, 1);
lean_dec(x_190);
x_112 = x_110;
x_113 = x_189;
goto block_188;
}
else
{
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_box(0);
x_113 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_186; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_ctor_get(x_111, 2);
x_116 = lean_ctor_get(x_111, 3);
x_117 = lean_ctor_get(x_111, 4);
x_186 = !lean_is_exclusive(x_111);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_111, 1);
lean_dec(x_187);
x_118 = x_111;
x_119 = x_186;
goto block_185;
}
else
{
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_111);
x_118 = lean_box(0);
x_119 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_inc_ref(x_114);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_120, 0, x_114);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_121, 0, x_114);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_123, 0, x_117);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_124, 0, x_116);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_125, 0, x_115);
if (x_119 == 0)
{
lean_ctor_set(x_118, 4, x_123);
lean_ctor_set(x_118, 3, x_124);
lean_ctor_set(x_118, 2, x_125);
lean_ctor_set(x_118, 1, x_49);
lean_ctor_set(x_118, 0, x_122);
x_126 = x_118;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_122);
lean_ctor_set(x_184, 1, x_49);
lean_ctor_set(x_184, 2, x_125);
lean_ctor_set(x_184, 3, x_124);
lean_ctor_set(x_184, 4, x_123);
x_126 = x_184;
goto block_183;
}
block_183:
{
lean_object* x_127; 
if (x_113 == 0)
{
lean_ctor_set(x_112, 1, x_50);
lean_ctor_set(x_112, 0, x_126);
x_127 = x_112;
goto block_181;
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_126);
lean_ctor_set(x_182, 1, x_50);
x_127 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_179; 
x_128 = l_ReaderT_instMonad___redArg(x_127);
x_129 = lean_ctor_get(x_128, 0);
x_179 = !lean_is_exclusive(x_128);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_128, 1);
lean_dec(x_180);
x_130 = x_128;
x_131 = x_179;
goto block_178;
}
else
{
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_box(0);
x_131 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_176; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_ctor_get(x_129, 2);
x_134 = lean_ctor_get(x_129, 3);
x_135 = lean_ctor_get(x_129, 4);
x_176 = !lean_is_exclusive(x_129);
if (x_176 == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_129, 1);
lean_dec(x_177);
x_136 = x_129;
x_137 = x_176;
goto block_175;
}
else
{
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_129);
x_136 = lean_box(0);
x_137 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_138 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__8));
x_139 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__9));
lean_inc_ref(x_132);
x_140 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_140, 0, x_132);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_141, 0, x_132);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_143, 0, x_135);
x_144 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_144, 0, x_134);
x_145 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_145, 0, x_133);
if (x_137 == 0)
{
lean_ctor_set(x_136, 4, x_143);
lean_ctor_set(x_136, 3, x_144);
lean_ctor_set(x_136, 2, x_145);
lean_ctor_set(x_136, 1, x_138);
lean_ctor_set(x_136, 0, x_142);
x_146 = x_136;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_142);
lean_ctor_set(x_174, 1, x_138);
lean_ctor_set(x_174, 2, x_145);
lean_ctor_set(x_174, 3, x_144);
lean_ctor_set(x_174, 4, x_143);
x_146 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_147; 
if (x_131 == 0)
{
lean_ctor_set(x_130, 1, x_139);
lean_ctor_set(x_130, 0, x_146);
x_147 = x_130;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_146);
lean_ctor_set(x_172, 1, x_139);
x_147 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_168; 
x_148 = lean_obj_once(&l_Lean_Elab_Tactic_instAlternativeTacticM___closed__17, &l_Lean_Elab_Tactic_instAlternativeTacticM___closed__17_once, _init_l_Lean_Elab_Tactic_instAlternativeTacticM___closed__17);
x_149 = l_Lean_Elab_Term_instMonadMacroAdapterTermElabM;
x_150 = lean_ctor_get(x_149, 0);
x_168 = !lean_is_exclusive(x_149);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_149, 2);
lean_dec(x_169);
x_170 = lean_ctor_get(x_149, 1);
lean_dec(x_170);
x_151 = x_149;
x_152 = x_168;
goto block_167;
}
else
{
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_box(0);
x_152 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_153 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__2));
x_154 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__0));
x_155 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__1));
x_156 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_153, x_155, x_150);
x_157 = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(x_153, x_154, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc_ref(x_158);
lean_dec_ref(x_157);
x_159 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16_once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___closed__16);
lean_inc_ref(x_147);
x_160 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_159, x_147);
if (x_152 == 0)
{
lean_ctor_set(x_151, 2, x_160);
lean_ctor_set(x_151, 1, x_158);
lean_ctor_set(x_151, 0, x_148);
x_161 = x_151;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_148);
lean_ctor_set(x_166, 1, x_158);
lean_ctor_set(x_166, 2, x_160);
x_161 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instAlternativeTacticM___lam__0___boxed), 12, 2);
lean_closure_set(x_162, 0, x_147);
lean_closure_set(x_162, 1, x_161);
x_163 = ((lean_object*)(l_Lean_Elab_Tactic_instAlternativeTacticM___closed__18));
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_74);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_163);
return x_164;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_saveTacticInfoForToken___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_12);
x_15 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = ((lean_object*)(l_Lean_Elab_Tactic_saveTacticInfoForToken___closed__0));
x_19 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_18, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_15, 0);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
x_21 = x_15;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_saveTacticInfoForToken(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_40; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_17 = lean_ctor_get(x_6, 2);
x_18 = lean_ctor_get(x_6, 3);
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 5);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 3);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 4);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 5);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 7);
x_28 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 8);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 9);
x_30 = lean_ctor_get(x_6, 7);
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
x_31 = x_6;
x_32 = x_40;
goto block_39;
}
else
{
lean_inc(x_30);
lean_inc(x_26);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_31 = lean_box(0);
x_32 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_14);
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_34);
x_35 = x_31;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_17);
lean_ctor_set(x_38, 3, x_18);
lean_ctor_set(x_38, 4, x_19);
lean_ctor_set(x_38, 5, x_20);
lean_ctor_set(x_38, 6, x_26);
lean_ctor_set(x_38, 7, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*8, x_15);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 1, x_16);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 2, x_21);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 3, x_22);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 4, x_23);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 5, x_24);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 6, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 7, x_27);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 8, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*8 + 9, x_29);
x_35 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_36; 
x_36 = lean_apply_9(x_3, x_4, x_5, x_35, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_withMacroExpansion___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_137; 
x_13 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadTacticM___closed__1, &l_Lean_Elab_Tactic_instMonadTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
x_14 = lean_ctor_get(x_13, 0);
x_137 = !lean_is_exclusive(x_13);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_13, 1);
lean_dec(x_138);
x_15 = x_13;
x_16 = x_137;
goto block_136;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_134; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_ctor_get(x_14, 3);
x_20 = lean_ctor_get(x_14, 4);
x_134 = !lean_is_exclusive(x_14);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_14, 1);
lean_dec(x_135);
x_21 = x_14;
x_22 = x_134;
goto block_133;
}
else
{
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__2));
x_24 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__3));
lean_inc_ref(x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_20);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_29, 0, x_19);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_30, 0, x_18);
if (x_22 == 0)
{
lean_ctor_set(x_21, 4, x_28);
lean_ctor_set(x_21, 3, x_29);
lean_ctor_set(x_21, 2, x_30);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_27);
x_31 = x_21;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_27);
lean_ctor_set(x_132, 1, x_23);
lean_ctor_set(x_132, 2, x_30);
lean_ctor_set(x_132, 3, x_29);
lean_ctor_set(x_132, 4, x_28);
x_31 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_32; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_31);
x_32 = x_15;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_31);
lean_ctor_set(x_130, 1, x_24);
x_32 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_127; 
x_33 = l_ReaderT_instMonad___redArg(x_32);
x_34 = lean_ctor_get(x_33, 0);
x_127 = !lean_is_exclusive(x_33);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_33, 1);
lean_dec(x_128);
x_35 = x_33;
x_36 = x_127;
goto block_126;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_124; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 2);
x_39 = lean_ctor_get(x_34, 3);
x_40 = lean_ctor_get(x_34, 4);
x_124 = !lean_is_exclusive(x_34);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_34, 1);
lean_dec(x_125);
x_41 = x_34;
x_42 = x_124;
goto block_123;
}
else
{
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_34);
x_41 = lean_box(0);
x_42 = x_124;
goto block_123;
}
block_123:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__4));
x_44 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__5));
lean_inc_ref(x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_40);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_49, 0, x_39);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_50, 0, x_38);
if (x_42 == 0)
{
lean_ctor_set(x_41, 4, x_48);
lean_ctor_set(x_41, 3, x_49);
lean_ctor_set(x_41, 2, x_50);
lean_ctor_set(x_41, 1, x_43);
lean_ctor_set(x_41, 0, x_47);
x_51 = x_41;
goto block_121;
}
else
{
lean_object* x_122; 
x_122 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_122, 0, x_47);
lean_ctor_set(x_122, 1, x_43);
lean_ctor_set(x_122, 2, x_50);
lean_ctor_set(x_122, 3, x_49);
lean_ctor_set(x_122, 4, x_48);
x_51 = x_122;
goto block_121;
}
block_121:
{
lean_object* x_52; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 1, x_44);
lean_ctor_set(x_35, 0, x_51);
x_52 = x_35;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_51);
lean_ctor_set(x_120, 1, x_44);
x_52 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_117; 
x_53 = l_ReaderT_instMonad___redArg(x_52);
x_54 = lean_ctor_get(x_53, 0);
x_117 = !lean_is_exclusive(x_53);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_53, 1);
lean_dec(x_118);
x_55 = x_53;
x_56 = x_117;
goto block_116;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_114; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 2);
x_59 = lean_ctor_get(x_54, 3);
x_60 = lean_ctor_get(x_54, 4);
x_114 = !lean_is_exclusive(x_54);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_54, 1);
lean_dec(x_115);
x_61 = x_54;
x_62 = x_114;
goto block_113;
}
else
{
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
x_61 = lean_box(0);
x_62 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__6));
x_64 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__7));
lean_inc_ref(x_57);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_66, 0, x_57);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_68, 0, x_60);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_69, 0, x_59);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_70, 0, x_58);
if (x_62 == 0)
{
lean_ctor_set(x_61, 4, x_68);
lean_ctor_set(x_61, 3, x_69);
lean_ctor_set(x_61, 2, x_70);
lean_ctor_set(x_61, 1, x_63);
lean_ctor_set(x_61, 0, x_67);
x_71 = x_61;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_67);
lean_ctor_set(x_112, 1, x_63);
lean_ctor_set(x_112, 2, x_70);
lean_ctor_set(x_112, 3, x_69);
lean_ctor_set(x_112, 4, x_68);
x_71 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_72; 
if (x_56 == 0)
{
lean_ctor_set(x_55, 1, x_64);
lean_ctor_set(x_55, 0, x_71);
x_72 = x_55;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_71);
lean_ctor_set(x_110, 1, x_64);
x_72 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_107; 
x_73 = l_ReaderT_instMonad___redArg(x_72);
x_74 = lean_ctor_get(x_73, 0);
x_107 = !lean_is_exclusive(x_73);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_73, 1);
lean_dec(x_108);
x_75 = x_73;
x_76 = x_107;
goto block_106;
}
else
{
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_box(0);
x_76 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_104; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 2);
x_79 = lean_ctor_get(x_74, 3);
x_80 = lean_ctor_get(x_74, 4);
x_104 = !lean_is_exclusive(x_74);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_74, 1);
lean_dec(x_105);
x_81 = x_74;
x_82 = x_104;
goto block_103;
}
else
{
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_74);
x_81 = lean_box(0);
x_82 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_inc(x_2);
lean_inc(x_1);
x_83 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMacroExpansion___redArg___lam__0___boxed), 12, 3);
lean_closure_set(x_83, 0, x_1);
lean_closure_set(x_83, 1, x_2);
lean_closure_set(x_83, 2, x_3);
x_84 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__16));
x_85 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__8));
x_86 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__9));
lean_inc_ref(x_77);
x_87 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_87, 0, x_77);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_88, 0, x_77);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_90, 0, x_80);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_91, 0, x_79);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_92, 0, x_78);
if (x_82 == 0)
{
lean_ctor_set(x_81, 4, x_90);
lean_ctor_set(x_81, 3, x_91);
lean_ctor_set(x_81, 2, x_92);
lean_ctor_set(x_81, 1, x_85);
lean_ctor_set(x_81, 0, x_89);
x_93 = x_81;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_85);
lean_ctor_set(x_102, 2, x_92);
lean_ctor_set(x_102, 3, x_91);
lean_ctor_set(x_102, 4, x_90);
x_93 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_94; 
if (x_76 == 0)
{
lean_ctor_set(x_75, 1, x_86);
lean_ctor_set(x_75, 0, x_93);
x_94 = x_75;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_86);
x_94 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7);
x_96 = ((lean_object*)(l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__4));
x_97 = l_Lean_Elab_withMacroExpansionInfo___redArg(x_84, x_94, x_95, x_96, x_1, x_2, x_83);
x_98 = lean_apply_9(x_97, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_98;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_withMacroExpansion___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_138; 
x_14 = lean_obj_once(&l_Lean_Elab_Tactic_instMonadTacticM___closed__1, &l_Lean_Elab_Tactic_instMonadTacticM___closed__1_once, _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
x_15 = lean_ctor_get(x_14, 0);
x_138 = !lean_is_exclusive(x_14);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_14, 1);
lean_dec(x_139);
x_16 = x_14;
x_17 = x_138;
goto block_137;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_135; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 2);
x_20 = lean_ctor_get(x_15, 3);
x_21 = lean_ctor_get(x_15, 4);
x_135 = !lean_is_exclusive(x_15);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_15, 1);
lean_dec(x_136);
x_22 = x_15;
x_23 = x_135;
goto block_134;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__2));
x_25 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__3));
lean_inc_ref(x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_26, 0, x_18);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_21);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_20);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_31, 0, x_19);
if (x_23 == 0)
{
lean_ctor_set(x_22, 4, x_29);
lean_ctor_set(x_22, 3, x_30);
lean_ctor_set(x_22, 2, x_31);
lean_ctor_set(x_22, 1, x_24);
lean_ctor_set(x_22, 0, x_28);
x_32 = x_22;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_28);
lean_ctor_set(x_133, 1, x_24);
lean_ctor_set(x_133, 2, x_31);
lean_ctor_set(x_133, 3, x_30);
lean_ctor_set(x_133, 4, x_29);
x_32 = x_133;
goto block_132;
}
block_132:
{
lean_object* x_33; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_32);
x_33 = x_16;
goto block_130;
}
else
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_32);
lean_ctor_set(x_131, 1, x_25);
x_33 = x_131;
goto block_130;
}
block_130:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_128; 
x_34 = l_ReaderT_instMonad___redArg(x_33);
x_35 = lean_ctor_get(x_34, 0);
x_128 = !lean_is_exclusive(x_34);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_34, 1);
lean_dec(x_129);
x_36 = x_34;
x_37 = x_128;
goto block_127;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_125; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 2);
x_40 = lean_ctor_get(x_35, 3);
x_41 = lean_ctor_get(x_35, 4);
x_125 = !lean_is_exclusive(x_35);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_35, 1);
lean_dec(x_126);
x_42 = x_35;
x_43 = x_125;
goto block_124;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
x_42 = lean_box(0);
x_43 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__4));
x_45 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__5));
lean_inc_ref(x_38);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_38);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_49, 0, x_41);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_40);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_51, 0, x_39);
if (x_43 == 0)
{
lean_ctor_set(x_42, 4, x_49);
lean_ctor_set(x_42, 3, x_50);
lean_ctor_set(x_42, 2, x_51);
lean_ctor_set(x_42, 1, x_44);
lean_ctor_set(x_42, 0, x_48);
x_52 = x_42;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_123, 0, x_48);
lean_ctor_set(x_123, 1, x_44);
lean_ctor_set(x_123, 2, x_51);
lean_ctor_set(x_123, 3, x_50);
lean_ctor_set(x_123, 4, x_49);
x_52 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_53; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_45);
lean_ctor_set(x_36, 0, x_52);
x_53 = x_36;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_52);
lean_ctor_set(x_121, 1, x_45);
x_53 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_118; 
x_54 = l_ReaderT_instMonad___redArg(x_53);
x_55 = lean_ctor_get(x_54, 0);
x_118 = !lean_is_exclusive(x_54);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_54, 1);
lean_dec(x_119);
x_56 = x_54;
x_57 = x_118;
goto block_117;
}
else
{
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_115; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 2);
x_60 = lean_ctor_get(x_55, 3);
x_61 = lean_ctor_get(x_55, 4);
x_115 = !lean_is_exclusive(x_55);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_55, 1);
lean_dec(x_116);
x_62 = x_55;
x_63 = x_115;
goto block_114;
}
else
{
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_55);
x_62 = lean_box(0);
x_63 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__6));
x_65 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__7));
lean_inc_ref(x_58);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_66, 0, x_58);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_67, 0, x_58);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_69, 0, x_61);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_70, 0, x_60);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_71, 0, x_59);
if (x_63 == 0)
{
lean_ctor_set(x_62, 4, x_69);
lean_ctor_set(x_62, 3, x_70);
lean_ctor_set(x_62, 2, x_71);
lean_ctor_set(x_62, 1, x_64);
lean_ctor_set(x_62, 0, x_68);
x_72 = x_62;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_68);
lean_ctor_set(x_113, 1, x_64);
lean_ctor_set(x_113, 2, x_71);
lean_ctor_set(x_113, 3, x_70);
lean_ctor_set(x_113, 4, x_69);
x_72 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_73; 
if (x_57 == 0)
{
lean_ctor_set(x_56, 1, x_65);
lean_ctor_set(x_56, 0, x_72);
x_73 = x_56;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_72);
lean_ctor_set(x_111, 1, x_65);
x_73 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_108; 
x_74 = l_ReaderT_instMonad___redArg(x_73);
x_75 = lean_ctor_get(x_74, 0);
x_108 = !lean_is_exclusive(x_74);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_74, 1);
lean_dec(x_109);
x_76 = x_74;
x_77 = x_108;
goto block_107;
}
else
{
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_box(0);
x_77 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_105; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 2);
x_80 = lean_ctor_get(x_75, 3);
x_81 = lean_ctor_get(x_75, 4);
x_105 = !lean_is_exclusive(x_75);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_75, 1);
lean_dec(x_106);
x_82 = x_75;
x_83 = x_105;
goto block_104;
}
else
{
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_75);
x_82 = lean_box(0);
x_83 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_inc(x_3);
lean_inc(x_2);
x_84 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMacroExpansion___redArg___lam__0___boxed), 12, 3);
lean_closure_set(x_84, 0, x_2);
lean_closure_set(x_84, 1, x_3);
lean_closure_set(x_84, 2, x_4);
x_85 = ((lean_object*)(l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__16));
x_86 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__8));
x_87 = ((lean_object*)(l_Lean_Elab_Tactic_instMonadTacticM___closed__9));
lean_inc_ref(x_78);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_88, 0, x_78);
x_89 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_89, 0, x_78);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_91, 0, x_81);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_92, 0, x_80);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_93, 0, x_79);
if (x_83 == 0)
{
lean_ctor_set(x_82, 4, x_91);
lean_ctor_set(x_82, 3, x_92);
lean_ctor_set(x_82, 2, x_93);
lean_ctor_set(x_82, 1, x_86);
lean_ctor_set(x_82, 0, x_90);
x_94 = x_82;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_86);
lean_ctor_set(x_103, 2, x_93);
lean_ctor_set(x_103, 3, x_92);
lean_ctor_set(x_103, 4, x_91);
x_94 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_95; 
if (x_77 == 0)
{
lean_ctor_set(x_76, 1, x_87);
lean_ctor_set(x_76, 0, x_94);
x_95 = x_76;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set(x_101, 1, x_87);
x_95 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_obj_once(&l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7, &l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_withTacticInfoContext___redArg___closed__7);
x_97 = ((lean_object*)(l_Lean_Elab_Tactic_withMacroExpansion___redArg___closed__4));
x_98 = l_Lean_Elab_withMacroExpansionInfo___redArg(x_85, x_95, x_96, x_97, x_2, x_3, x_84);
x_99 = lean_apply_9(x_98, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_99;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMacroExpansion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_withMacroExpansion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_39; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_16 = lean_ctor_get(x_5, 2);
x_17 = lean_ctor_get(x_5, 3);
x_18 = lean_ctor_get(x_5, 4);
x_19 = lean_ctor_get(x_5, 5);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 3);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 4);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 5);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 6);
x_25 = lean_ctor_get(x_5, 6);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 7);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 8);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 9);
x_29 = lean_ctor_get(x_5, 7);
x_39 = !lean_is_exclusive(x_5);
if (x_39 == 0)
{
x_30 = x_5;
x_31 = x_39;
goto block_38;
}
else
{
lean_inc(x_29);
lean_inc(x_25);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_13);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_33);
x_34 = x_30;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_16);
lean_ctor_set(x_37, 3, x_17);
lean_ctor_set(x_37, 4, x_18);
lean_ctor_set(x_37, 5, x_19);
lean_ctor_set(x_37, 6, x_25);
lean_ctor_set(x_37, 7, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 1, x_15);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 2, x_20);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 3, x_21);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 4, x_22);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 5, x_23);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 6, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 7, x_26);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 8, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 9, x_28);
x_34 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_35; 
x_35 = l_Lean_Elab_Tactic_evalTactic(x_2, x_3, x_4, x_34, x_6, x_7, x_8, x_9, x_10);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_adaptExpander___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_13);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_2);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg___lam__0___boxed), 12, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_12 = lean_apply_10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_13);
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_adaptExpander___lam__0___boxed), 11, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg(x_2, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 0);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
x_17 = x_12;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_adaptExpander___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_adaptExpander(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_adaptExpander_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_take(x_2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_st_ref_set(x_2, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_pushGoal___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_pushGoal___redArg(x_1, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_pushGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoals___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_take(x_2);
x_5 = l_List_appendTR___redArg(x_1, x_4);
x_6 = lean_st_ref_set(x_2, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoals___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_pushGoals___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_pushGoals___redArg(x_1, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_pushGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_pushGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_take(x_2);
x_5 = l_List_appendTR___redArg(x_4, x_1);
x_6 = lean_st_ref_set(x_2, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_appendGoals___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_appendGoals___redArg(x_1, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_appendGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_22; 
x_8 = l_Lean_Elab_Tactic_getGoals___redArg(x_2);
x_9 = lean_ctor_get(x_8, 0);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
x_10 = x_8;
x_11 = x_22;
goto block_21;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_22;
goto block_21;
}
block_21:
{
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = lean_st_ref_take(x_2);
lean_dec(x_13);
x_14 = l_List_appendTR___redArg(x_1, x_12);
x_15 = lean_st_ref_set(x_2, x_14);
x_16 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_16);
x_17 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
lean_object* x_20; 
lean_del_object(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_20 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(x_3, x_4, x_5, x_6);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_1, x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_replaceMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_replaceMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___redArg(x_3, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_pruneSolvedGoals_spec__0___redArg(x_9, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = l_Lean_Elab_Tactic_setGoals___redArg(x_1, x_2);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_15 = x_14;
x_16 = x_21;
goto block_20;
}
else
{
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_9);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_9);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_inc(x_10);
lean_dec_ref(x_1);
lean_dec(x_9);
x_1 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___redArg(x_1, x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Elab_Tactic_getGoals___redArg(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getMainGoal_loop___redArg(x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_popMainGoal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_9, x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_11 = x_10;
x_12 = x_17;
goto block_16;
}
else
{
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_8);
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_8);
x_19 = lean_ctor_get(x_10, 0);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
x_20 = x_10;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_popMainGoal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_popMainGoal___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_popMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_popMainGoal___redArg(x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_popMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_popMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_MVarId_getDecl(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_10 = lean_ctor_get(x_7, 0);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
x_11 = x_7;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_getMainDecl___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl___redArg(x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_getMainDecl___redArg(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_16; 
x_8 = lean_ctor_get(x_7, 0);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
x_9 = x_7;
x_10 = x_16;
goto block_15;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_7, 0);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
x_18 = x_7;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_getMainTag___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainTag___redArg(x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainTag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl___redArg(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_12, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_10, 0);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
x_15 = x_10;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getMainTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
x_15 = x_13;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_11, 0);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
x_15 = x_11;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_withMainContext___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withMainContext___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withMainContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_withMainContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = l_Lean_Elab_Tactic_getGoals___redArg(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Tactic_setGoals___redArg(x_26, x_4);
lean_dec_ref(x_27);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_28 = l_Lean_Elab_Tactic_evalTactic(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec_ref(x_28);
x_29 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_29);
x_30 = l_Lean_Elab_Tactic_getGoals___redArg(x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Elab_Tactic_setGoals___redArg(x_13, x_4);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_33 = x_32;
x_34 = x_39;
goto block_38;
}
else
{
lean_dec(x_32);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_31);
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_31);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
lean_dec_ref(x_29);
x_14 = x_41;
goto block_24;
}
}
else
{
lean_object* x_42; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
lean_dec_ref(x_28);
x_14 = x_42;
goto block_24;
}
block_24:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = l_Lean_Elab_Tactic_setGoals___redArg(x_13, x_4);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_16 = x_15;
x_17 = x_22;
goto block_21;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_14);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_14);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTacticAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAtRaw(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_setGoals___redArg(x_13, x_4);
lean_dec_ref(x_14);
lean_inc(x_4);
x_15 = l_Lean_Elab_Tactic_evalTactic(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = l_Lean_Elab_Tactic_getGoals___redArg(x_4);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
lean_dec(x_4);
x_17 = lean_ctor_get(x_15, 0);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
x_18 = x_15;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalTacticAtRaw___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTacticAtRaw(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_1, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc(x_10);
x_11 = l_Lean_Meta_getMVars(x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_box(0);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_14 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_27; 
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_14, 0);
lean_dec(x_28);
x_15 = x_14;
x_16 = x_27;
goto block_26;
}
else
{
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = x_27;
goto block_26;
}
block_26:
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasExprMVar(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_18 = lean_box(0);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_del_object(x_15);
x_22 = lean_obj_once(&l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__1, &l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___closed__1);
x_23 = l_Lean_indentExpr(x_10);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_24, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_25;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_29 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_30 = x_14;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_11, 0);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
x_38 = x_11;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_ensureHasNoMVars___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_ensureHasNoMVars___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_ensureHasNoMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
if (x_3 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
x_12 = x_4;
x_13 = x_7;
x_14 = x_8;
x_15 = x_9;
x_16 = x_10;
goto block_47;
}
else
{
lean_object* x_48; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
x_48 = l_Lean_Elab_Tactic_ensureHasNoMVars___redArg(x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_48) == 0)
{
lean_dec_ref(x_48);
x_12 = x_4;
x_13 = x_7;
x_14 = x_8;
x_15 = x_9;
x_16 = x_10;
goto block_47;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_48;
}
}
block_47:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_2);
lean_inc(x_18);
x_19 = lean_checked_assign(x_18, x_2, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__1, &l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__1);
x_23 = l_Lean_indentExpr(x_2);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_obj_once(&l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__3, &l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_closeMainGoal___redArg___closed__3);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_Meta_throwTacticEx___redArg(x_1, x_18, x_27, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_18);
lean_dec_ref(x_2);
lean_dec(x_1);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_29, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_19, 0);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
x_32 = x_19;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_17, 0);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
x_40 = x_17;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_17);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l_Lean_Elab_Tactic_closeMainGoal___redArg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_closeMainGoal___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_closeMainGoal(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, lean_box(0));
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_11, 0);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
x_15 = x_11;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaMAtMain___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaMAtMain___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = l_Lean_Elab_Tactic_withMainContext___redArg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_liftMetaMAtMain(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_16, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_18 = x_17;
x_19 = x_24;
goto block_23;
}
else
{
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_15);
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_15);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_17, 0);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
x_27 = x_17;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_34 = lean_ctor_get(x_13, 0);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
x_35 = x_13;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_11, 0);
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
x_43 = x_11;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_11);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTacticAux___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = l_Lean_Elab_Tactic_withMainContext___redArg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_liftMetaTacticAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_14, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_16 = x_15;
x_17 = x_23;
goto block_22;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_25 = lean_ctor_get(x_13, 0);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
x_26 = x_13;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_11, 0);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
x_34 = x_11;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTactic___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lam__0___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_17, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_19, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_21 = lean_ctor_get(x_13, 0);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
x_22 = x_13;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_11, 0);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
x_30 = x_11;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTactic1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic1___lam__0___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaTactic1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTactic1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_13 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_14, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_16 = x_15;
x_17 = x_23;
goto block_22;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_19 = x_16;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
else
{
return x_15;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_13;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_11, 0);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
x_26 = x_11;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaFinishingTactic___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic___lam__0___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaFinishingTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_13 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
x_15 = x_13;
x_16 = x_22;
goto block_21;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_17);
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_52; 
x_23 = lean_ctor_get(x_13, 0);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
x_24 = x_13;
x_25 = x_52;
goto block_51;
}
else
{
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_26; 
lean_inc(x_23);
if (x_25 == 0)
{
x_26 = x_24;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_23);
x_26 = x_50;
goto block_49;
}
block_49:
{
uint8_t x_27; uint8_t x_47; 
x_47 = l_Lean_Exception_isInterrupt(x_23);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Exception_isRuntime(x_23);
x_27 = x_48;
goto block_46;
}
else
{
lean_dec(x_23);
x_27 = x_47;
goto block_46;
}
block_46:
{
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_26);
x_28 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_12, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_28, 0);
lean_dec(x_37);
x_29 = x_28;
x_30 = x_36;
goto block_35;
}
else
{
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_31);
x_32 = x_29;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
x_38 = lean_ctor_get(x_28, 0);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
x_39 = x_28;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_28);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_26;
}
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_11, 0);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
x_54 = x_11;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_tryTactic_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_tryTactic_x3f___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_tryTactic_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_13 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_14 = x_13;
x_15 = x_22;
goto block_21;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_box(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_53; 
x_24 = lean_ctor_get(x_13, 0);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
x_25 = x_13;
x_26 = x_53;
goto block_52;
}
else
{
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_box(0);
x_26 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_27; 
lean_inc(x_24);
if (x_26 == 0)
{
x_27 = x_25;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_24);
x_27 = x_51;
goto block_50;
}
block_50:
{
uint8_t x_28; uint8_t x_48; 
x_48 = l_Lean_Exception_isInterrupt(x_24);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Exception_isRuntime(x_24);
x_28 = x_49;
goto block_47;
}
else
{
lean_dec(x_24);
x_28 = x_48;
goto block_47;
}
block_47:
{
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec_ref(x_27);
x_29 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_12, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_29, 0);
lean_dec(x_38);
x_30 = x_29;
x_31 = x_37;
goto block_36;
}
else
{
lean_dec(x_29);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(x_28);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_39 = lean_ctor_get(x_29, 0);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
x_40 = x_29;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_27;
}
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_11, 0);
x_61 = !lean_is_exclusive(x_11);
if (x_61 == 0)
{
x_55 = x_11;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_11);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_tryTactic___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_tryTactic___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tryTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_tryTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_8 = l_Lean_MetavarContext_isAnonymousMVar(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_2 = x_7;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_32; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
x_10 = x_5;
x_11 = x_32;
goto block_31;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = x_32;
goto block_31;
}
block_31:
{
uint8_t x_12; 
lean_inc(x_9);
x_12 = l_Lean_MetavarContext_isAnonymousMVar(x_9, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
if (x_11 == 0)
{
x_13 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_9);
x_13 = x_16;
goto block_15;
}
block_15:
{
x_4 = x_7;
x_5 = x_13;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_26; 
x_17 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_eq(x_1, x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_8);
lean_inc(x_2);
x_27 = lean_name_append_index_after(x_2, x_8);
lean_inc(x_3);
x_28 = l_Lean_Name_append(x_3, x_27);
x_29 = l_Lean_MetavarContext_setMVarUserName(x_9, x_6, x_28);
x_18 = x_8;
x_19 = x_29;
goto block_25;
}
else
{
lean_object* x_30; 
lean_inc(x_3);
x_30 = l_Lean_MetavarContext_setMVarUserName(x_9, x_6, x_3);
x_18 = x_8;
x_19 = x_30;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_nat_add(x_18, x_17);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_20);
x_21 = x_10;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_19);
x_21 = x_24;
goto block_23;
}
block_23:
{
x_4 = x_7;
x_5 = x_21;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_43; 
x_13 = lean_st_ref_get(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___redArg(x_14, x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
x_18 = x_16;
x_19 = x_43;
goto block_42;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_41; 
x_20 = lean_st_ref_take(x_9);
x_21 = lean_ctor_get(x_20, 0);
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 2);
x_24 = lean_ctor_get(x_20, 3);
x_25 = lean_ctor_get(x_20, 4);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
x_26 = x_20;
x_27 = x_41;
goto block_40;
}
else
{
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
x_30 = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___redArg(x_17, x_2, x_1, x_3, x_29);
lean_dec(x_17);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_31);
x_32 = x_26;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_22);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_24);
lean_ctor_set(x_39, 4, x_25);
x_32 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_st_ref_set(x_9, x_32);
x_34 = lean_box(0);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_34);
x_35 = x_18;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___redArg(x_1, x_3, x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___redArg(x_1, x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_tagUntaggedGoals_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isIdent(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Lean_Elab_Tactic_getNameOfIdent_x27___closed__1));
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getId(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_apply_3(x_2, lean_box(0), x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_withCaseRef___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_array_push(x_10, x_3);
x_12 = lean_array_push(x_11, x_4);
x_13 = ((lean_object*)(l_Lean_Elab_Tactic_evalTactic___lam__2___closed__5));
x_14 = lean_box(2);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_12);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withCaseRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_8);
lean_closure_set(x_16, 2, x_5);
x_17 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCaseRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_withCaseRef___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3237160090u);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__8_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__11_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__10_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__9_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__13_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__12_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__11_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__11_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__11_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__14_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__13_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__13_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__13_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__0_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_));
x_3 = 0;
x_4 = lean_obj_once(&l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__14_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__14_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__14_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_);
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTactic_handleEx___lam__0___closed__1));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn___closed__3_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_instMonadTacticM = _init_l_Lean_Elab_Tactic_instMonadTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM);
res = l_Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_1336121563____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_tacticElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_docString__1()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_tacticElabAttribute___regBuiltin_Lean_Elab_Tactic_tacticElabAttribute_declRange__3()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM);
l_Lean_Elab_Tactic_instAlternativeTacticM = _init_l_Lean_Elab_Tactic_instAlternativeTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instAlternativeTacticM);
res = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_3237160090____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_initFn_00___x40_Lean_Elab_Tactic_Basic_778036212____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
