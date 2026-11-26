// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Driver
// Imports: public import Lean.Elab.Tactic.Meta public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.Solve public import Lean.Meta.Sym.Grind import Lean.Elab.Tactic.RenameInaccessibles
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_renameInaccessibles(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_cleanupVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3_spec__7(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__4_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__8_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9_value;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "vc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_run___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_e_30_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg___lam__0(lean_object* v_x_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
v___x_56_ = lean_apply_7(v_x_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, lean_box(0));
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg___lam__0___boxed(lean_object* v_x_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg___lam__0(v_x_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg(lean_object* v_mvarId_66_, lean_object* v_x_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___f_75_; lean_object* v___x_76_; 
lean_inc(v___y_69_);
lean_inc_ref(v___y_68_);
v___f_75_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_75_, 0, v_x_67_);
lean_closure_set(v___f_75_, 1, v___y_68_);
lean_closure_set(v___f_75_, 2, v___y_69_);
v___x_76_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_66_, v___f_75_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
if (lean_obj_tag(v___x_76_) == 0)
{
return v___x_76_;
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg___boxed(lean_object* v_mvarId_85_, lean_object* v_x_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg(v_mvarId_85_, v_x_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4(lean_object* v_00_u03b1_95_, lean_object* v_mvarId_96_, lean_object* v_x_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg(v_mvarId_96_, v_x_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___boxed(lean_object* v_00_u03b1_106_, lean_object* v_mvarId_107_, lean_object* v_x_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4(v_00_u03b1_106_, v_mvarId_107_, v_x_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(lean_object* v___x_117_, uint8_t v___x_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_box(0), v___x_117_, v___x_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0___boxed(lean_object* v___x_127_, lean_object* v___x_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
uint8_t v___x_20744__boxed_136_; lean_object* v_res_137_; 
v___x_20744__boxed_136_ = lean_unbox(v___x_128_);
v_res_137_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0(v___x_127_, v___x_20744__boxed_136_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(lean_object* v___x_138_, lean_object* v_mv_139_, lean_object* v_fst_140_, lean_object* v_snd_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_toCold_149_; lean_object* v_currRecDepth_150_; lean_object* v_ref_151_; uint16_t v_optionFlags_152_; uint8_t v_suppressElabErrors_153_; uint8_t v_checkDeprecated_154_; uint8_t v_isRecordingDeps_155_; lean_object* v_ref_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_toCold_149_ = lean_ctor_get(v___y_146_, 0);
v_currRecDepth_150_ = lean_ctor_get(v___y_146_, 1);
v_ref_151_ = lean_ctor_get(v___y_146_, 2);
v_optionFlags_152_ = lean_ctor_get_uint16(v___y_146_, sizeof(void*)*3);
v_suppressElabErrors_153_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 2);
v_checkDeprecated_154_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 3);
v_isRecordingDeps_155_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 4);
v_ref_156_ = l_Lean_replaceRef(v___x_138_, v_ref_151_);
lean_inc(v_currRecDepth_150_);
lean_inc_ref(v_toCold_149_);
v___x_157_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_157_, 0, v_toCold_149_);
lean_ctor_set(v___x_157_, 1, v_currRecDepth_150_);
lean_ctor_set(v___x_157_, 2, v_ref_156_);
lean_ctor_set_uint16(v___x_157_, sizeof(void*)*3, v_optionFlags_152_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*3 + 2, v_suppressElabErrors_153_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*3 + 3, v_checkDeprecated_154_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*3 + 4, v_isRecordingDeps_155_);
v___x_158_ = l_Lean_Elab_Tactic_renameInaccessibles(v_mv_139_, v_fst_140_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___x_157_, v___y_147_);
lean_dec_ref_known(v___x_157_, 3);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_n(v_a_159_, 2);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = l_Lean_MVarId_getType(v_a_159_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_177_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_177_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_177_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_177_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_176_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___x_175_; 
v___x_167_ = 1;
v___x_168_ = lean_box(0);
v___x_169_ = lean_box(v___x_167_);
v___x_170_ = lean_box(v___x_167_);
v___x_171_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(v___x_171_, 0, v_snd_141_);
lean_closure_set(v___x_171_, 1, v___x_166_);
lean_closure_set(v___x_171_, 2, v___x_169_);
lean_closure_set(v___x_171_, 3, v___x_170_);
lean_closure_set(v___x_171_, 4, v___x_168_);
v___x_172_ = 1;
v___x_173_ = lean_box(v___x_172_);
v___f_174_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__0___boxed), 9, 2);
lean_closure_set(v___f_174_, 0, v___x_171_);
lean_closure_set(v___f_174_, 1, v___x_173_);
v___x_175_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__4___redArg(v_a_159_, v___f_174_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_175_;
}
}
}
else
{
lean_dec(v_a_159_);
lean_dec(v_snd_141_);
return v___x_160_;
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec(v_snd_141_);
v_a_178_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_158_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_158_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed(lean_object* v___x_186_, lean_object* v_mv_187_, lean_object* v_fst_188_, lean_object* v_snd_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1(v___x_186_, v_mv_187_, v_fst_188_, v_snd_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___x_186_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__2(lean_object* v_elabRhs_198_, lean_object* v_termCtx_199_, lean_object* v___x_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Elab_Term_TermElabM_run___redArg(v_elabRhs_198_, v_termCtx_199_, v___x_200_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_217_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_217_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_217_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_fst_213_; lean_object* v___x_215_; 
v_fst_213_ = lean_ctor_get(v_a_209_, 0);
lean_inc(v_fst_213_);
lean_dec(v_a_209_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v_fst_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_fst_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_a_218_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_208_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_208_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__2___boxed(lean_object* v_elabRhs_226_, lean_object* v_termCtx_227_, lean_object* v___x_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__2(v_elabRhs_226_, v_termCtx_227_, v___x_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13_spec__14___redArg(lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
lean_object* v_ks_241_; lean_object* v_vs_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_266_; 
v_ks_241_ = lean_ctor_get(v_x_237_, 0);
v_vs_242_ = lean_ctor_get(v_x_237_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_x_237_);
if (v_isSharedCheck_266_ == 0)
{
v___x_244_ = v_x_237_;
v_isShared_245_ = v_isSharedCheck_266_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_vs_242_);
lean_inc(v_ks_241_);
lean_dec(v_x_237_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_266_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = lean_array_get_size(v_ks_241_);
v___x_247_ = lean_nat_dec_lt(v_x_238_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
lean_dec(v_x_238_);
v___x_248_ = lean_array_push(v_ks_241_, v_x_239_);
v___x_249_ = lean_array_push(v_vs_242_, v_x_240_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_249_);
lean_ctor_set(v___x_244_, 0, v___x_248_);
v___x_251_ = v___x_244_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v_k_x27_253_; uint8_t v___x_254_; 
v_k_x27_253_ = lean_array_fget_borrowed(v_ks_241_, v_x_238_);
v___x_254_ = l_Lean_instBEqMVarId_beq(v_x_239_, v_k_x27_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_256_; 
if (v_isShared_245_ == 0)
{
v___x_256_ = v___x_244_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_ks_241_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_vs_242_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_x_238_, v___x_257_);
lean_dec(v_x_238_);
v_x_237_ = v___x_256_;
v_x_238_ = v___x_258_;
goto _start;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = lean_array_fset(v_ks_241_, v_x_238_, v_x_239_);
v___x_262_ = lean_array_fset(v_vs_242_, v_x_238_, v_x_240_);
lean_dec(v_x_238_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_262_);
lean_ctor_set(v___x_244_, 0, v___x_261_);
v___x_264_ = v___x_244_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13___redArg(lean_object* v_n_267_, lean_object* v_k_268_, lean_object* v_v_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13_spec__14___redArg(v_n_267_, v___x_270_, v_k_268_, v_v_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg(lean_object* v_x_273_, size_t v_x_274_, size_t v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
lean_object* v_es_278_; size_t v___x_279_; size_t v___x_280_; lean_object* v_j_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_es_278_ = lean_ctor_get(v_x_273_, 0);
v___x_279_ = ((size_t)31ULL);
v___x_280_ = lean_usize_land(v_x_274_, v___x_279_);
v_j_281_ = lean_usize_to_nat(v___x_280_);
v___x_282_ = lean_array_get_size(v_es_278_);
v___x_283_ = lean_nat_dec_lt(v_j_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_dec(v_j_281_);
lean_dec(v_x_277_);
lean_dec(v_x_276_);
return v_x_273_;
}
else
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_322_; 
lean_inc_ref(v_es_278_);
v_isSharedCheck_322_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_322_ == 0)
{
lean_object* v_unused_323_; 
v_unused_323_ = lean_ctor_get(v_x_273_, 0);
lean_dec(v_unused_323_);
v___x_285_ = v_x_273_;
v_isShared_286_ = v_isSharedCheck_322_;
goto v_resetjp_284_;
}
else
{
lean_dec(v_x_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_322_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_v_287_; lean_object* v___x_288_; lean_object* v_xs_x27_289_; lean_object* v___y_291_; 
v_v_287_ = lean_array_fget(v_es_278_, v_j_281_);
v___x_288_ = lean_box(0);
v_xs_x27_289_ = lean_array_fset(v_es_278_, v_j_281_, v___x_288_);
switch(lean_obj_tag(v_v_287_))
{
case 0:
{
lean_object* v_key_296_; lean_object* v_val_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_307_; 
v_key_296_ = lean_ctor_get(v_v_287_, 0);
v_val_297_ = lean_ctor_get(v_v_287_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_v_287_);
if (v_isSharedCheck_307_ == 0)
{
v___x_299_ = v_v_287_;
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_val_297_);
lean_inc(v_key_296_);
lean_dec(v_v_287_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_instBEqMVarId_beq(v_x_276_, v_key_296_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_del_object(v___x_299_);
v___x_302_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_296_, v_val_297_, v_x_276_, v_x_277_);
v___x_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
v___y_291_ = v___x_303_;
goto v___jp_290_;
}
else
{
lean_object* v___x_305_; 
lean_dec(v_val_297_);
lean_dec(v_key_296_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_x_277_);
lean_ctor_set(v___x_299_, 0, v_x_276_);
v___x_305_ = v___x_299_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_x_276_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_x_277_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
v___y_291_ = v___x_305_;
goto v___jp_290_;
}
}
}
}
case 1:
{
lean_object* v_node_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_320_; 
v_node_308_ = lean_ctor_get(v_v_287_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v_v_287_);
if (v_isSharedCheck_320_ == 0)
{
v___x_310_ = v_v_287_;
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_node_308_);
lean_dec(v_v_287_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_312_ = ((size_t)5ULL);
v___x_313_ = lean_usize_shift_right(v_x_274_, v___x_312_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_add(v_x_275_, v___x_314_);
v___x_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg(v_node_308_, v___x_313_, v___x_315_, v_x_276_, v_x_277_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_316_);
v___x_318_ = v___x_310_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
v___y_291_ = v___x_318_;
goto v___jp_290_;
}
}
}
default: 
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_x_276_);
lean_ctor_set(v___x_321_, 1, v_x_277_);
v___y_291_ = v___x_321_;
goto v___jp_290_;
}
}
v___jp_290_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_array_fset(v_xs_x27_289_, v_j_281_, v___y_291_);
lean_dec(v_j_281_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_292_);
v___x_294_ = v___x_285_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
else
{
lean_object* v_ks_324_; lean_object* v_vs_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_343_; 
v_ks_324_ = lean_ctor_get(v_x_273_, 0);
v_vs_325_ = lean_ctor_get(v_x_273_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_343_ == 0)
{
v___x_327_ = v_x_273_;
v_isShared_328_ = v_isSharedCheck_343_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_vs_325_);
lean_inc(v_ks_324_);
lean_dec(v_x_273_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_343_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_ks_324_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_vs_325_);
v___x_330_ = v_reuseFailAlloc_342_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v_newNode_331_; size_t v___x_332_; uint8_t v___x_333_; 
v_newNode_331_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13___redArg(v___x_330_, v_x_276_, v_x_277_);
v___x_332_ = ((size_t)7ULL);
v___x_333_ = lean_usize_dec_le(v___x_332_, v_x_275_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_331_);
v___x_335_ = lean_unsigned_to_nat(4u);
v___x_336_ = lean_nat_dec_lt(v___x_334_, v___x_335_);
lean_dec(v___x_334_);
if (v___x_336_ == 0)
{
lean_object* v_ks_337_; lean_object* v_vs_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_ks_337_ = lean_ctor_get(v_newNode_331_, 0);
lean_inc_ref(v_ks_337_);
v_vs_338_ = lean_ctor_get(v_newNode_331_, 1);
lean_inc_ref(v_vs_338_);
lean_dec_ref(v_newNode_331_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg___closed__0);
v___x_341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___redArg(v_x_275_, v_ks_337_, v_vs_338_, v___x_339_, v___x_340_);
lean_dec_ref(v_vs_338_);
lean_dec_ref(v_ks_337_);
return v___x_341_;
}
else
{
return v_newNode_331_;
}
}
else
{
return v_newNode_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___redArg(size_t v_depth_344_, lean_object* v_keys_345_, lean_object* v_vals_346_, lean_object* v_i_347_, lean_object* v_entries_348_){
_start:
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = lean_array_get_size(v_keys_345_);
v___x_350_ = lean_nat_dec_lt(v_i_347_, v___x_349_);
if (v___x_350_ == 0)
{
lean_dec(v_i_347_);
return v_entries_348_;
}
else
{
lean_object* v_k_351_; lean_object* v_v_352_; uint64_t v___x_353_; size_t v_h_354_; size_t v___x_355_; lean_object* v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v_h_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_k_351_ = lean_array_fget_borrowed(v_keys_345_, v_i_347_);
v_v_352_ = lean_array_fget_borrowed(v_vals_346_, v_i_347_);
v___x_353_ = l_Lean_instHashableMVarId_hash(v_k_351_);
v_h_354_ = lean_uint64_to_usize(v___x_353_);
v___x_355_ = ((size_t)5ULL);
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_sub(v_depth_344_, v___x_357_);
v___x_359_ = lean_usize_mul(v___x_355_, v___x_358_);
v_h_360_ = lean_usize_shift_right(v_h_354_, v___x_359_);
v___x_361_ = lean_nat_add(v_i_347_, v___x_356_);
lean_dec(v_i_347_);
lean_inc(v_v_352_);
lean_inc(v_k_351_);
v___x_362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg(v_entries_348_, v_h_360_, v_depth_344_, v_k_351_, v_v_352_);
v_i_347_ = v___x_361_;
v_entries_348_ = v___x_362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___redArg___boxed(lean_object* v_depth_364_, lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_i_367_, lean_object* v_entries_368_){
_start:
{
size_t v_depth_boxed_369_; lean_object* v_res_370_; 
v_depth_boxed_369_ = lean_unbox_usize(v_depth_364_);
lean_dec(v_depth_364_);
v_res_370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___redArg(v_depth_boxed_369_, v_keys_365_, v_vals_366_, v_i_367_, v_entries_368_);
lean_dec_ref(v_vals_366_);
lean_dec_ref(v_keys_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
size_t v_x_20996__boxed_376_; size_t v_x_20997__boxed_377_; lean_object* v_res_378_; 
v_x_20996__boxed_376_ = lean_unbox_usize(v_x_372_);
lean_dec(v_x_372_);
v_x_20997__boxed_377_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_res_378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg(v_x_371_, v_x_20996__boxed_376_, v_x_20997__boxed_377_, v_x_374_, v_x_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6___redArg(lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
uint64_t v___x_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_382_ = l_Lean_instHashableMVarId_hash(v_x_380_);
v___x_383_ = lean_uint64_to_usize(v___x_382_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg(v_x_379_, v___x_383_, v___x_384_, v_x_380_, v_x_381_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(lean_object* v_mvarId_386_, lean_object* v_val_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_mctx_391_; lean_object* v_cache_392_; lean_object* v_zetaDeltaFVarIds_393_; lean_object* v_postponed_394_; lean_object* v_diag_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_424_; 
v___x_390_ = lean_st_ref_take(v___y_388_);
v_mctx_391_ = lean_ctor_get(v___x_390_, 0);
v_cache_392_ = lean_ctor_get(v___x_390_, 1);
v_zetaDeltaFVarIds_393_ = lean_ctor_get(v___x_390_, 2);
v_postponed_394_ = lean_ctor_get(v___x_390_, 3);
v_diag_395_ = lean_ctor_get(v___x_390_, 4);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_424_ == 0)
{
v___x_397_ = v___x_390_;
v_isShared_398_ = v_isSharedCheck_424_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_diag_395_);
lean_inc(v_postponed_394_);
lean_inc(v_zetaDeltaFVarIds_393_);
lean_inc(v_cache_392_);
lean_inc(v_mctx_391_);
lean_dec(v___x_390_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_424_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_depth_399_; lean_object* v_levelAssignDepth_400_; lean_object* v_lmvarCounter_401_; lean_object* v_mvarCounter_402_; lean_object* v_lDecls_403_; lean_object* v_decls_404_; lean_object* v_userNames_405_; lean_object* v_lAssignment_406_; lean_object* v_eAssignment_407_; lean_object* v_dAssignment_408_; lean_object* v_instanceTypedMVars_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_423_; 
v_depth_399_ = lean_ctor_get(v_mctx_391_, 0);
v_levelAssignDepth_400_ = lean_ctor_get(v_mctx_391_, 1);
v_lmvarCounter_401_ = lean_ctor_get(v_mctx_391_, 2);
v_mvarCounter_402_ = lean_ctor_get(v_mctx_391_, 3);
v_lDecls_403_ = lean_ctor_get(v_mctx_391_, 4);
v_decls_404_ = lean_ctor_get(v_mctx_391_, 5);
v_userNames_405_ = lean_ctor_get(v_mctx_391_, 6);
v_lAssignment_406_ = lean_ctor_get(v_mctx_391_, 7);
v_eAssignment_407_ = lean_ctor_get(v_mctx_391_, 8);
v_dAssignment_408_ = lean_ctor_get(v_mctx_391_, 9);
v_instanceTypedMVars_409_ = lean_ctor_get(v_mctx_391_, 10);
v_isSharedCheck_423_ = !lean_is_exclusive(v_mctx_391_);
if (v_isSharedCheck_423_ == 0)
{
v___x_411_ = v_mctx_391_;
v_isShared_412_ = v_isSharedCheck_423_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_instanceTypedMVars_409_);
lean_inc(v_dAssignment_408_);
lean_inc(v_eAssignment_407_);
lean_inc(v_lAssignment_406_);
lean_inc(v_userNames_405_);
lean_inc(v_decls_404_);
lean_inc(v_lDecls_403_);
lean_inc(v_mvarCounter_402_);
lean_inc(v_lmvarCounter_401_);
lean_inc(v_levelAssignDepth_400_);
lean_inc(v_depth_399_);
lean_dec(v_mctx_391_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_423_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_413_ = lean_box(0);
v___x_414_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6___redArg(v_eAssignment_407_, v_mvarId_386_, v_val_387_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 8, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_depth_399_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_levelAssignDepth_400_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_lmvarCounter_401_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_mvarCounter_402_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_lDecls_403_);
lean_ctor_set(v_reuseFailAlloc_422_, 5, v_decls_404_);
lean_ctor_set(v_reuseFailAlloc_422_, 6, v_userNames_405_);
lean_ctor_set(v_reuseFailAlloc_422_, 7, v_lAssignment_406_);
lean_ctor_set(v_reuseFailAlloc_422_, 8, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_422_, 9, v_dAssignment_408_);
lean_ctor_set(v_reuseFailAlloc_422_, 10, v_instanceTypedMVars_409_);
v___x_416_ = v_reuseFailAlloc_422_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_416_);
v___x_418_ = v___x_397_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_cache_392_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_zetaDeltaFVarIds_393_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v_postponed_394_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v_diag_395_);
v___x_418_ = v_reuseFailAlloc_421_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_st_ref_put(v___y_388_, v___x_418_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_413_);
return v___x_420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object* v_mvarId_425_, lean_object* v_val_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_425_, v_val_426_, v___y_427_);
lean_dec(v___y_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_box(0);
return v___x_432_;
}
else
{
lean_object* v_key_433_; lean_object* v_value_434_; lean_object* v_tail_435_; uint8_t v___x_436_; 
v_key_433_ = lean_ctor_get(v_x_431_, 0);
v_value_434_ = lean_ctor_get(v_x_431_, 1);
v_tail_435_ = lean_ctor_get(v_x_431_, 2);
v___x_436_ = lean_nat_dec_eq(v_key_433_, v_a_430_);
if (v___x_436_ == 0)
{
v_x_431_ = v_tail_435_;
goto _start;
}
else
{
lean_object* v___x_438_; 
lean_inc(v_value_434_);
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v_value_434_);
return v___x_438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec(v_a_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_buckets_444_; lean_object* v___x_445_; uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v___x_448_; uint64_t v_fold_449_; uint64_t v___x_450_; uint64_t v___x_451_; uint64_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; size_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_buckets_444_ = lean_ctor_get(v_m_442_, 1);
v___x_445_ = lean_array_get_size(v_buckets_444_);
v___x_446_ = lean_uint64_of_nat(v_a_443_);
v___x_447_ = 32ULL;
v___x_448_ = lean_uint64_shift_right(v___x_446_, v___x_447_);
v_fold_449_ = lean_uint64_xor(v___x_446_, v___x_448_);
v___x_450_ = 16ULL;
v___x_451_ = lean_uint64_shift_right(v_fold_449_, v___x_450_);
v___x_452_ = lean_uint64_xor(v_fold_449_, v___x_451_);
v___x_453_ = lean_uint64_to_usize(v___x_452_);
v___x_454_ = lean_usize_of_nat(v___x_445_);
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_sub(v___x_454_, v___x_455_);
v___x_457_ = lean_usize_land(v___x_453_, v___x_456_);
v___x_458_ = lean_array_uget_borrowed(v_buckets_444_, v___x_457_);
v___x_459_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_443_, v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_m_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__7(lean_object* v_msgData_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; lean_object* v_env_470_; uint8_t v___x_471_; lean_object* v_env_472_; lean_object* v___x_473_; lean_object* v_toCold_474_; lean_object* v_mctx_475_; lean_object* v_lctx_476_; lean_object* v_options_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_469_ = lean_st_ref_get(v___y_467_);
v_env_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref(v_env_470_);
lean_dec(v___x_469_);
v___x_471_ = 0;
v_env_472_ = l_Lean_Environment_setRecordingDeps(v_env_470_, v___x_471_);
v___x_473_ = lean_st_ref_get(v___y_465_);
v_toCold_474_ = lean_ctor_get(v___y_466_, 0);
v_mctx_475_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref(v_mctx_475_);
lean_dec(v___x_473_);
v_lctx_476_ = lean_ctor_get(v___y_464_, 2);
v_options_477_ = lean_ctor_get(v_toCold_474_, 2);
lean_inc_ref(v_options_477_);
lean_inc_ref(v_lctx_476_);
v___x_478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_478_, 0, v_env_472_);
lean_ctor_set(v___x_478_, 1, v_mctx_475_);
lean_ctor_set(v___x_478_, 2, v_lctx_476_);
lean_ctor_set(v___x_478_, 3, v_options_477_);
v___x_479_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_msgData_463_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__7___boxed(lean_object* v_msgData_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__7(v_msgData_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_487_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__8(lean_object* v_opts_488_, lean_object* v_opt_489_){
_start:
{
lean_object* v_name_490_; lean_object* v_defValue_491_; lean_object* v_map_492_; lean_object* v___x_493_; 
v_name_490_ = lean_ctor_get(v_opt_489_, 0);
v_defValue_491_ = lean_ctor_get(v_opt_489_, 1);
v_map_492_ = lean_ctor_get(v_opts_488_, 0);
v___x_493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_492_, v_name_490_);
if (lean_obj_tag(v___x_493_) == 0)
{
uint8_t v___x_494_; 
v___x_494_ = lean_unbox(v_defValue_491_);
return v___x_494_;
}
else
{
lean_object* v_val_495_; 
v_val_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_493_, 1);
if (lean_obj_tag(v_val_495_) == 1)
{
uint8_t v_v_496_; 
v_v_496_ = lean_ctor_get_uint8(v_val_495_, 0);
lean_dec_ref_known(v_val_495_, 0);
return v_v_496_;
}
else
{
uint8_t v___x_497_; 
lean_dec(v_val_495_);
v___x_497_ = lean_unbox(v_defValue_491_);
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_opts_498_, lean_object* v_opt_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__8(v_opts_498_, v_opt_499_);
lean_dec_ref(v_opt_499_);
lean_dec_ref(v_opts_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0(uint8_t v_suppressElabErrors_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_511_) == 1)
{
lean_object* v_pre_512_; 
v_pre_512_ = lean_ctor_get(v_x_511_, 0);
switch(lean_obj_tag(v_pre_512_))
{
case 1:
{
lean_object* v_pre_513_; 
v_pre_513_ = lean_ctor_get(v_pre_512_, 0);
switch(lean_obj_tag(v_pre_513_))
{
case 0:
{
lean_object* v_str_514_; lean_object* v_str_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_str_514_ = lean_ctor_get(v_x_511_, 1);
v_str_515_ = lean_ctor_get(v_pre_512_, 1);
v___x_516_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__0));
v___x_517_ = lean_string_dec_eq(v_str_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__1));
v___x_519_ = lean_string_dec_eq(v_str_515_, v___x_518_);
if (v___x_519_ == 0)
{
return v___x_519_;
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__2));
v___x_521_ = lean_string_dec_eq(v_str_514_, v___x_520_);
if (v___x_521_ == 0)
{
return v___x_521_;
}
else
{
return v_suppressElabErrors_510_;
}
}
}
else
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__3));
v___x_523_ = lean_string_dec_eq(v_str_514_, v___x_522_);
if (v___x_523_ == 0)
{
return v___x_523_;
}
else
{
return v_suppressElabErrors_510_;
}
}
}
case 1:
{
lean_object* v_pre_524_; 
v_pre_524_ = lean_ctor_get(v_pre_513_, 0);
if (lean_obj_tag(v_pre_524_) == 0)
{
lean_object* v_str_525_; lean_object* v_str_526_; lean_object* v_str_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_str_525_ = lean_ctor_get(v_x_511_, 1);
v_str_526_ = lean_ctor_get(v_pre_512_, 1);
v_str_527_ = lean_ctor_get(v_pre_513_, 1);
v___x_528_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__4));
v___x_529_ = lean_string_dec_eq(v_str_527_, v___x_528_);
if (v___x_529_ == 0)
{
return v___x_529_;
}
else
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__5));
v___x_531_ = lean_string_dec_eq(v_str_526_, v___x_530_);
if (v___x_531_ == 0)
{
return v___x_531_;
}
else
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__6));
v___x_533_ = lean_string_dec_eq(v_str_525_, v___x_532_);
if (v___x_533_ == 0)
{
return v___x_533_;
}
else
{
return v_suppressElabErrors_510_;
}
}
}
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 0;
return v___x_534_;
}
}
default: 
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
}
}
case 0:
{
lean_object* v_str_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_str_536_ = lean_ctor_get(v_x_511_, 1);
v___x_537_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___closed__7));
v___x_538_ = lean_string_dec_eq(v_str_536_, v___x_537_);
if (v___x_538_ == 0)
{
return v___x_538_;
}
else
{
return v_suppressElabErrors_510_;
}
}
default: 
{
uint8_t v___x_539_; 
v___x_539_ = 0;
return v___x_539_;
}
}
}
else
{
uint8_t v___x_540_; 
v___x_540_ = 0;
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_541_, lean_object* v_x_542_){
_start:
{
uint8_t v_suppressElabErrors_boxed_543_; uint8_t v_res_544_; lean_object* v_r_545_; 
v_suppressElabErrors_boxed_543_ = lean_unbox(v_suppressElabErrors_541_);
v_res_544_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0(v_suppressElabErrors_boxed_543_, v_x_542_);
lean_dec(v_x_542_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg(lean_object* v_ref_547_, lean_object* v_msgData_548_, uint8_t v_severity_549_, uint8_t v_isSilent_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; uint8_t v___y_562_; uint8_t v___y_563_; lean_object* v_toCold_564_; lean_object* v___y_565_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; uint8_t v___y_598_; uint8_t v___y_599_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_621_; lean_object* v___y_622_; uint8_t v___y_623_; lean_object* v___y_624_; uint8_t v___y_625_; uint8_t v___y_626_; lean_object* v___y_627_; uint8_t v___y_631_; uint8_t v___y_632_; uint8_t v___x_642_; uint8_t v___y_644_; uint8_t v___x_650_; 
v___x_642_ = 2;
v___x_650_ = l_Lean_instBEqMessageSeverity_beq(v_severity_549_, v___x_642_);
if (v___x_650_ == 0)
{
v___y_644_ = v___x_650_;
goto v___jp_643_;
}
else
{
uint8_t v___x_651_; 
lean_inc_ref(v_msgData_548_);
v___x_651_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_548_);
if (v___x_651_ == 0)
{
v___y_644_ = v___x_651_;
goto v___jp_643_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref(v_msgData_548_);
v___x_652_ = lean_box(0);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
v___jp_556_:
{
lean_object* v_currNamespace_566_; lean_object* v_openDecls_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v_env_572_; lean_object* v_nextMacroScope_573_; lean_object* v_ngen_574_; lean_object* v_auxDeclNGen_575_; lean_object* v_traceState_576_; lean_object* v_cache_577_; lean_object* v_recordedDeps_578_; lean_object* v_messages_579_; lean_object* v_infoState_580_; lean_object* v_snapshotTasks_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_592_; 
v_currNamespace_566_ = lean_ctor_get(v_toCold_564_, 4);
v_openDecls_567_ = lean_ctor_get(v_toCold_564_, 5);
lean_inc(v_openDecls_567_);
lean_inc(v_currNamespace_566_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v_currNamespace_566_);
lean_ctor_set(v___x_568_, 1, v_openDecls_567_);
v___x_569_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___y_559_);
lean_inc_ref(v___y_561_);
lean_inc_ref(v___y_560_);
v___x_570_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_570_, 0, v___y_560_);
lean_ctor_set(v___x_570_, 1, v___y_557_);
lean_ctor_set(v___x_570_, 2, v___y_558_);
lean_ctor_set(v___x_570_, 3, v___y_561_);
lean_ctor_set(v___x_570_, 4, v___x_569_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*5, v___y_563_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*5 + 1, v___y_562_);
lean_ctor_set_uint8(v___x_570_, sizeof(void*)*5 + 2, v_isSilent_550_);
v___x_571_ = lean_st_ref_take(v___y_565_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
v_nextMacroScope_573_ = lean_ctor_get(v___x_571_, 1);
v_ngen_574_ = lean_ctor_get(v___x_571_, 2);
v_auxDeclNGen_575_ = lean_ctor_get(v___x_571_, 3);
v_traceState_576_ = lean_ctor_get(v___x_571_, 4);
v_cache_577_ = lean_ctor_get(v___x_571_, 5);
v_recordedDeps_578_ = lean_ctor_get(v___x_571_, 6);
v_messages_579_ = lean_ctor_get(v___x_571_, 7);
v_infoState_580_ = lean_ctor_get(v___x_571_, 8);
v_snapshotTasks_581_ = lean_ctor_get(v___x_571_, 9);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_592_ == 0)
{
v___x_583_ = v___x_571_;
v_isShared_584_ = v_isSharedCheck_592_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_snapshotTasks_581_);
lean_inc(v_infoState_580_);
lean_inc(v_messages_579_);
lean_inc(v_recordedDeps_578_);
lean_inc(v_cache_577_);
lean_inc(v_traceState_576_);
lean_inc(v_auxDeclNGen_575_);
lean_inc(v_ngen_574_);
lean_inc(v_nextMacroScope_573_);
lean_inc(v_env_572_);
lean_dec(v___x_571_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_592_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_585_ = lean_box(0);
v___x_586_ = l_Lean_MessageLog_add(v___x_570_, v_messages_579_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 7, v___x_586_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_env_572_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v_nextMacroScope_573_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_ngen_574_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_auxDeclNGen_575_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_traceState_576_);
lean_ctor_set(v_reuseFailAlloc_591_, 5, v_cache_577_);
lean_ctor_set(v_reuseFailAlloc_591_, 6, v_recordedDeps_578_);
lean_ctor_set(v_reuseFailAlloc_591_, 7, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_591_, 8, v_infoState_580_);
lean_ctor_set(v_reuseFailAlloc_591_, 9, v_snapshotTasks_581_);
v___x_588_ = v_reuseFailAlloc_591_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_st_ref_put(v___y_565_, v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_585_);
return v___x_590_;
}
}
}
v___jp_593_:
{
lean_object* v_fileName_602_; lean_object* v_fileMap_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_619_; 
v_fileName_602_ = lean_ctor_get(v___y_596_, 0);
v_fileMap_603_ = lean_ctor_get(v___y_596_, 1);
v___x_604_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_548_);
v___x_605_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__7(v___x_604_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_619_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_619_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_619_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_inc_ref_n(v_fileMap_603_, 2);
v___x_610_ = l_Lean_FileMap_toPosition(v_fileMap_603_, v___y_597_);
lean_dec(v___y_597_);
v___x_611_ = l_Lean_FileMap_toPosition(v_fileMap_603_, v___y_601_);
lean_dec(v___y_601_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
v___x_613_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___closed__0));
if (v___y_598_ == 0)
{
lean_del_object(v___x_608_);
lean_dec_ref(v___y_595_);
v___y_557_ = v___x_610_;
v___y_558_ = v___x_612_;
v___y_559_ = v_a_606_;
v___y_560_ = v_fileName_602_;
v___y_561_ = v___x_613_;
v___y_562_ = v___y_600_;
v___y_563_ = v___y_599_;
v_toCold_564_ = v___y_594_;
v___y_565_ = v___y_554_;
goto v___jp_556_;
}
else
{
uint8_t v___x_614_; 
lean_inc(v_a_606_);
v___x_614_ = l_Lean_MessageData_hasTag(v___y_595_, v_a_606_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_617_; 
lean_dec_ref_known(v___x_612_, 1);
lean_dec_ref(v___x_610_);
lean_dec(v_a_606_);
v___x_615_ = lean_box(0);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_615_);
v___x_617_ = v___x_608_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
else
{
lean_del_object(v___x_608_);
v___y_557_ = v___x_610_;
v___y_558_ = v___x_612_;
v___y_559_ = v_a_606_;
v___y_560_ = v_fileName_602_;
v___y_561_ = v___x_613_;
v___y_562_ = v___y_600_;
v___y_563_ = v___y_599_;
v_toCold_564_ = v___y_594_;
v___y_565_ = v___y_554_;
goto v___jp_556_;
}
}
}
}
v___jp_620_:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Syntax_getTailPos_x3f(v___y_624_, v___y_626_);
lean_dec(v___y_624_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_inc(v___y_627_);
v___y_594_ = v___y_621_;
v___y_595_ = v___y_622_;
v___y_596_ = v___y_621_;
v___y_597_ = v___y_627_;
v___y_598_ = v___y_623_;
v___y_599_ = v___y_626_;
v___y_600_ = v___y_625_;
v___y_601_ = v___y_627_;
goto v___jp_593_;
}
else
{
lean_object* v_val_629_; 
v_val_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v___x_628_, 1);
v___y_594_ = v___y_621_;
v___y_595_ = v___y_622_;
v___y_596_ = v___y_621_;
v___y_597_ = v___y_627_;
v___y_598_ = v___y_623_;
v___y_599_ = v___y_626_;
v___y_600_ = v___y_625_;
v___y_601_ = v_val_629_;
goto v___jp_593_;
}
}
v___jp_630_:
{
lean_object* v_toCold_633_; lean_object* v_ref_634_; uint8_t v_suppressElabErrors_635_; lean_object* v___x_636_; lean_object* v___f_637_; lean_object* v_ref_638_; lean_object* v___x_639_; 
v_toCold_633_ = lean_ctor_get(v___y_553_, 0);
v_ref_634_ = lean_ctor_get(v___y_553_, 2);
v_suppressElabErrors_635_ = lean_ctor_get_uint8(v___y_553_, sizeof(void*)*3 + 2);
v___x_636_ = lean_box(v_suppressElabErrors_635_);
v___f_637_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_637_, 0, v___x_636_);
v_ref_638_ = l_Lean_replaceRef(v_ref_547_, v_ref_634_);
v___x_639_ = l_Lean_Syntax_getPos_x3f(v_ref_638_, v___y_631_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_640_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___y_621_ = v_toCold_633_;
v___y_622_ = v___f_637_;
v___y_623_ = v_suppressElabErrors_635_;
v___y_624_ = v_ref_638_;
v___y_625_ = v___y_632_;
v___y_626_ = v___y_631_;
v___y_627_ = v___x_640_;
goto v___jp_620_;
}
else
{
lean_object* v_val_641_; 
v_val_641_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v___x_639_, 1);
v___y_621_ = v_toCold_633_;
v___y_622_ = v___f_637_;
v___y_623_ = v_suppressElabErrors_635_;
v___y_624_ = v_ref_638_;
v___y_625_ = v___y_632_;
v___y_626_ = v___y_631_;
v___y_627_ = v_val_641_;
goto v___jp_620_;
}
}
v___jp_643_:
{
uint8_t v___x_645_; uint8_t v___x_646_; 
v___x_645_ = 1;
v___x_646_ = l_Lean_instBEqMessageSeverity_beq(v_severity_549_, v___x_645_);
if (v___x_646_ == 0)
{
v___y_631_ = v___y_644_;
v___y_632_ = v_severity_549_;
goto v___jp_630_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_553_);
v___x_648_ = l_Lean_warningAsError;
v___x_649_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5_spec__8(v___x_647_, v___x_648_);
lean_dec_ref(v___x_647_);
if (v___x_649_ == 0)
{
v___y_631_ = v___y_644_;
v___y_632_ = v_severity_549_;
goto v___jp_630_;
}
else
{
v___y_631_ = v___y_644_;
v___y_632_ = v___x_642_;
goto v___jp_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_ref_654_, lean_object* v_msgData_655_, lean_object* v_severity_656_, lean_object* v_isSilent_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v_severity_boxed_663_; uint8_t v_isSilent_boxed_664_; lean_object* v_res_665_; 
v_severity_boxed_663_ = lean_unbox(v_severity_656_);
v_isSilent_boxed_664_ = lean_unbox(v_isSilent_657_);
v_res_665_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg(v_ref_654_, v_msgData_655_, v_severity_boxed_663_, v_isSilent_boxed_664_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v_ref_654_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3_spec__7(lean_object* v_msgData_666_, uint8_t v_severity_667_, uint8_t v_isSilent_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_ref_676_; lean_object* v___x_677_; 
v_ref_676_ = lean_ctor_get(v___y_673_, 2);
v___x_677_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg(v_ref_676_, v_msgData_666_, v_severity_667_, v_isSilent_668_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3_spec__7___boxed(lean_object* v_msgData_678_, lean_object* v_severity_679_, lean_object* v_isSilent_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v_severity_boxed_688_; uint8_t v_isSilent_boxed_689_; lean_object* v_res_690_; 
v_severity_boxed_688_ = lean_unbox(v_severity_679_);
v_isSilent_boxed_689_ = lean_unbox(v_isSilent_680_);
v_res_690_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3_spec__7(v_msgData_678_, v_severity_boxed_688_, v_isSilent_boxed_689_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3(lean_object* v_msgData_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
uint8_t v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = 2;
v___x_700_ = 0;
v___x_701_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3_spec__7(v_msgData_691_, v___x_699_, v___x_700_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3___boxed(lean_object* v_msgData_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3(v_msgData_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_ref_711_, lean_object* v_msgData_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; 
v___x_720_ = 2;
v___x_721_ = 0;
v___x_722_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg(v_ref_711_, v_msgData_712_, v___x_720_, v___x_721_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_ref_723_, lean_object* v_msgData_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(v_ref_723_, v_msgData_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v_ref_723_);
return v_res_732_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__1(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__0));
v___x_735_ = l_Lean_stringToMessageData(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(lean_object* v_ex_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
if (lean_obj_tag(v_ex_736_) == 0)
{
lean_object* v_ref_747_; lean_object* v_msg_748_; lean_object* v___x_749_; 
v_ref_747_ = lean_ctor_get(v_ex_736_, 0);
lean_inc(v_ref_747_);
v_msg_748_ = lean_ctor_get(v_ex_736_, 1);
lean_inc_ref(v_msg_748_);
lean_dec_ref_known(v_ex_736_, 2);
v___x_749_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2(v_ref_747_, v_msg_748_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v_ref_747_);
return v___x_749_;
}
else
{
lean_object* v_id_750_; uint8_t v___x_751_; 
v_id_750_ = lean_ctor_get(v_ex_736_, 0);
lean_inc(v_id_750_);
v___x_751_ = l_Lean_Elab_isAbortExceptionId(v_id_750_);
if (v___x_751_ == 0)
{
uint8_t v___x_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_777_; 
v___x_752_ = l_Lean_Exception_isInterrupt(v_ex_736_);
v_isSharedCheck_777_ = !lean_is_exclusive(v_ex_736_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; lean_object* v_unused_779_; 
v_unused_778_ = lean_ctor_get(v_ex_736_, 1);
lean_dec(v_unused_778_);
v_unused_779_ = lean_ctor_get(v_ex_736_, 0);
lean_dec(v_unused_779_);
v___x_754_ = v_ex_736_;
v_isShared_755_ = v_isSharedCheck_777_;
goto v_resetjp_753_;
}
else
{
lean_dec(v_ex_736_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_777_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
if (v___x_752_ == 0)
{
lean_object* v_ref_756_; lean_object* v___x_757_; 
v_ref_756_ = lean_ctor_get(v___y_741_, 2);
v___x_757_ = l_Lean_InternalExceptionId_getName(v_id_750_);
lean_dec(v_id_750_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_del_object(v___x_754_);
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___closed__1);
v___x_760_ = l_Lean_MessageData_ofName(v_a_758_);
v___x_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__3(v___x_761_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
return v___x_762_;
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_776_; 
v_a_763_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_776_ == 0)
{
v___x_765_ = v___x_757_;
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_757_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_767_ = lean_io_error_to_string(v_a_763_);
v___x_768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
v___x_769_ = l_Lean_MessageData_ofFormat(v___x_768_);
lean_inc(v_ref_756_);
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 0);
lean_ctor_set(v___x_754_, 1, v___x_769_);
lean_ctor_set(v___x_754_, 0, v_ref_756_);
v___x_771_ = v___x_754_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_ref_756_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_769_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_771_);
v___x_773_ = v___x_765_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
else
{
lean_del_object(v___x_754_);
lean_dec(v_id_750_);
goto v___jp_744_;
}
}
}
else
{
lean_dec(v_id_750_);
lean_dec_ref_known(v_ex_736_, 2);
goto v___jp_744_;
}
}
v___jp_744_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_box(0);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1___boxed(lean_object* v_ex_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(v_ex_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant(lean_object* v_ctx_815_, lean_object* v_n_816_, lean_object* v_mv_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v_a_832_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v_invariantAlts_884_; lean_object* v_termCtx_885_; lean_object* v_levelNames_886_; lean_object* v___x_887_; 
v_invariantAlts_884_ = lean_ctor_get(v_ctx_815_, 5);
lean_inc_ref(v_invariantAlts_884_);
v_termCtx_885_ = lean_ctor_get(v_ctx_815_, 6);
lean_inc_ref(v_termCtx_885_);
v_levelNames_886_ = lean_ctor_get(v_ctx_815_, 7);
lean_inc(v_levelNames_886_);
lean_dec_ref(v_ctx_815_);
v___x_887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_884_, v_n_816_);
lean_dec_ref(v_invariantAlts_884_);
if (lean_obj_tag(v___x_887_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_957_; 
v_val_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_957_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_957_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_val_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_957_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__3));
lean_inc(v_val_888_);
v___x_927_ = l_Lean_Syntax_isOfKind(v_val_888_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__5));
lean_inc(v_val_888_);
v___x_929_ = l_Lean_Syntax_isOfKind(v_val_888_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_932_; 
lean_dec(v_val_888_);
lean_dec(v_levelNames_886_);
lean_dec_ref(v_termCtx_885_);
lean_dec(v_mv_817_);
v___x_930_ = lean_box(v___x_929_);
if (v_isShared_891_ == 0)
{
lean_ctor_set_tag(v___x_890_, 0);
lean_ctor_set(v___x_890_, 0, v___x_930_);
v___x_932_ = v___x_890_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = l_Lean_Syntax_getArg(v_val_888_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__7));
lean_inc(v___x_935_);
v___x_937_ = l_Lean_Syntax_isOfKind(v___x_935_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_940_; 
lean_dec(v___x_935_);
lean_dec(v_val_888_);
lean_dec(v_levelNames_886_);
lean_dec_ref(v_termCtx_885_);
lean_dec(v_mv_817_);
v___x_938_ = lean_box(v___x_937_);
if (v_isShared_891_ == 0)
{
lean_ctor_set_tag(v___x_890_, 0);
lean_ctor_set(v___x_890_, 0, v___x_938_);
v___x_940_ = v___x_890_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_rhs_944_; lean_object* v_names_945_; 
lean_del_object(v___x_890_);
v___x_942_ = l_Lean_Syntax_getArg(v___x_935_, v___x_934_);
lean_dec(v___x_935_);
v___x_943_ = lean_unsigned_to_nat(3u);
v_rhs_944_ = l_Lean_Syntax_getArg(v_val_888_, v___x_943_);
v_names_945_ = l_Lean_Syntax_getArgs(v___x_942_);
lean_dec(v___x_942_);
v_fst_893_ = v_names_945_;
v_snd_894_ = v_rhs_944_;
v___y_895_ = v_a_818_;
v___y_896_ = v_a_819_;
v___y_897_ = v_a_820_;
v___y_898_ = v_a_821_;
v___y_899_ = v_a_822_;
v___y_900_ = v_a_823_;
goto v___jp_892_;
}
}
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = l_Lean_Syntax_getArg(v_val_888_, v___x_946_);
v___x_948_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__9));
v___x_949_ = l_Lean_Syntax_isOfKind(v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_952_; 
lean_dec(v_val_888_);
lean_dec(v_levelNames_886_);
lean_dec_ref(v_termCtx_885_);
lean_dec(v_mv_817_);
v___x_950_ = lean_box(v___x_949_);
if (v_isShared_891_ == 0)
{
lean_ctor_set_tag(v___x_890_, 0);
lean_ctor_set(v___x_890_, 0, v___x_950_);
v___x_952_ = v___x_890_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v___x_954_; lean_object* v_rhs_955_; lean_object* v___x_956_; 
lean_del_object(v___x_890_);
v___x_954_ = lean_unsigned_to_nat(1u);
v_rhs_955_ = l_Lean_Syntax_getArg(v_val_888_, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10));
v_fst_893_ = v___x_956_;
v_snd_894_ = v_rhs_955_;
v___y_895_ = v_a_818_;
v___y_896_ = v_a_819_;
v___y_897_ = v_a_820_;
v___y_898_ = v_a_821_;
v___y_899_ = v_a_822_;
v___y_900_ = v_a_823_;
goto v___jp_892_;
}
}
v___jp_892_:
{
lean_object* v___x_901_; uint8_t v_transparency_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v_elabRhs_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; uint8_t v___x_910_; 
v___x_901_ = l_Lean_Meta_Context_config(v___y_897_);
v_transparency_902_ = lean_ctor_get_uint8(v___x_901_, 9);
lean_dec_ref(v___x_901_);
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = l_Lean_Syntax_getArg(v_val_888_, v___x_903_);
lean_dec(v_val_888_);
lean_inc(v_mv_817_);
v_elabRhs_905_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__1___boxed), 11, 4);
lean_closure_set(v_elabRhs_905_, 0, v___x_904_);
lean_closure_set(v_elabRhs_905_, 1, v_mv_817_);
lean_closure_set(v_elabRhs_905_, 2, v_fst_893_);
lean_closure_set(v_elabRhs_905_, 3, v_snd_894_);
v___x_906_ = lean_box(1);
v___x_907_ = lean_box(0);
v___x_908_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_908_, 0, v_levelNames_886_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
lean_ctor_set(v___x_908_, 2, v___x_907_);
lean_ctor_set(v___x_908_, 3, v___x_907_);
lean_ctor_set(v___x_908_, 4, v___x_907_);
lean_ctor_set(v___x_908_, 5, v___x_906_);
lean_ctor_set(v___x_908_, 6, v___x_907_);
lean_ctor_set(v___x_908_, 7, v___x_906_);
v___x_909_ = 1;
v___x_910_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_902_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v_keyedConfig_911_; uint8_t v_trackZetaDelta_912_; lean_object* v_zetaDeltaSet_913_; lean_object* v_lctx_914_; lean_object* v_localInstances_915_; lean_object* v_defEqCtx_x3f_916_; lean_object* v_synthPendingDepth_917_; lean_object* v_customCanUnfoldPredicate_x3f_918_; uint8_t v_univApprox_919_; uint8_t v_inTypeClassResolution_920_; uint8_t v_cacheInferType_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_keyedConfig_911_ = lean_ctor_get(v___y_897_, 0);
v_trackZetaDelta_912_ = lean_ctor_get_uint8(v___y_897_, sizeof(void*)*7);
v_zetaDeltaSet_913_ = lean_ctor_get(v___y_897_, 1);
v_lctx_914_ = lean_ctor_get(v___y_897_, 2);
v_localInstances_915_ = lean_ctor_get(v___y_897_, 3);
v_defEqCtx_x3f_916_ = lean_ctor_get(v___y_897_, 4);
v_synthPendingDepth_917_ = lean_ctor_get(v___y_897_, 5);
v_customCanUnfoldPredicate_x3f_918_ = lean_ctor_get(v___y_897_, 6);
v_univApprox_919_ = lean_ctor_get_uint8(v___y_897_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_920_ = lean_ctor_get_uint8(v___y_897_, sizeof(void*)*7 + 2);
v_cacheInferType_921_ = lean_ctor_get_uint8(v___y_897_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_911_);
v___x_922_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_909_, v_keyedConfig_911_);
lean_inc(v_customCanUnfoldPredicate_x3f_918_);
lean_inc(v_synthPendingDepth_917_);
lean_inc(v_defEqCtx_x3f_916_);
lean_inc_ref(v_localInstances_915_);
lean_inc_ref(v_lctx_914_);
lean_inc(v_zetaDeltaSet_913_);
v___x_923_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_zetaDeltaSet_913_);
lean_ctor_set(v___x_923_, 2, v_lctx_914_);
lean_ctor_set(v___x_923_, 3, v_localInstances_915_);
lean_ctor_set(v___x_923_, 4, v_defEqCtx_x3f_916_);
lean_ctor_set(v___x_923_, 5, v_synthPendingDepth_917_);
lean_ctor_set(v___x_923_, 6, v_customCanUnfoldPredicate_x3f_918_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*7, v_trackZetaDelta_912_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*7 + 1, v_univApprox_919_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*7 + 2, v_inTypeClassResolution_920_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*7 + 3, v_cacheInferType_921_);
v___x_924_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__2(v_elabRhs_905_, v_termCtx_885_, v___x_908_, v___y_895_, v___y_896_, v___x_923_, v___y_898_, v___y_899_, v___y_900_);
lean_dec_ref_known(v___x_923_, 7);
v___y_856_ = v___y_898_;
v___y_857_ = v___y_895_;
v___y_858_ = v___y_897_;
v___y_859_ = v___y_899_;
v___y_860_ = v___y_896_;
v___y_861_ = v___y_900_;
v___y_862_ = v___x_924_;
goto v___jp_855_;
}
else
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Elab_Tactic_VCGen_elabInvariant___lam__2(v_elabRhs_905_, v_termCtx_885_, v___x_908_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
v___y_856_ = v___y_898_;
v___y_857_ = v___y_895_;
v___y_858_ = v___y_897_;
v___y_859_ = v___y_899_;
v___y_860_ = v___y_896_;
v___y_861_ = v___y_900_;
v___y_862_ = v___x_925_;
goto v___jp_855_;
}
}
}
}
else
{
uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v___x_887_);
lean_dec(v_levelNames_886_);
lean_dec_ref(v_termCtx_885_);
lean_dec(v_mv_817_);
v___x_958_ = 0;
v___x_959_ = lean_box(v___x_958_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
v___jp_825_:
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_Exception_isInterrupt(v_a_832_);
if (v___x_833_ == 0)
{
uint8_t v___x_834_; 
lean_inc_ref(v_a_832_);
v___x_834_ = l_Lean_Exception_isRuntime(v_a_832_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1(v_a_832_, v___y_827_, v___y_830_, v___y_828_, v___y_826_, v___y_829_, v___y_831_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_843_; 
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v___x_835_, 0);
lean_dec(v_unused_844_);
v___x_837_ = v___x_835_;
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
else
{
lean_dec(v___x_835_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_843_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = lean_box(v___x_834_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_839_);
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_835_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_835_);
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
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v_a_832_);
return v___x_853_;
}
}
else
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v_a_832_);
return v___x_854_;
}
}
v___jp_855_:
{
if (lean_obj_tag(v___y_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_866_; 
v_a_863_ = lean_ctor_get(v___y_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___y_862_, 1);
v___x_864_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__2___redArg(v_a_863_, v___y_856_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
v___x_866_ = l_Lean_Meta_Sym_unfoldReducible(v_a_865_, v___y_858_, v___y_856_, v___y_859_, v___y_861_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = l_Lean_Meta_Sym_shareCommon(v_a_867_, v___y_857_, v___y_860_, v___y_858_, v___y_856_, v___y_859_, v___y_861_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_879_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mv_817_, v_a_869_, v___y_856_);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v___x_870_, 0);
lean_dec(v_unused_880_);
v___x_872_ = v___x_870_;
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
else
{
lean_dec(v___x_870_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = 1;
v___x_875_ = lean_box(v___x_874_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_881_; 
lean_dec(v_mv_817_);
v_a_881_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_868_, 1);
v___y_826_ = v___y_856_;
v___y_827_ = v___y_857_;
v___y_828_ = v___y_858_;
v___y_829_ = v___y_859_;
v___y_830_ = v___y_860_;
v___y_831_ = v___y_861_;
v_a_832_ = v_a_881_;
goto v___jp_825_;
}
}
else
{
lean_object* v_a_882_; 
lean_dec(v_mv_817_);
v_a_882_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_866_, 1);
v___y_826_ = v___y_856_;
v___y_827_ = v___y_857_;
v___y_828_ = v___y_858_;
v___y_829_ = v___y_859_;
v___y_830_ = v___y_860_;
v___y_831_ = v___y_861_;
v_a_832_ = v_a_882_;
goto v___jp_825_;
}
}
else
{
lean_object* v_a_883_; 
lean_dec(v_mv_817_);
v_a_883_ = lean_ctor_get(v___y_862_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___y_862_, 1);
v___y_826_ = v___y_856_;
v___y_827_ = v___y_857_;
v___y_828_ = v___y_858_;
v___y_829_ = v___y_859_;
v___y_830_ = v___y_860_;
v___y_831_ = v___y_861_;
v_a_832_ = v_a_883_;
goto v___jp_825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_elabInvariant___boxed(lean_object* v_ctx_961_, lean_object* v_n_962_, lean_object* v_mv_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v_ctx_961_, v_n_962_, v_mv_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_n_962_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___redArg(v_m_973_, v_a_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_976_, lean_object* v_m_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0(v_00_u03b2_976_, v_m_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_m_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_980_, lean_object* v_val_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___redArg(v_mvarId_980_, v_val_981_, v___y_985_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_990_, lean_object* v_val_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3(v_mvarId_990_, v_val_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_1000_, lean_object* v_a_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1004_, lean_object* v_a_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_1004_, v_a_1005_, v_x_1006_);
lean_dec(v_x_1006_);
lean_dec(v_a_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6(lean_object* v_00_u03b2_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6___redArg(v_x_1009_, v_x_1010_, v_x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5(lean_object* v_ref_1013_, lean_object* v_msgData_1014_, uint8_t v_severity_1015_, uint8_t v_isSilent_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___redArg(v_ref_1013_, v_msgData_1014_, v_severity_1015_, v_isSilent_1016_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5___boxed(lean_object* v_ref_1025_, lean_object* v_msgData_1026_, lean_object* v_severity_1027_, lean_object* v_isSilent_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
uint8_t v_severity_boxed_1036_; uint8_t v_isSilent_boxed_1037_; lean_object* v_res_1038_; 
v_severity_boxed_1036_ = lean_unbox(v_severity_1027_);
v_isSilent_boxed_1037_ = lean_unbox(v_isSilent_1028_);
v_res_1038_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__1_spec__2_spec__5(v_ref_1025_, v_msgData_1026_, v_severity_boxed_1036_, v_isSilent_boxed_1037_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v_ref_1025_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_1039_, lean_object* v_x_1040_, size_t v_x_1041_, size_t v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___redArg(v_x_1040_, v_x_1041_, v_x_1042_, v_x_1043_, v_x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
size_t v_x_22117__boxed_1052_; size_t v_x_22118__boxed_1053_; lean_object* v_res_1054_; 
v_x_22117__boxed_1052_ = lean_unbox_usize(v_x_1048_);
lean_dec(v_x_1048_);
v_x_22118__boxed_1053_ = lean_unbox_usize(v_x_1049_);
lean_dec(v_x_1049_);
v_res_1054_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10(v_00_u03b2_1046_, v_x_1047_, v_x_22117__boxed_1052_, v_x_22118__boxed_1053_, v_x_1050_, v_x_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13(lean_object* v_00_u03b2_1055_, lean_object* v_n_1056_, lean_object* v_k_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13___redArg(v_n_1056_, v_k_1057_, v_v_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14(lean_object* v_00_u03b2_1060_, size_t v_depth_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_entries_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___redArg(v_depth_1061_, v_keys_1062_, v_vals_1063_, v_i_1065_, v_entries_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_depth_1069_, lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_heq_1072_, lean_object* v_i_1073_, lean_object* v_entries_1074_){
_start:
{
size_t v_depth_boxed_1075_; lean_object* v_res_1076_; 
v_depth_boxed_1075_ = lean_unbox_usize(v_depth_1069_);
lean_dec(v_depth_1069_);
v_res_1076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__14(v_00_u03b2_1068_, v_depth_boxed_1075_, v_keys_1070_, v_vals_1071_, v_heq_1072_, v_i_1073_, v_entries_1074_);
lean_dec_ref(v_vals_1071_);
lean_dec_ref(v_keys_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13_spec__14(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_VCGen_elabInvariant_spec__3_spec__6_spec__10_spec__13_spec__14___redArg(v_x_1078_, v_x_1079_, v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v___x_1083_, lean_object* v_as_x27_1084_, lean_object* v_b_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
if (lean_obj_tag(v_as_x27_1084_) == 0)
{
lean_object* v___x_1095_; 
lean_dec_ref(v___x_1083_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_b_1085_);
return v___x_1095_;
}
else
{
lean_object* v_head_1096_; lean_object* v_tail_1097_; lean_object* v___x_1098_; 
v_head_1096_ = lean_ctor_get(v_as_x27_1084_, 0);
v_tail_1097_ = lean_ctor_get(v_as_x27_1084_, 1);
lean_inc(v_head_1096_);
v___x_1098_ = l_Lean_MVarId_getType(v_head_1096_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; uint8_t v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
lean_inc_ref(v___x_1083_);
v___x_1100_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_1083_, v_a_1099_);
lean_dec(v_a_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_inc(v_head_1096_);
v___x_1101_ = lean_array_push(v_b_1085_, v_head_1096_);
v_as_x27_1084_ = v_tail_1097_;
v_b_1085_ = v___x_1101_;
goto _start;
}
else
{
lean_object* v___x_1103_; lean_object* v_invariants_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v_specBackwardRuleCache_1109_; lean_object* v_wpSplitBackwardRuleCache_1110_; lean_object* v_assertionSplitBackwardRuleCache_1111_; lean_object* v_latticeBackwardRuleCache_1112_; lean_object* v_frameBackwardRuleCache_1113_; lean_object* v_rintroBackwardRuleCache_1114_; lean_object* v_frameDB_1115_; lean_object* v_invariants_1116_; lean_object* v_vcs_1117_; lean_object* v_simpState_1118_; lean_object* v_fuel_1119_; lean_object* v_pendingJoinPoints_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1152_; 
v___x_1103_ = lean_st_ref_get(v___y_1087_);
v_invariants_1104_ = lean_ctor_get(v___x_1103_, 7);
lean_inc_ref(v_invariants_1104_);
lean_dec(v___x_1103_);
v___x_1105_ = lean_array_get_size(v_invariants_1104_);
lean_dec_ref(v_invariants_1104_);
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_nat_add(v___x_1105_, v___x_1106_);
v___x_1108_ = lean_st_ref_take(v___y_1087_);
v_specBackwardRuleCache_1109_ = lean_ctor_get(v___x_1108_, 0);
v_wpSplitBackwardRuleCache_1110_ = lean_ctor_get(v___x_1108_, 1);
v_assertionSplitBackwardRuleCache_1111_ = lean_ctor_get(v___x_1108_, 2);
v_latticeBackwardRuleCache_1112_ = lean_ctor_get(v___x_1108_, 3);
v_frameBackwardRuleCache_1113_ = lean_ctor_get(v___x_1108_, 4);
v_rintroBackwardRuleCache_1114_ = lean_ctor_get(v___x_1108_, 5);
v_frameDB_1115_ = lean_ctor_get(v___x_1108_, 6);
v_invariants_1116_ = lean_ctor_get(v___x_1108_, 7);
v_vcs_1117_ = lean_ctor_get(v___x_1108_, 8);
v_simpState_1118_ = lean_ctor_get(v___x_1108_, 9);
v_fuel_1119_ = lean_ctor_get(v___x_1108_, 10);
v_pendingJoinPoints_1120_ = lean_ctor_get(v___x_1108_, 11);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1122_ = v___x_1108_;
v_isShared_1123_ = v_isSharedCheck_1152_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_pendingJoinPoints_1120_);
lean_inc(v_fuel_1119_);
lean_inc(v_simpState_1118_);
lean_inc(v_vcs_1117_);
lean_inc(v_invariants_1116_);
lean_inc(v_frameDB_1115_);
lean_inc(v_rintroBackwardRuleCache_1114_);
lean_inc(v_frameBackwardRuleCache_1113_);
lean_inc(v_latticeBackwardRuleCache_1112_);
lean_inc(v_assertionSplitBackwardRuleCache_1111_);
lean_inc(v_wpSplitBackwardRuleCache_1110_);
lean_inc(v_specBackwardRuleCache_1109_);
lean_dec(v___x_1108_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1152_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_inc(v_head_1096_);
v___x_1124_ = lean_array_push(v_invariants_1116_, v_head_1096_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 7, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_specBackwardRuleCache_1109_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_wpSplitBackwardRuleCache_1110_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_assertionSplitBackwardRuleCache_1111_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_latticeBackwardRuleCache_1112_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_frameBackwardRuleCache_1113_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v_rintroBackwardRuleCache_1114_);
lean_ctor_set(v_reuseFailAlloc_1151_, 6, v_frameDB_1115_);
lean_ctor_set(v_reuseFailAlloc_1151_, 7, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1151_, 8, v_vcs_1117_);
lean_ctor_set(v_reuseFailAlloc_1151_, 9, v_simpState_1118_);
lean_ctor_set(v_reuseFailAlloc_1151_, 10, v_fuel_1119_);
lean_ctor_set(v_reuseFailAlloc_1151_, 11, v_pendingJoinPoints_1120_);
v___x_1126_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_st_ref_put(v___y_1087_, v___x_1126_);
lean_inc(v_head_1096_);
lean_inc_ref(v___y_1086_);
v___x_1128_ = l_Lean_Elab_Tactic_VCGen_elabInvariant(v___y_1086_, v___x_1107_, v_head_1096_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___x_1107_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; uint8_t v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = lean_unbox(v_a_1129_);
lean_dec(v_a_1129_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = 2;
lean_inc(v_head_1096_);
v___x_1132_ = l_Lean_MVarId_setKind___redArg(v_head_1096_, v___x_1131_, v___y_1091_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_dec_ref_known(v___x_1132_, 1);
v_as_x27_1084_ = v_tail_1097_;
goto _start;
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_b_1085_);
lean_dec_ref(v___x_1083_);
v_a_1134_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
v_as_x27_1084_ = v_tail_1097_;
goto _start;
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref(v_b_1085_);
lean_dec_ref(v___x_1083_);
v_a_1143_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1128_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1128_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_b_1085_);
lean_dec_ref(v___x_1083_);
v_a_1153_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1098_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1098_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg___boxed(lean_object* v___x_1161_, lean_object* v_as_x27_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v___x_1161_, v_as_x27_1162_, v_b_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v_as_x27_1162_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_env_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1189_ = lean_st_ref_get(v_a_1187_);
v_env_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_ref(v_env_1190_);
lean_dec(v___x_1189_);
v___x_1191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_1192_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v_env_1190_, v_subgoals_1176_, v___x_1191_, v_a_1177_, v_a_1178_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_subgoals_1193_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(lean_object* v___x_1207_, lean_object* v_as_1208_, lean_object* v_as_x27_1209_, lean_object* v_b_1210_, lean_object* v_a_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___redArg(v___x_1207_, v_as_x27_1209_, v_b_1210_, v___y_1212_, v___y_1213_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0___boxed(lean_object** _args){
lean_object* v___x_1225_ = _args[0];
lean_object* v_as_1226_ = _args[1];
lean_object* v_as_x27_1227_ = _args[2];
lean_object* v_b_1228_ = _args[3];
lean_object* v_a_1229_ = _args[4];
lean_object* v___y_1230_ = _args[5];
lean_object* v___y_1231_ = _args[6];
lean_object* v___y_1232_ = _args[7];
lean_object* v___y_1233_ = _args[8];
lean_object* v___y_1234_ = _args[9];
lean_object* v___y_1235_ = _args[10];
lean_object* v___y_1236_ = _args[11];
lean_object* v___y_1237_ = _args[12];
lean_object* v___y_1238_ = _args[13];
lean_object* v___y_1239_ = _args[14];
lean_object* v___y_1240_ = _args[15];
lean_object* v___y_1241_ = _args[16];
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals_spec__0(v___x_1225_, v_as_1226_, v_as_x27_1227_, v_b_1228_, v_a_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v_as_x27_1227_);
lean_dec(v_as_1226_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0(lean_object* v_x_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
v___x_1256_ = lean_apply_12(v_x_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, lean_box(0));
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0___boxed(lean_object* v_x_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0(v_x_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(lean_object* v_mvarId_1271_, lean_object* v_x_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___f_1285_; lean_object* v___x_1286_; 
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1285_, 0, v_x_1272_);
lean_closure_set(v___f_1285_, 1, v___y_1273_);
lean_closure_set(v___f_1285_, 2, v___y_1274_);
lean_closure_set(v___f_1285_, 3, v___y_1275_);
lean_closure_set(v___f_1285_, 4, v___y_1276_);
lean_closure_set(v___f_1285_, 5, v___y_1277_);
lean_closure_set(v___f_1285_, 6, v___y_1278_);
lean_closure_set(v___f_1285_, 7, v___y_1279_);
v___x_1286_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1271_, v___f_1285_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1286_) == 0)
{
return v___x_1286_;
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg___boxed(lean_object* v_mvarId_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(v_mvarId_1295_, v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0(lean_object* v_00_u03b1_1310_, lean_object* v_mvarId_1311_, lean_object* v_x_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(v_mvarId_1311_, v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___boxed(lean_object* v_00_u03b1_1326_, lean_object* v_mvarId_1327_, lean_object* v_x_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0(v_00_u03b1_1326_, v_mvarId_1327_, v_x_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0(lean_object* v_goal_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_simpMethods_1355_; 
v_simpMethods_1355_ = lean_ctor_get(v___y_1343_, 3);
if (lean_obj_tag(v_simpMethods_1355_) == 1)
{
lean_object* v_val_1356_; lean_object* v___x_1357_; 
v_val_1356_ = lean_ctor_get(v_simpMethods_1355_, 0);
lean_inc(v_goal_1342_);
v___x_1357_ = l_Lean_MVarId_getType(v_goal_1342_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1359_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_1359_, 0, v_a_1358_);
lean_inc(v_val_1356_);
v___x_1360_ = l_Lean_Elab_Tactic_VCGen_runSimp___redArg(v_val_1356_, v___x_1359_, v___y_1343_, v___y_1344_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1362_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_a_1361_, v_goal_1342_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1362_;
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_goal_1342_);
v_a_1363_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1360_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1360_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_goal_1342_);
v_a_1371_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1357_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1357_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec(v_goal_1342_);
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___boxed(lean_object* v_goal_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0(v_goal_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC(lean_object* v_goal_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___f_1408_; lean_object* v___x_1409_; 
lean_inc(v_goal_1395_);
v___f_1408_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___lam__0___boxed), 13, 1);
lean_closure_set(v___f_1408_, 0, v_goal_1395_);
v___x_1409_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC_spec__0___redArg(v_goal_1395_, v___f_1408_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC___boxed(lean_object* v_goal_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC(v_goal_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC(lean_object* v_goal_1424_, lean_object* v_reason_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_goal_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v_goal_1533_; lean_object* v_toGoalState_1534_; lean_object* v_mvarId_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v_toGoalState_1567_; lean_object* v_mvarId_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1620_; 
v_toGoalState_1567_ = lean_ctor_get(v_goal_1424_, 0);
v_mvarId_1568_ = lean_ctor_get(v_goal_1424_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_goal_1424_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1570_ = v_goal_1424_;
v_isShared_1571_ = v_isSharedCheck_1620_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_mvarId_1568_);
lean_inc(v_toGoalState_1567_);
lean_dec(v_goal_1424_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1620_;
goto v_resetjp_1569_;
}
v___jp_1438_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v_goal_1439_, v___y_1440_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1523_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1523_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_a_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1523_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v_toGoalState_1456_; uint8_t v_inconsistent_1457_; 
v_toGoalState_1456_ = lean_ctor_get(v_a_1452_, 0);
lean_inc_ref(v_toGoalState_1456_);
v_inconsistent_1457_ = lean_ctor_get_uint8(v_toGoalState_1456_, sizeof(void*)*21 + 8);
if (v_inconsistent_1457_ == 0)
{
lean_object* v_mvarId_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1517_; 
lean_del_object(v___x_1454_);
v_mvarId_1458_ = lean_ctor_get(v_a_1452_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_a_1452_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_a_1452_, 0);
lean_dec(v_unused_1518_);
v___x_1460_ = v_a_1452_;
v_isShared_1461_ = v_isSharedCheck_1517_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_mvarId_1458_);
lean_dec(v_a_1452_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1517_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Elab_Tactic_VCGen_cleanupVC(v_mvarId_1458_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1508_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1508_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1508_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
if (lean_obj_tag(v_a_1463_) == 1)
{
lean_object* v_val_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; 
lean_del_object(v___x_1465_);
v_val_1467_ = lean_ctor_get(v_a_1463_, 0);
lean_inc_n(v_val_1467_, 2);
lean_dec_ref_known(v_a_1463_, 1);
v___x_1468_ = 2;
v___x_1469_ = l_Lean_MVarId_setKind___redArg(v_val_1467_, v___x_1468_, v___y_1448_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v___x_1469_, 0);
lean_dec(v_unused_1503_);
v___x_1471_ = v___x_1469_;
v_isShared_1472_ = v_isSharedCheck_1502_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v___x_1469_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1502_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v_specBackwardRuleCache_1474_; lean_object* v_wpSplitBackwardRuleCache_1475_; lean_object* v_assertionSplitBackwardRuleCache_1476_; lean_object* v_latticeBackwardRuleCache_1477_; lean_object* v_frameBackwardRuleCache_1478_; lean_object* v_rintroBackwardRuleCache_1479_; lean_object* v_frameDB_1480_; lean_object* v_invariants_1481_; lean_object* v_vcs_1482_; lean_object* v_simpState_1483_; lean_object* v_fuel_1484_; lean_object* v_pendingJoinPoints_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1501_; 
v___x_1473_ = lean_st_ref_take(v___y_1441_);
v_specBackwardRuleCache_1474_ = lean_ctor_get(v___x_1473_, 0);
v_wpSplitBackwardRuleCache_1475_ = lean_ctor_get(v___x_1473_, 1);
v_assertionSplitBackwardRuleCache_1476_ = lean_ctor_get(v___x_1473_, 2);
v_latticeBackwardRuleCache_1477_ = lean_ctor_get(v___x_1473_, 3);
v_frameBackwardRuleCache_1478_ = lean_ctor_get(v___x_1473_, 4);
v_rintroBackwardRuleCache_1479_ = lean_ctor_get(v___x_1473_, 5);
v_frameDB_1480_ = lean_ctor_get(v___x_1473_, 6);
v_invariants_1481_ = lean_ctor_get(v___x_1473_, 7);
v_vcs_1482_ = lean_ctor_get(v___x_1473_, 8);
v_simpState_1483_ = lean_ctor_get(v___x_1473_, 9);
v_fuel_1484_ = lean_ctor_get(v___x_1473_, 10);
v_pendingJoinPoints_1485_ = lean_ctor_get(v___x_1473_, 11);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1487_ = v___x_1473_;
v_isShared_1488_ = v_isSharedCheck_1501_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_pendingJoinPoints_1485_);
lean_inc(v_fuel_1484_);
lean_inc(v_simpState_1483_);
lean_inc(v_vcs_1482_);
lean_inc(v_invariants_1481_);
lean_inc(v_frameDB_1480_);
lean_inc(v_rintroBackwardRuleCache_1479_);
lean_inc(v_frameBackwardRuleCache_1478_);
lean_inc(v_latticeBackwardRuleCache_1477_);
lean_inc(v_assertionSplitBackwardRuleCache_1476_);
lean_inc(v_wpSplitBackwardRuleCache_1475_);
lean_inc(v_specBackwardRuleCache_1474_);
lean_dec(v___x_1473_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1501_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 1, v_val_1467_);
v___x_1491_ = v___x_1460_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_toGoalState_1456_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_val_1467_);
v___x_1491_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_array_push(v_vcs_1482_, v___x_1491_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 8, v___x_1492_);
v___x_1494_ = v___x_1487_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_specBackwardRuleCache_1474_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_wpSplitBackwardRuleCache_1475_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_assertionSplitBackwardRuleCache_1476_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_latticeBackwardRuleCache_1477_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_frameBackwardRuleCache_1478_);
lean_ctor_set(v_reuseFailAlloc_1499_, 5, v_rintroBackwardRuleCache_1479_);
lean_ctor_set(v_reuseFailAlloc_1499_, 6, v_frameDB_1480_);
lean_ctor_set(v_reuseFailAlloc_1499_, 7, v_invariants_1481_);
lean_ctor_set(v_reuseFailAlloc_1499_, 8, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1499_, 9, v_simpState_1483_);
lean_ctor_set(v_reuseFailAlloc_1499_, 10, v_fuel_1484_);
lean_ctor_set(v_reuseFailAlloc_1499_, 11, v_pendingJoinPoints_1485_);
v___x_1494_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_st_ref_put(v___y_1441_, v___x_1494_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1489_);
v___x_1497_ = v___x_1471_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1489_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1467_);
lean_del_object(v___x_1460_);
lean_dec_ref(v_toGoalState_1456_);
return v___x_1469_;
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
lean_dec(v_a_1463_);
lean_del_object(v___x_1460_);
lean_dec_ref(v_toGoalState_1456_);
v___x_1504_ = lean_box(0);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1504_);
v___x_1506_ = v___x_1465_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_del_object(v___x_1460_);
lean_dec_ref(v_toGoalState_1456_);
v_a_1509_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1462_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1462_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
lean_dec_ref(v_toGoalState_1456_);
lean_dec(v_a_1452_);
v___x_1519_ = lean_box(0);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1519_);
v___x_1521_ = v___x_1454_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_a_1524_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1451_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1451_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
v___jp_1532_:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_simpVC(v_mvarId_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1558_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1558_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
switch(lean_obj_tag(v_a_1548_))
{
case 0:
{
lean_del_object(v___x_1550_);
lean_dec_ref(v_toGoalState_1534_);
v_goal_1439_ = v_goal_1533_;
v___y_1440_ = v___y_1536_;
v___y_1441_ = v___y_1537_;
v___y_1442_ = v___y_1538_;
v___y_1443_ = v___y_1539_;
v___y_1444_ = v___y_1540_;
v___y_1445_ = v___y_1541_;
v___y_1446_ = v___y_1542_;
v___y_1447_ = v___y_1543_;
v___y_1448_ = v___y_1544_;
v___y_1449_ = v___y_1545_;
v___y_1450_ = v___y_1546_;
goto v___jp_1438_;
}
case 1:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec_ref(v_toGoalState_1534_);
lean_dec_ref(v_goal_1533_);
v___x_1552_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1552_);
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
default: 
{
lean_object* v_mvarId_1556_; lean_object* v___x_1557_; 
lean_del_object(v___x_1550_);
lean_dec_ref(v_goal_1533_);
v_mvarId_1556_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_mvarId_1556_);
lean_dec_ref_known(v_a_1548_, 1);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_toGoalState_1534_);
lean_ctor_set(v___x_1557_, 1, v_mvarId_1556_);
v_goal_1439_ = v___x_1557_;
v___y_1440_ = v___y_1536_;
v___y_1441_ = v___y_1537_;
v___y_1442_ = v___y_1538_;
v___y_1443_ = v___y_1539_;
v___y_1444_ = v___y_1540_;
v___y_1445_ = v___y_1541_;
v___y_1446_ = v___y_1542_;
v___y_1447_ = v___y_1543_;
v___y_1448_ = v___y_1544_;
v___y_1449_ = v___y_1545_;
v___y_1450_ = v___y_1546_;
goto v___jp_1438_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v_toGoalState_1534_);
lean_dec_ref(v_goal_1533_);
v_a_1559_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1547_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1547_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Elab_Tactic_VCGen_elimTopPre___redArg(v_mvarId_1568_, v_a_1426_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_n(v_a_1573_, 2);
lean_dec_ref_known(v___x_1572_, 1);
lean_inc_ref(v_toGoalState_1567_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v_a_1573_);
v___x_1575_ = v___x_1570_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_toGoalState_1567_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1573_);
v___x_1575_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
switch(lean_obj_tag(v_reason_1425_))
{
case 2:
{
goto v___jp_1576_;
}
case 3:
{
goto v___jp_1576_;
}
default: 
{
lean_dec(v_a_1573_);
lean_dec_ref(v_toGoalState_1567_);
v_goal_1439_ = v___x_1575_;
v___y_1440_ = v_a_1426_;
v___y_1441_ = v_a_1427_;
v___y_1442_ = v_a_1428_;
v___y_1443_ = v_a_1429_;
v___y_1444_ = v_a_1430_;
v___y_1445_ = v_a_1431_;
v___y_1446_ = v_a_1432_;
v___y_1447_ = v_a_1433_;
v___y_1448_ = v_a_1434_;
v___y_1449_ = v_a_1435_;
v___y_1450_ = v_a_1436_;
goto v___jp_1438_;
}
}
v___jp_1576_:
{
lean_object* v___x_1577_; 
lean_inc(v_a_1573_);
v___x_1577_ = l_Lean_MVarId_getType(v_a_1573_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_n(v_a_1578_, 2);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_1578_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; size_t v___x_1581_; size_t v___x_1582_; uint8_t v___x_1583_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = lean_ptr_addr(v_a_1578_);
lean_dec(v_a_1578_);
v___x_1582_ = lean_ptr_addr(v_a_1580_);
v___x_1583_ = lean_usize_dec_eq(v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref(v___x_1575_);
v___x_1584_ = l_Lean_MVarId_replaceTargetDefEqFast(v_a_1573_, v_a_1580_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_n(v_a_1585_, 2);
lean_dec_ref_known(v___x_1584_, 1);
lean_inc_ref(v_toGoalState_1567_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_toGoalState_1567_);
lean_ctor_set(v___x_1586_, 1, v_a_1585_);
v_goal_1533_ = v___x_1586_;
v_toGoalState_1534_ = v_toGoalState_1567_;
v_mvarId_1535_ = v_a_1585_;
v___y_1536_ = v_a_1426_;
v___y_1537_ = v_a_1427_;
v___y_1538_ = v_a_1428_;
v___y_1539_ = v_a_1429_;
v___y_1540_ = v_a_1430_;
v___y_1541_ = v_a_1431_;
v___y_1542_ = v_a_1432_;
v___y_1543_ = v_a_1433_;
v___y_1544_ = v_a_1434_;
v___y_1545_ = v_a_1435_;
v___y_1546_ = v_a_1436_;
goto v___jp_1532_;
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v_toGoalState_1567_);
v_a_1587_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1584_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1584_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_dec(v_a_1580_);
v_goal_1533_ = v___x_1575_;
v_toGoalState_1534_ = v_toGoalState_1567_;
v_mvarId_1535_ = v_a_1573_;
v___y_1536_ = v_a_1426_;
v___y_1537_ = v_a_1427_;
v___y_1538_ = v_a_1428_;
v___y_1539_ = v_a_1429_;
v___y_1540_ = v_a_1430_;
v___y_1541_ = v_a_1431_;
v___y_1542_ = v_a_1432_;
v___y_1543_ = v_a_1433_;
v___y_1544_ = v_a_1434_;
v___y_1545_ = v_a_1435_;
v___y_1546_ = v_a_1436_;
goto v___jp_1532_;
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1578_);
lean_dec_ref(v___x_1575_);
lean_dec(v_a_1573_);
lean_dec_ref(v_toGoalState_1567_);
v_a_1595_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1579_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1579_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v___x_1575_);
lean_dec(v_a_1573_);
lean_dec_ref(v_toGoalState_1567_);
v_a_1603_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1577_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1577_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_del_object(v___x_1570_);
lean_dec_ref(v_toGoalState_1567_);
v_a_1612_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1572_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1572_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_emitVC___boxed(lean_object* v_goal_1621_, lean_object* v_reason_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_goal_1621_, v_reason_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec_ref(v_a_1623_);
lean_dec(v_reason_1622_);
return v_res_1635_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_1636_, lean_object* v_i_1637_, lean_object* v_k_1638_){
_start:
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = lean_array_get_size(v_keys_1636_);
v___x_1640_ = lean_nat_dec_lt(v_i_1637_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_dec(v_i_1637_);
return v___x_1640_;
}
else
{
lean_object* v_k_x27_1641_; uint8_t v___x_1642_; 
v_k_x27_1641_ = lean_array_fget_borrowed(v_keys_1636_, v_i_1637_);
v___x_1642_ = l_Lean_instBEqMVarId_beq(v_k_1638_, v_k_x27_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(1u);
v___x_1644_ = lean_nat_add(v_i_1637_, v___x_1643_);
lean_dec(v_i_1637_);
v_i_1637_ = v___x_1644_;
goto _start;
}
else
{
lean_dec(v_i_1637_);
return v___x_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_1646_, lean_object* v_i_1647_, lean_object* v_k_1648_){
_start:
{
uint8_t v_res_1649_; lean_object* v_r_1650_; 
v_res_1649_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_1646_, v_i_1647_, v_k_1648_);
lean_dec(v_k_1648_);
lean_dec_ref(v_keys_1646_);
v_r_1650_ = lean_box(v_res_1649_);
return v_r_1650_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___redArg(lean_object* v_x_1651_, size_t v_x_1652_, lean_object* v_x_1653_){
_start:
{
if (lean_obj_tag(v_x_1651_) == 0)
{
lean_object* v_es_1654_; lean_object* v___x_1655_; size_t v___x_1656_; size_t v___x_1657_; lean_object* v_j_1658_; lean_object* v___x_1659_; 
v_es_1654_ = lean_ctor_get(v_x_1651_, 0);
v___x_1655_ = lean_box(2);
v___x_1656_ = ((size_t)31ULL);
v___x_1657_ = lean_usize_land(v_x_1652_, v___x_1656_);
v_j_1658_ = lean_usize_to_nat(v___x_1657_);
v___x_1659_ = lean_array_get_borrowed(v___x_1655_, v_es_1654_, v_j_1658_);
lean_dec(v_j_1658_);
switch(lean_obj_tag(v___x_1659_))
{
case 0:
{
lean_object* v_key_1660_; uint8_t v___x_1661_; 
v_key_1660_ = lean_ctor_get(v___x_1659_, 0);
v___x_1661_ = l_Lean_instBEqMVarId_beq(v_x_1653_, v_key_1660_);
return v___x_1661_;
}
case 1:
{
lean_object* v_node_1662_; size_t v___x_1663_; size_t v___x_1664_; 
v_node_1662_ = lean_ctor_get(v___x_1659_, 0);
v___x_1663_ = ((size_t)5ULL);
v___x_1664_ = lean_usize_shift_right(v_x_1652_, v___x_1663_);
v_x_1651_ = v_node_1662_;
v_x_1652_ = v___x_1664_;
goto _start;
}
default: 
{
uint8_t v___x_1666_; 
v___x_1666_ = 0;
return v___x_1666_;
}
}
}
else
{
lean_object* v_ks_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_ks_1667_ = lean_ctor_get(v_x_1651_, 0);
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_1667_, v___x_1668_, v_x_1653_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_){
_start:
{
size_t v_x_20905__boxed_1673_; uint8_t v_res_1674_; lean_object* v_r_1675_; 
v_x_20905__boxed_1673_ = lean_unbox_usize(v_x_1671_);
lean_dec(v_x_1671_);
v_res_1674_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___redArg(v_x_1670_, v_x_20905__boxed_1673_, v_x_1672_);
lean_dec(v_x_1672_);
lean_dec_ref(v_x_1670_);
v_r_1675_ = lean_box(v_res_1674_);
return v_r_1675_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___redArg(lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
uint64_t v___x_1678_; size_t v___x_1679_; uint8_t v___x_1680_; 
v___x_1678_ = l_Lean_instHashableMVarId_hash(v_x_1677_);
v___x_1679_ = lean_uint64_to_usize(v___x_1678_);
v___x_1680_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___redArg(v_x_1676_, v___x_1679_, v_x_1677_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___redArg___boxed(lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
uint8_t v_res_1683_; lean_object* v_r_1684_; 
v_res_1683_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___redArg(v_x_1681_, v_x_1682_);
lean_dec(v_x_1682_);
lean_dec_ref(v_x_1681_);
v_r_1684_ = lean_box(v_res_1683_);
return v_r_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(lean_object* v_mvarId_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v_mctx_1689_; lean_object* v_eAssignment_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1688_ = lean_st_ref_get(v___y_1686_);
v_mctx_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc_ref(v_mctx_1689_);
lean_dec(v___x_1688_);
v_eAssignment_1690_ = lean_ctor_get(v_mctx_1689_, 8);
lean_inc_ref(v_eAssignment_1690_);
lean_dec_ref(v_mctx_1689_);
v___x_1691_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___redArg(v_eAssignment_1690_, v_mvarId_1685_);
lean_dec_ref(v_eAssignment_1690_);
v___x_1692_ = lean_box(v___x_1691_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg___boxed(lean_object* v_mvarId_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec(v_mvarId_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(lean_object* v___x_1698_, lean_object* v_scope_1699_, size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_bs_1702_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1703_ == 0)
{
lean_dec_ref(v_scope_1699_);
lean_dec_ref(v___x_1698_);
return v_bs_1702_;
}
else
{
lean_object* v_v_1704_; lean_object* v___x_1705_; lean_object* v_bs_x27_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; size_t v___x_1709_; size_t v___x_1710_; lean_object* v___x_1711_; 
v_v_1704_ = lean_array_uget(v_bs_1702_, v_i_1701_);
v___x_1705_ = lean_unsigned_to_nat(0u);
v_bs_x27_1706_ = lean_array_uset(v_bs_1702_, v_i_1701_, v___x_1705_);
lean_inc_ref(v___x_1698_);
v___x_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1698_);
lean_ctor_set(v___x_1707_, 1, v_v_1704_);
lean_inc_ref(v_scope_1699_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v_scope_1699_);
v___x_1709_ = ((size_t)1ULL);
v___x_1710_ = lean_usize_add(v_i_1701_, v___x_1709_);
v___x_1711_ = lean_array_uset(v_bs_x27_1706_, v_i_1701_, v___x_1708_);
v_i_1701_ = v___x_1710_;
v_bs_1702_ = v___x_1711_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1___boxed(lean_object* v___x_1713_, lean_object* v_scope_1714_, lean_object* v_sz_1715_, lean_object* v_i_1716_, lean_object* v_bs_1717_){
_start:
{
size_t v_sz_boxed_1718_; size_t v_i_boxed_1719_; lean_object* v_res_1720_; 
v_sz_boxed_1718_ = lean_unbox_usize(v_sz_1715_);
lean_dec(v_sz_1715_);
v_i_boxed_1719_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v___x_1713_, v_scope_1714_, v_sz_boxed_1718_, v_i_boxed_1719_, v_bs_1717_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(lean_object* v_a_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1734_ = lean_array_get_size(v_a_1721_);
v___x_1735_ = lean_unsigned_to_nat(1u);
v___x_1736_ = lean_nat_sub(v___x_1734_, v___x_1735_);
v___x_1737_ = lean_nat_dec_lt(v___x_1736_, v___x_1734_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
lean_dec(v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v_a_1721_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v_goal_1740_; lean_object* v_scope_1741_; lean_object* v_toGoalState_1742_; lean_object* v_mvarId_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1826_; 
v___x_1739_ = lean_array_fget_borrowed(v_a_1721_, v___x_1736_);
lean_dec(v___x_1736_);
v_goal_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc_ref(v_goal_1740_);
v_scope_1741_ = lean_ctor_get(v___x_1739_, 1);
lean_inc_ref(v_scope_1741_);
v_toGoalState_1742_ = lean_ctor_get(v_goal_1740_, 0);
v_mvarId_1743_ = lean_ctor_get(v_goal_1740_, 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_goal_1740_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1745_ = v_goal_1740_;
v_isShared_1746_ = v_isSharedCheck_1826_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_mvarId_1743_);
lean_inc(v_toGoalState_1742_);
lean_dec(v_goal_1740_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1826_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_array_pop(v_a_1721_);
v___x_1748_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1743_, v___y_1730_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; uint8_t v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = lean_unbox(v_a_1749_);
lean_dec(v_a_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Elab_Tactic_VCGen_finalizeJoinPoint(v_mvarId_1743_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_a_1752_);
v___x_1754_ = v___x_1745_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_toGoalState_1742_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_a_1752_);
v___x_1754_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Elab_Tactic_VCGen_processHypotheses___redArg(v___x_1754_, v___y_1722_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v_toGoalState_1757_; uint8_t v_inconsistent_1758_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v_toGoalState_1757_ = lean_ctor_get(v_a_1756_, 0);
v_inconsistent_1758_ = lean_ctor_get_uint8(v_toGoalState_1757_, sizeof(void*)*21 + 8);
if (v_inconsistent_1758_ == 0)
{
lean_object* v_mvarId_1759_; lean_object* v___x_1760_; 
v_mvarId_1759_ = lean_ctor_get(v_a_1756_, 1);
lean_inc(v_mvarId_1759_);
v___x_1760_ = l_Lean_Elab_Tactic_VCGen_solve(v_scope_1741_, v_mvarId_1759_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
if (lean_obj_tag(v_a_1761_) == 0)
{
lean_object* v_scope_1762_; lean_object* v_subgoals_1763_; lean_object* v___x_1764_; 
lean_inc_ref(v_toGoalState_1757_);
lean_dec(v_a_1756_);
v_scope_1762_ = lean_ctor_get(v_a_1761_, 0);
lean_inc_ref(v_scope_1762_);
v_subgoals_1763_ = lean_ctor_get(v_a_1761_, 1);
lean_inc(v_subgoals_1763_);
lean_dec_ref_known(v_a_1761_, 2);
v___x_1764_ = l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals(v_subgoals_1763_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v_subgoals_1763_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; size_t v_sz_1767_; size_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l_Array_reverse___redArg(v_a_1765_);
v_sz_1767_ = lean_array_size(v___x_1766_);
v___x_1768_ = ((size_t)0ULL);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_work_spec__1(v_toGoalState_1757_, v_scope_1762_, v_sz_1767_, v___x_1768_, v___x_1766_);
v___x_1770_ = l_Array_append___redArg(v___x_1747_, v___x_1769_);
lean_dec_ref(v___x_1769_);
v_a_1721_ = v___x_1770_;
goto _start;
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v_scope_1762_);
lean_dec_ref(v_toGoalState_1757_);
lean_dec_ref(v___x_1747_);
v_a_1772_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1764_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1764_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_reason_1780_; lean_object* v___x_1781_; 
v_reason_1780_ = lean_ctor_get(v_a_1761_, 0);
lean_inc(v_reason_1780_);
lean_dec_ref_known(v_a_1761_, 1);
v___x_1781_ = l_Lean_Elab_Tactic_VCGen_emitVC(v_a_1756_, v_reason_1780_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v_reason_1780_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_dec_ref_known(v___x_1781_, 1);
v_a_1721_ = v___x_1747_;
goto _start;
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref(v___x_1747_);
v_a_1783_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1781_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_a_1756_);
lean_dec_ref(v___x_1747_);
v_a_1791_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1760_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1760_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_dec(v_a_1756_);
lean_dec_ref(v_scope_1741_);
v_a_1721_ = v___x_1747_;
goto _start;
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v___x_1747_);
lean_dec_ref(v_scope_1741_);
v_a_1800_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1755_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1755_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec_ref(v___x_1747_);
lean_del_object(v___x_1745_);
lean_dec_ref(v_toGoalState_1742_);
lean_dec_ref(v_scope_1741_);
v_a_1809_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1751_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1751_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_del_object(v___x_1745_);
lean_dec(v_mvarId_1743_);
lean_dec_ref(v_toGoalState_1742_);
lean_dec_ref(v_scope_1741_);
v_a_1721_ = v___x_1747_;
goto _start;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref(v___x_1747_);
lean_del_object(v___x_1745_);
lean_dec(v_mvarId_1743_);
lean_dec_ref(v_toGoalState_1742_);
lean_dec_ref(v_scope_1741_);
v_a_1818_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1748_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1748_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg___boxed(lean_object* v_a_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work(lean_object* v_scope_1841_, lean_object* v_goal_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_toGoalState_1855_; lean_object* v_mvarId_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1895_; 
v_toGoalState_1855_ = lean_ctor_get(v_goal_1842_, 0);
v_mvarId_1856_ = lean_ctor_get(v_goal_1842_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_goal_1842_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1858_ = v_goal_1842_;
v_isShared_1859_ = v_isSharedCheck_1895_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_mvarId_1856_);
lean_inc(v_toGoalState_1855_);
lean_dec(v_goal_1842_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1895_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_1856_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v_a_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_toGoalState_1855_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_a_1861_);
v___x_1863_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v_scope_1841_);
v___x_1865_ = lean_unsigned_to_nat(1u);
v___x_1866_ = lean_mk_empty_array_with_capacity(v___x_1865_);
v___x_1867_ = lean_array_push(v___x_1866_, v___x_1864_);
v___x_1868_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v___x_1867_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1876_; 
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; 
v_unused_1877_ = lean_ctor_get(v___x_1868_, 0);
lean_dec(v_unused_1877_);
v___x_1870_ = v___x_1868_;
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v___x_1868_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = lean_box(0);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1872_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
v_a_1878_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1868_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1868_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_del_object(v___x_1858_);
lean_dec_ref(v_toGoalState_1855_);
lean_dec_ref(v_scope_1841_);
v_a_1887_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1860_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1860_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_work___boxed(lean_object* v_scope_1896_, lean_object* v_goal_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_1896_, v_goal_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(lean_object* v_mvarId_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___redArg(v_mvarId_1911_, v___y_1920_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0___boxed(lean_object* v_mvarId_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0(v_mvarId_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v_mvarId_1925_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(lean_object* v_inst_1939_, lean_object* v_a_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___redArg(v_a_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2___boxed(lean_object* v_inst_1954_, lean_object* v_a_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_VCGen_work_spec__2(v_inst_1954_, v_a_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1968_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0(lean_object* v_00_u03b2_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
uint8_t v___x_1972_; 
v___x_1972_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___redArg(v_x_1970_, v_x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_){
_start:
{
uint8_t v_res_1976_; lean_object* v_r_1977_; 
v_res_1976_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0(v_00_u03b2_1973_, v_x_1974_, v_x_1975_);
lean_dec(v_x_1975_);
lean_dec_ref(v_x_1974_);
v_r_1977_ = lean_box(v_res_1976_);
return v_r_1977_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1978_, lean_object* v_x_1979_, size_t v_x_1980_, lean_object* v_x_1981_){
_start:
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___redArg(v_x_1979_, v_x_1980_, v_x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_){
_start:
{
size_t v_x_21370__boxed_1987_; uint8_t v_res_1988_; lean_object* v_r_1989_; 
v_x_21370__boxed_1987_ = lean_unbox_usize(v_x_1985_);
lean_dec(v_x_1985_);
v_res_1988_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1(v_00_u03b2_1983_, v_x_1984_, v_x_21370__boxed_1987_, v_x_1986_);
lean_dec(v_x_1986_);
lean_dec_ref(v_x_1984_);
v_r_1989_ = lean_box(v_res_1988_);
return v_r_1989_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1990_, lean_object* v_keys_1991_, lean_object* v_vals_1992_, lean_object* v_heq_1993_, lean_object* v_i_1994_, lean_object* v_k_1995_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_1991_, v_i_1994_, v_k_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1997_, lean_object* v_keys_1998_, lean_object* v_vals_1999_, lean_object* v_heq_2000_, lean_object* v_i_2001_, lean_object* v_k_2002_){
_start:
{
uint8_t v_res_2003_; lean_object* v_r_2004_; 
v_res_2003_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1997_, v_keys_1998_, v_vals_1999_, v_heq_2000_, v_i_2001_, v_k_2002_);
lean_dec(v_k_2002_);
lean_dec_ref(v_vals_1999_);
lean_dec_ref(v_keys_1998_);
v_r_2004_ = lean_box(v_res_2003_);
return v_r_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(lean_object* v_x_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_config_2016_; lean_object* v_sharedExprs_2017_; uint8_t v_verbose_2018_; uint8_t v_enforceUnfoldReducible_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_config_2016_ = lean_ctor_get(v___y_2009_, 1);
v_sharedExprs_2017_ = lean_ctor_get(v___y_2009_, 0);
v_verbose_2018_ = lean_ctor_get_uint8(v_config_2016_, 0);
v_enforceUnfoldReducible_2019_ = lean_ctor_get_uint8(v_config_2016_, 1);
v___x_2020_ = 0;
v___x_2021_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_2021_, 0, v_verbose_2018_);
lean_ctor_set_uint8(v___x_2021_, 1, v_enforceUnfoldReducible_2019_);
lean_ctor_set_uint8(v___x_2021_, 2, v___x_2020_);
lean_inc_ref(v_sharedExprs_2017_);
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_sharedExprs_2017_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2010_);
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2007_);
lean_inc(v___y_2006_);
v___x_2023_ = lean_apply_10(v_x_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___x_2022_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, lean_box(0));
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg___boxed(lean_object* v_x_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(lean_object* v_00_u03b1_2036_, lean_object* v_x_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v_x_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___boxed(lean_object* v_00_u03b1_2049_, lean_object* v_x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1(v_00_u03b1_2049_, v_x_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0(lean_object* v_initState_2062_, lean_object* v_scope_2063_, lean_object* v_goal_2064_, lean_object* v_ctx_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_st_mk_ref(v_initState_2062_);
v___x_2077_ = l_Lean_Elab_Tactic_VCGen_work(v_scope_2063_, v_goal_2064_, v_ctx_2065_, v___x_2076_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2087_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2087_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2087_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2082_ = lean_st_ref_get(v___x_2076_);
lean_dec(v___x_2076_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v_a_2078_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2083_);
v___x_2085_ = v___x_2080_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v___x_2076_);
v_a_2088_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2077_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2077_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed(lean_object* v_initState_2096_, lean_object* v_scope_2097_, lean_object* v_goal_2098_, lean_object* v_ctx_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Elab_Tactic_VCGen_run___lam__0(v_initState_2096_, v_scope_2097_, v_goal_2098_, v_ctx_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v_ctx_2099_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(lean_object* v_mvarId_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v_mctx_2115_; lean_object* v_eAssignment_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2114_ = lean_st_ref_get(v___y_2112_);
v_mctx_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc_ref(v_mctx_2115_);
lean_dec(v___x_2114_);
v_eAssignment_2116_ = lean_ctor_get(v_mctx_2115_, 8);
lean_inc_ref(v_eAssignment_2116_);
lean_dec_ref(v_mctx_2115_);
v___x_2117_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_work_spec__0_spec__0___redArg(v_eAssignment_2116_, v_mvarId_2111_);
lean_dec_ref(v_eAssignment_2116_);
v___x_2118_ = lean_box(v___x_2117_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec(v_mvarId_2120_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(lean_object* v_as_2124_, size_t v_i_2125_, size_t v_stop_2126_, lean_object* v_b_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_a_2139_; uint8_t v___x_2143_; 
v___x_2143_ = lean_usize_dec_eq(v_i_2125_, v_stop_2126_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v_mvarId_2145_; lean_object* v___x_2146_; 
v___x_2144_ = lean_array_uget_borrowed(v_as_2124_, v_i_2125_);
v_mvarId_2145_ = lean_ctor_get(v___x_2144_, 1);
v___x_2146_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_2145_, v___y_2134_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; uint8_t v___x_2148_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2148_ = lean_unbox(v_a_2147_);
lean_dec(v_a_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_inc(v___x_2144_);
v___x_2149_ = lean_array_push(v_b_2127_, v___x_2144_);
v_a_2139_ = v___x_2149_;
goto v___jp_2138_;
}
else
{
v_a_2139_ = v_b_2127_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v_b_2127_);
v_a_2150_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2146_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2146_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_b_2127_);
return v___x_2158_;
}
v___jp_2138_:
{
size_t v___x_2140_; size_t v___x_2141_; 
v___x_2140_ = ((size_t)1ULL);
v___x_2141_ = lean_usize_add(v_i_2125_, v___x_2140_);
v_i_2125_ = v___x_2141_;
v_b_2127_ = v_a_2139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5___boxed(lean_object* v_as_2159_, lean_object* v_i_2160_, lean_object* v_stop_2161_, lean_object* v_b_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
size_t v_i_boxed_2173_; size_t v_stop_boxed_2174_; lean_object* v_res_2175_; 
v_i_boxed_2173_ = lean_unbox_usize(v_i_2160_);
lean_dec(v_i_2160_);
v_stop_boxed_2174_ = lean_unbox_usize(v_stop_2161_);
lean_dec(v_stop_2161_);
v_res_2175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_as_2159_, v_i_boxed_2173_, v_stop_boxed_2174_, v_b_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v_as_2159_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(size_t v_sz_2177_, size_t v_i_2178_, lean_object* v_bs_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2178_, v_sz_2177_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_bs_2179_);
return v___x_2186_;
}
else
{
lean_object* v_v_2187_; lean_object* v_mvarId_2188_; lean_object* v___x_2189_; lean_object* v_bs_x27_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_v_2187_ = lean_array_uget_borrowed(v_bs_2179_, v_i_2178_);
v_mvarId_2188_ = lean_ctor_get(v_v_2187_, 1);
lean_inc_n(v_mvarId_2188_, 2);
v___x_2189_ = lean_unsigned_to_nat(0u);
v_bs_x27_2190_ = lean_array_uset(v_bs_2179_, v_i_2178_, v___x_2189_);
v___x_2191_ = lean_usize_to_nat(v_i_2178_);
v___x_2192_ = l_Lean_MVarId_getTag(v_mvarId_2188_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___closed__0));
v___x_2195_ = lean_unsigned_to_nat(1u);
v___x_2196_ = lean_nat_add(v___x_2191_, v___x_2195_);
lean_dec(v___x_2191_);
v___x_2197_ = l_Nat_reprFast(v___x_2196_);
v___x_2198_ = lean_string_append(v___x_2194_, v___x_2197_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = lean_box(0);
v___x_2200_ = l_Lean_Name_str___override(v___x_2199_, v___x_2198_);
v___x_2201_ = l_Lean_Name_eraseMacroScopes(v_a_2193_);
lean_dec(v_a_2193_);
v___x_2202_ = l_Lean_Name_append(v___x_2200_, v___x_2201_);
v___x_2203_ = l_Lean_MVarId_setTag___redArg(v_mvarId_2188_, v___x_2202_, v___y_2181_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; size_t v___x_2205_; size_t v___x_2206_; lean_object* v___x_2207_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = ((size_t)1ULL);
v___x_2206_ = lean_usize_add(v_i_2178_, v___x_2205_);
v___x_2207_ = lean_array_uset(v_bs_x27_2190_, v_i_2178_, v_a_2204_);
v_i_2178_ = v___x_2206_;
v_bs_2179_ = v___x_2207_;
goto _start;
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v_bs_x27_2190_);
v_a_2209_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2203_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2203_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v___x_2191_);
lean_dec_ref(v_bs_x27_2190_);
lean_dec(v_mvarId_2188_);
v_a_2217_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2192_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2192_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg___boxed(lean_object* v_sz_2225_, lean_object* v_i_2226_, lean_object* v_bs_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
size_t v_sz_boxed_2233_; size_t v_i_boxed_2234_; lean_object* v_res_2235_; 
v_sz_boxed_2233_ = lean_unbox_usize(v_sz_2225_);
lean_dec(v_sz_2225_);
v_i_boxed_2234_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_res_2235_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_boxed_2233_, v_i_boxed_2234_, v_bs_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(size_t v_sz_2237_, size_t v_i_2238_, lean_object* v_bs_2239_, lean_object* v___y_2240_){
_start:
{
uint8_t v___x_2242_; 
v___x_2242_ = lean_usize_dec_lt(v_i_2238_, v_sz_2237_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v_bs_2239_);
return v___x_2243_;
}
else
{
lean_object* v_v_2244_; lean_object* v___x_2245_; lean_object* v_bs_x27_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_v_2244_ = lean_array_uget(v_bs_2239_, v_i_2238_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v_bs_x27_2246_ = lean_array_uset(v_bs_2239_, v_i_2238_, v___x_2245_);
v___x_2247_ = lean_usize_to_nat(v_i_2238_);
v___x_2248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___closed__0));
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_add(v___x_2247_, v___x_2249_);
lean_dec(v___x_2247_);
v___x_2251_ = l_Nat_reprFast(v___x_2250_);
v___x_2252_ = lean_string_append(v___x_2248_, v___x_2251_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = lean_box(0);
v___x_2254_ = l_Lean_Name_str___override(v___x_2253_, v___x_2252_);
v___x_2255_ = l_Lean_MVarId_setTag___redArg(v_v_2244_, v___x_2254_, v___y_2240_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; size_t v___x_2257_; size_t v___x_2258_; lean_object* v___x_2259_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v___x_2257_ = ((size_t)1ULL);
v___x_2258_ = lean_usize_add(v_i_2238_, v___x_2257_);
v___x_2259_ = lean_array_uset(v_bs_x27_2246_, v_i_2238_, v_a_2256_);
v_i_2238_ = v___x_2258_;
v_bs_2239_ = v___x_2259_;
goto _start;
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v_bs_x27_2246_);
v_a_2261_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2255_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2255_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg___boxed(lean_object* v_sz_2269_, lean_object* v_i_2270_, lean_object* v_bs_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
size_t v_sz_boxed_2274_; size_t v_i_boxed_2275_; lean_object* v_res_2276_; 
v_sz_boxed_2274_ = lean_unbox_usize(v_sz_2269_);
lean_dec(v_sz_2269_);
v_i_boxed_2275_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_res_2276_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_boxed_2274_, v_i_boxed_2275_, v_bs_2271_, v___y_2272_);
lean_dec(v___y_2272_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(lean_object* v_as_2277_, size_t v_i_2278_, size_t v_stop_2279_, lean_object* v_b_2280_){
_start:
{
lean_object* v___y_2282_; uint8_t v___x_2286_; 
v___x_2286_ = lean_usize_dec_eq(v_i_2278_, v_stop_2279_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; uint8_t v_retired_2288_; 
v___x_2287_ = lean_array_uget_borrowed(v_as_2277_, v_i_2278_);
v_retired_2288_ = lean_ctor_get_uint8(v___x_2287_, sizeof(void*)*4);
if (v_retired_2288_ == 0)
{
lean_object* v_frameStx_2289_; lean_object* v___x_2290_; 
v_frameStx_2289_ = lean_ctor_get(v___x_2287_, 2);
lean_inc(v_frameStx_2289_);
v___x_2290_ = lean_array_push(v_b_2280_, v_frameStx_2289_);
v___y_2282_ = v___x_2290_;
goto v___jp_2281_;
}
else
{
v___y_2282_ = v_b_2280_;
goto v___jp_2281_;
}
}
else
{
return v_b_2280_;
}
v___jp_2281_:
{
size_t v___x_2283_; size_t v___x_2284_; 
v___x_2283_ = ((size_t)1ULL);
v___x_2284_ = lean_usize_add(v_i_2278_, v___x_2283_);
v_i_2278_ = v___x_2284_;
v_b_2280_ = v___y_2282_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2___boxed(lean_object* v_as_2291_, lean_object* v_i_2292_, lean_object* v_stop_2293_, lean_object* v_b_2294_){
_start:
{
size_t v_i_boxed_2295_; size_t v_stop_boxed_2296_; lean_object* v_res_2297_; 
v_i_boxed_2295_ = lean_unbox_usize(v_i_2292_);
lean_dec(v_i_2292_);
v_stop_boxed_2296_ = lean_unbox_usize(v_stop_2293_);
lean_dec(v_stop_2293_);
v_res_2297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2291_, v_i_boxed_2295_, v_stop_boxed_2296_, v_b_2294_);
lean_dec_ref(v_as_2291_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(lean_object* v_as_2298_, lean_object* v_start_2299_, lean_object* v_stop_2300_){
_start:
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_elabInvariant___closed__10));
v___x_2302_ = lean_nat_dec_lt(v_start_2299_, v_stop_2300_);
if (v___x_2302_ == 0)
{
return v___x_2301_;
}
else
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = lean_array_get_size(v_as_2298_);
v___x_2304_ = lean_nat_dec_le(v_stop_2300_, v___x_2303_);
if (v___x_2304_ == 0)
{
uint8_t v___x_2305_; 
v___x_2305_ = lean_nat_dec_lt(v_start_2299_, v___x_2303_);
if (v___x_2305_ == 0)
{
return v___x_2301_;
}
else
{
size_t v___x_2306_; size_t v___x_2307_; lean_object* v___x_2308_; 
v___x_2306_ = lean_usize_of_nat(v_start_2299_);
v___x_2307_ = lean_usize_of_nat(v___x_2303_);
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2298_, v___x_2306_, v___x_2307_, v___x_2301_);
return v___x_2308_;
}
}
else
{
size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_usize_of_nat(v_start_2299_);
v___x_2310_ = lean_usize_of_nat(v_stop_2300_);
v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2_spec__2(v_as_2298_, v___x_2309_, v___x_2310_, v___x_2301_);
return v___x_2311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2___boxed(lean_object* v_as_2312_, lean_object* v_start_2313_, lean_object* v_stop_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_as_2312_, v_start_2313_, v_stop_2314_);
lean_dec(v_stop_2314_);
lean_dec(v_start_2313_);
lean_dec_ref(v_as_2312_);
return v_res_2315_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_unsigned_to_nat(16u);
v___x_2318_ = lean_mk_array(v___x_2317_, v___x_2316_);
return v___x_2318_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__0, &l_Lean_Elab_Tactic_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__0);
v___x_2320_ = lean_unsigned_to_nat(0u);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2323_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__2, &l_Lean_Elab_Tactic_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__2);
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__3, &l_Lean_Elab_Tactic_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__3);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2325_);
lean_ctor_set(v___x_2327_, 2, v___x_2325_);
lean_ctor_set(v___x_2327_, 3, v___x_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run(lean_object* v_goal_2328_, lean_object* v_ctx_2329_, lean_object* v_scope_2330_, lean_object* v_stepLimit_x3f_2331_, lean_object* v_frameDB_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2343_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v_a_2347_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___y_2357_; 
v___x_2343_ = lean_unsigned_to_nat(0u);
v___x_2353_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__1, &l_Lean_Elab_Tactic_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__1);
v___x_2354_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_Driver_0__Lean_Elab_Tactic_VCGen_handleInvariantSubgoals___closed__0));
v___x_2355_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_run___closed__4, &l_Lean_Elab_Tactic_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_2331_) == 0)
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_box(1);
v___y_2357_ = v___x_2408_;
goto v___jp_2356_;
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_val_2409_ = lean_ctor_get(v_stepLimit_x3f_2331_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_stepLimit_x3f_2331_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v_stepLimit_x3f_2331_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_val_2409_);
lean_dec(v_stepLimit_x3f_2331_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
lean_ctor_set_tag(v___x_2411_, 0);
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_val_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
v___y_2357_ = v___x_2414_;
goto v___jp_2356_;
}
}
}
v___jp_2344_:
{
lean_object* v_entries_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_entries_2348_ = lean_ctor_get(v___y_2346_, 1);
lean_inc_ref(v_entries_2348_);
lean_dec_ref(v___y_2346_);
v___x_2349_ = lean_array_get_size(v_entries_2348_);
v___x_2350_ = l_Array_filterMapM___at___00Lean_Elab_Tactic_VCGen_run_spec__2(v_entries_2348_, v___x_2343_, v___x_2349_);
lean_dec_ref(v_entries_2348_);
v___x_2351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2351_, 0, v___y_2345_);
lean_ctor_set(v___x_2351_, 1, v_a_2347_);
lean_ctor_set(v___x_2351_, 2, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
v___jp_2356_:
{
lean_object* v_initState_2358_; lean_object* v___f_2359_; lean_object* v___x_2360_; 
v_initState_2358_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_initState_2358_, 0, v___x_2353_);
lean_ctor_set(v_initState_2358_, 1, v___x_2353_);
lean_ctor_set(v_initState_2358_, 2, v___x_2353_);
lean_ctor_set(v_initState_2358_, 3, v___x_2353_);
lean_ctor_set(v_initState_2358_, 4, v___x_2353_);
lean_ctor_set(v_initState_2358_, 5, v___x_2353_);
lean_ctor_set(v_initState_2358_, 6, v_frameDB_2332_);
lean_ctor_set(v_initState_2358_, 7, v___x_2354_);
lean_ctor_set(v_initState_2358_, 8, v___x_2354_);
lean_ctor_set(v_initState_2358_, 9, v___x_2355_);
lean_ctor_set(v_initState_2358_, 10, v___y_2357_);
lean_ctor_set(v_initState_2358_, 11, v___x_2353_);
v___f_2359_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_run___lam__0___boxed), 14, 4);
lean_closure_set(v___f_2359_, 0, v_initState_2358_);
lean_closure_set(v___f_2359_, 1, v_scope_2330_);
lean_closure_set(v___f_2359_, 2, v_goal_2328_);
lean_closure_set(v___f_2359_, 3, v_ctx_2329_);
v___x_2360_ = l_Lean_Meta_Sym_withoutFoldProjsCheck___at___00Lean_Elab_Tactic_VCGen_run_spec__1___redArg(v___f_2359_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v_snd_2362_; lean_object* v_frameDB_2363_; lean_object* v_invariants_2364_; lean_object* v_vcs_2365_; size_t v_sz_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v_snd_2362_ = lean_ctor_get(v_a_2361_, 1);
lean_inc(v_snd_2362_);
lean_dec(v_a_2361_);
v_frameDB_2363_ = lean_ctor_get(v_snd_2362_, 6);
lean_inc_ref(v_frameDB_2363_);
v_invariants_2364_ = lean_ctor_get(v_snd_2362_, 7);
lean_inc_ref_n(v_invariants_2364_, 2);
v_vcs_2365_ = lean_ctor_get(v_snd_2362_, 8);
lean_inc_ref(v_vcs_2365_);
lean_dec(v_snd_2362_);
v_sz_2366_ = lean_array_size(v_invariants_2364_);
v___x_2367_ = ((size_t)0ULL);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_2366_, v___x_2367_, v_invariants_2364_, v_a_2339_);
if (lean_obj_tag(v___x_2368_) == 0)
{
size_t v_sz_2369_; lean_object* v___x_2370_; 
lean_dec_ref_known(v___x_2368_, 1);
v_sz_2369_ = lean_array_size(v_vcs_2365_);
lean_inc_ref(v_vcs_2365_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_2369_, v___x_2367_, v_vcs_2365_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
lean_dec_ref_known(v___x_2370_, 1);
v___x_2371_ = lean_array_get_size(v_vcs_2365_);
v___x_2372_ = lean_nat_dec_lt(v___x_2343_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_dec_ref(v_vcs_2365_);
v___y_2345_ = v_invariants_2364_;
v___y_2346_ = v_frameDB_2363_;
v_a_2347_ = v___x_2354_;
goto v___jp_2344_;
}
else
{
size_t v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_usize_of_nat(v___x_2371_);
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_VCGen_run_spec__5(v_vcs_2365_, v___x_2367_, v___x_2373_, v___x_2354_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec_ref(v_vcs_2365_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___y_2345_ = v_invariants_2364_;
v___y_2346_ = v_frameDB_2363_;
v_a_2347_ = v_a_2375_;
goto v___jp_2344_;
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v_invariants_2364_);
lean_dec_ref(v_frameDB_2363_);
v_a_2376_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2374_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2374_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec_ref(v_vcs_2365_);
lean_dec_ref(v_invariants_2364_);
lean_dec_ref(v_frameDB_2363_);
v_a_2384_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2370_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2370_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec_ref(v_vcs_2365_);
lean_dec_ref(v_invariants_2364_);
lean_dec_ref(v_frameDB_2363_);
v_a_2392_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2368_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2368_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
v_a_2400_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2360_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2360_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_run___boxed(lean_object* v_goal_2417_, lean_object* v_ctx_2418_, lean_object* v_scope_2419_, lean_object* v_stepLimit_x3f_2420_, lean_object* v_frameDB_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Elab_Tactic_VCGen_run(v_goal_2417_, v_ctx_2418_, v_scope_2419_, v_stepLimit_x3f_2420_, v_frameDB_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(lean_object* v_mvarId_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___redArg(v_mvarId_2433_, v___y_2440_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0___boxed(lean_object* v_mvarId_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_VCGen_run_spec__0(v_mvarId_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec(v_mvarId_2445_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(lean_object* v_as_2457_, size_t v_sz_2458_, size_t v_i_2459_, lean_object* v_bs_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___redArg(v_sz_2458_, v_i_2459_, v_bs_2460_, v___y_2467_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3___boxed(lean_object* v_as_2472_, lean_object* v_sz_2473_, lean_object* v_i_2474_, lean_object* v_bs_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
size_t v_sz_boxed_2486_; size_t v_i_boxed_2487_; lean_object* v_res_2488_; 
v_sz_boxed_2486_ = lean_unbox_usize(v_sz_2473_);
lean_dec(v_sz_2473_);
v_i_boxed_2487_ = lean_unbox_usize(v_i_2474_);
lean_dec(v_i_2474_);
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__3(v_as_2472_, v_sz_boxed_2486_, v_i_boxed_2487_, v_bs_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v_as_2472_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(lean_object* v_as_2489_, size_t v_sz_2490_, size_t v_i_2491_, lean_object* v_bs_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___redArg(v_sz_2490_, v_i_2491_, v_bs_2492_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4___boxed(lean_object* v_as_2504_, lean_object* v_sz_2505_, lean_object* v_i_2506_, lean_object* v_bs_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
size_t v_sz_boxed_2518_; size_t v_i_boxed_2519_; lean_object* v_res_2520_; 
v_sz_boxed_2518_ = lean_unbox_usize(v_sz_2505_);
lean_dec(v_sz_2505_);
v_i_boxed_2519_ = lean_unbox_usize(v_i_2506_);
lean_dec(v_i_2506_);
v_res_2520_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_VCGen_run_spec__4(v_as_2504_, v_sz_boxed_2518_, v_i_boxed_2519_, v_bs_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v_as_2504_);
return v_res_2520_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Solve(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Solve(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_RenameInaccessibles(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_RenameInaccessibles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_Driver(builtin);
}
#ifdef __cplusplus
}
#endif
