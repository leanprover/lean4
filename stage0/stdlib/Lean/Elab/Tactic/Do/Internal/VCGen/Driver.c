// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Driver
// Imports: public import Lean.Elab.Tactic.Meta public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.Solve public import Lean.Meta.Sym.Grind
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_grind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkGoalCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "`grind` failed on goal:"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2_value;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__4_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__8_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__11_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__13_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "renameI"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__17_value),LEAN_SCALAR_PTR_LITERAL(20, 41, 101, 89, 107, 117, 242, 244)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rename_i"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__25_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SpecProof.global "};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.local "};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.stx _ "};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "No spec matching the monad "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " found for program "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ". Candidates were "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7;
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "No spec found for program "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "Did not know how to decompose weakest precondition for "};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "vc"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_14_ = lean_apply_12(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0___boxed(lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0(v_x_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(lean_object* v_mvarId_29_, lean_object* v_x_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_43_, 0, v_x_30_);
lean_closure_set(v___f_43_, 1, v___y_31_);
lean_closure_set(v___f_43_, 2, v___y_32_);
lean_closure_set(v___f_43_, 3, v___y_33_);
lean_closure_set(v___f_43_, 4, v___y_34_);
lean_closure_set(v___f_43_, 5, v___y_35_);
lean_closure_set(v___f_43_, 6, v___y_36_);
lean_closure_set(v___f_43_, 7, v___y_37_);
v___x_44_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_29_, v___f_43_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg___boxed(lean_object* v_mvarId_53_, lean_object* v_x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_53_, v_x_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1(lean_object* v_00_u03b1_68_, lean_object* v_mvarId_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_69_, v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___boxed(lean_object* v_00_u03b1_84_, lean_object* v_mvarId_85_, lean_object* v_x_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1(v_00_u03b1_84_, v_mvarId_85_, v_x_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_99_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0(lean_object* v_x_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0___boxed(lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___lam__0(v_x_102_);
lean_dec(v_x_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = l_List_reverse___redArg(v_x_106_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v_head_119_; lean_object* v_tail_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_138_; 
v_head_119_ = lean_ctor_get(v_x_105_, 0);
v_tail_120_ = lean_ctor_get(v_x_105_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_105_);
if (v_isSharedCheck_138_ == 0)
{
v___x_122_ = v_x_105_;
v_isShared_123_ = v_isSharedCheck_138_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_tail_120_);
lean_inc(v_head_119_);
lean_dec(v_x_105_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_138_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_Meta_Grind_mkGoalCore(v_head_119_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_x_106_);
lean_ctor_set(v___x_122_, 0, v_a_125_);
v___x_127_ = v___x_122_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_x_106_);
v___x_127_ = v_reuseFailAlloc_129_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v_x_105_ = v_tail_120_;
v_x_106_ = v___x_127_;
goto _start;
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_del_object(v___x_122_);
lean_dec(v_tail_120_);
lean_dec(v_x_106_);
v_a_130_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_124_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_124_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg___boxed(lean_object* v_x_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(v_x_139_, v_x_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_msgData_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; lean_object* v_env_159_; lean_object* v___x_160_; lean_object* v_mctx_161_; lean_object* v_lctx_162_; lean_object* v_options_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_158_ = lean_st_ref_get(v___y_156_);
v_env_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_env_159_);
lean_dec(v___x_158_);
v___x_160_ = lean_st_ref_get(v___y_154_);
v_mctx_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc_ref(v_mctx_161_);
lean_dec(v___x_160_);
v_lctx_162_ = lean_ctor_get(v___y_153_, 2);
v_options_163_ = lean_ctor_get(v___y_155_, 2);
lean_inc_ref(v_options_163_);
lean_inc_ref(v_lctx_162_);
v___x_164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_164_, 0, v_env_159_);
lean_ctor_set(v___x_164_, 1, v_mctx_161_);
lean_ctor_set(v___x_164_, 2, v_lctx_162_);
lean_ctor_set(v___x_164_, 3, v_options_163_);
v___x_165_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_msgData_152_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_msgData_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(v_msgData_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5(lean_object* v_opts_174_, lean_object* v_opt_175_){
_start:
{
lean_object* v_name_176_; lean_object* v_defValue_177_; lean_object* v_map_178_; lean_object* v___x_179_; 
v_name_176_ = lean_ctor_get(v_opt_175_, 0);
v_defValue_177_ = lean_ctor_get(v_opt_175_, 1);
v_map_178_ = lean_ctor_get(v_opts_174_, 0);
v___x_179_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_178_, v_name_176_);
if (lean_obj_tag(v___x_179_) == 0)
{
uint8_t v___x_180_; 
v___x_180_ = lean_unbox(v_defValue_177_);
return v___x_180_;
}
else
{
lean_object* v_val_181_; 
v_val_181_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v___x_179_, 1);
if (lean_obj_tag(v_val_181_) == 1)
{
uint8_t v_v_182_; 
v_v_182_ = lean_ctor_get_uint8(v_val_181_, 0);
lean_dec_ref_known(v_val_181_, 0);
return v_v_182_;
}
else
{
uint8_t v___x_183_; 
lean_dec(v_val_181_);
v___x_183_ = lean_unbox(v_defValue_177_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_opts_184_, lean_object* v_opt_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5(v_opts_184_, v_opt_185_);
lean_dec_ref(v_opt_185_);
lean_dec_ref(v_opts_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v___y_196_, uint8_t v_suppressElabErrors_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_198_) == 1)
{
lean_object* v_pre_199_; 
v_pre_199_ = lean_ctor_get(v_x_198_, 0);
switch(lean_obj_tag(v_pre_199_))
{
case 1:
{
lean_object* v_pre_200_; 
v_pre_200_ = lean_ctor_get(v_pre_199_, 0);
switch(lean_obj_tag(v_pre_200_))
{
case 0:
{
lean_object* v_str_201_; lean_object* v_str_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_str_201_ = lean_ctor_get(v_x_198_, 1);
v_str_202_ = lean_ctor_get(v_pre_199_, 1);
v___x_203_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_204_ = lean_string_dec_eq(v_str_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_206_ = lean_string_dec_eq(v_str_202_, v___x_205_);
if (v___x_206_ == 0)
{
return v___y_196_;
}
else
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_208_ = lean_string_dec_eq(v_str_201_, v___x_207_);
if (v___x_208_ == 0)
{
return v___y_196_;
}
else
{
return v_suppressElabErrors_197_;
}
}
}
else
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_210_ = lean_string_dec_eq(v_str_201_, v___x_209_);
if (v___x_210_ == 0)
{
return v___y_196_;
}
else
{
return v_suppressElabErrors_197_;
}
}
}
case 1:
{
lean_object* v_pre_211_; 
v_pre_211_ = lean_ctor_get(v_pre_200_, 0);
if (lean_obj_tag(v_pre_211_) == 0)
{
lean_object* v_str_212_; lean_object* v_str_213_; lean_object* v_str_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_str_212_ = lean_ctor_get(v_x_198_, 1);
v_str_213_ = lean_ctor_get(v_pre_199_, 1);
v_str_214_ = lean_ctor_get(v_pre_200_, 1);
v___x_215_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_216_ = lean_string_dec_eq(v_str_214_, v___x_215_);
if (v___x_216_ == 0)
{
return v___y_196_;
}
else
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
v___x_218_ = lean_string_dec_eq(v_str_213_, v___x_217_);
if (v___x_218_ == 0)
{
return v___y_196_;
}
else
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
v___x_220_ = lean_string_dec_eq(v_str_212_, v___x_219_);
if (v___x_220_ == 0)
{
return v___y_196_;
}
else
{
return v_suppressElabErrors_197_;
}
}
}
}
else
{
return v___y_196_;
}
}
default: 
{
return v___y_196_;
}
}
}
case 0:
{
lean_object* v_str_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_str_221_ = lean_ctor_get(v_x_198_, 1);
v___x_222_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7));
v___x_223_ = lean_string_dec_eq(v_str_221_, v___x_222_);
if (v___x_223_ == 0)
{
return v___y_196_;
}
else
{
return v_suppressElabErrors_197_;
}
}
default: 
{
return v___y_196_;
}
}
}
else
{
return v___y_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_224_, lean_object* v_suppressElabErrors_225_, lean_object* v_x_226_){
_start:
{
uint8_t v___y_42436__boxed_227_; uint8_t v_suppressElabErrors_boxed_228_; uint8_t v_res_229_; lean_object* v_r_230_; 
v___y_42436__boxed_227_ = lean_unbox(v___y_224_);
v_suppressElabErrors_boxed_228_ = lean_unbox(v_suppressElabErrors_225_);
v_res_229_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0(v___y_42436__boxed_227_, v_suppressElabErrors_boxed_228_, v_x_226_);
lean_dec(v_x_226_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_232_, lean_object* v_msgData_233_, uint8_t v_severity_234_, uint8_t v_isSilent_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; uint8_t v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_278_; uint8_t v___y_279_; uint8_t v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; uint8_t v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_303_; uint8_t v___y_304_; lean_object* v___y_305_; lean_object* v___y_306_; uint8_t v___y_307_; lean_object* v___y_308_; uint8_t v___y_309_; lean_object* v___y_310_; lean_object* v___y_314_; uint8_t v___y_315_; uint8_t v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; uint8_t v___y_320_; uint8_t v___x_325_; lean_object* v___y_327_; lean_object* v___y_328_; uint8_t v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; uint8_t v___y_332_; uint8_t v___y_333_; uint8_t v___y_335_; uint8_t v___x_350_; 
v___x_325_ = 2;
v___x_350_ = l_Lean_instBEqMessageSeverity_beq(v_severity_234_, v___x_325_);
if (v___x_350_ == 0)
{
v___y_335_ = v___x_350_;
goto v___jp_334_;
}
else
{
uint8_t v___x_351_; 
lean_inc_ref(v_msgData_233_);
v___x_351_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_233_);
v___y_335_ = v___x_351_;
goto v___jp_334_;
}
v___jp_241_:
{
lean_object* v___x_251_; lean_object* v_currNamespace_252_; lean_object* v_openDecls_253_; lean_object* v_env_254_; lean_object* v_nextMacroScope_255_; lean_object* v_ngen_256_; lean_object* v_auxDeclNGen_257_; lean_object* v_traceState_258_; lean_object* v_cache_259_; lean_object* v_messages_260_; lean_object* v_infoState_261_; lean_object* v_snapshotTasks_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_276_; 
v___x_251_ = lean_st_ref_take(v___y_250_);
v_currNamespace_252_ = lean_ctor_get(v___y_249_, 6);
v_openDecls_253_ = lean_ctor_get(v___y_249_, 7);
v_env_254_ = lean_ctor_get(v___x_251_, 0);
v_nextMacroScope_255_ = lean_ctor_get(v___x_251_, 1);
v_ngen_256_ = lean_ctor_get(v___x_251_, 2);
v_auxDeclNGen_257_ = lean_ctor_get(v___x_251_, 3);
v_traceState_258_ = lean_ctor_get(v___x_251_, 4);
v_cache_259_ = lean_ctor_get(v___x_251_, 5);
v_messages_260_ = lean_ctor_get(v___x_251_, 6);
v_infoState_261_ = lean_ctor_get(v___x_251_, 7);
v_snapshotTasks_262_ = lean_ctor_get(v___x_251_, 8);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_276_ == 0)
{
v___x_264_ = v___x_251_;
v_isShared_265_ = v_isSharedCheck_276_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_snapshotTasks_262_);
lean_inc(v_infoState_261_);
lean_inc(v_messages_260_);
lean_inc(v_cache_259_);
lean_inc(v_traceState_258_);
lean_inc(v_auxDeclNGen_257_);
lean_inc(v_ngen_256_);
lean_inc(v_nextMacroScope_255_);
lean_inc(v_env_254_);
lean_dec(v___x_251_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_276_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
lean_inc(v_openDecls_253_);
lean_inc(v_currNamespace_252_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_currNamespace_252_);
lean_ctor_set(v___x_266_, 1, v_openDecls_253_);
v___x_267_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___y_243_);
lean_inc_ref(v___y_244_);
lean_inc_ref(v___y_245_);
v___x_268_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_268_, 0, v___y_245_);
lean_ctor_set(v___x_268_, 1, v___y_248_);
lean_ctor_set(v___x_268_, 2, v___y_246_);
lean_ctor_set(v___x_268_, 3, v___y_244_);
lean_ctor_set(v___x_268_, 4, v___x_267_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*5, v___y_242_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*5 + 1, v___y_247_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*5 + 2, v_isSilent_235_);
v___x_269_ = l_Lean_MessageLog_add(v___x_268_, v_messages_260_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 6, v___x_269_);
v___x_271_ = v___x_264_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_env_254_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_nextMacroScope_255_);
lean_ctor_set(v_reuseFailAlloc_275_, 2, v_ngen_256_);
lean_ctor_set(v_reuseFailAlloc_275_, 3, v_auxDeclNGen_257_);
lean_ctor_set(v_reuseFailAlloc_275_, 4, v_traceState_258_);
lean_ctor_set(v_reuseFailAlloc_275_, 5, v_cache_259_);
lean_ctor_set(v_reuseFailAlloc_275_, 6, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_275_, 7, v_infoState_261_);
lean_ctor_set(v_reuseFailAlloc_275_, 8, v_snapshotTasks_262_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_st_ref_set(v___y_250_, v___x_271_);
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
}
v___jp_277_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_301_; 
v___x_286_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_233_);
v___x_287_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(v___x_286_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_301_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_301_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_301_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_inc_ref_n(v___y_282_, 2);
v___x_292_ = l_Lean_FileMap_toPosition(v___y_282_, v___y_284_);
lean_dec(v___y_284_);
v___x_293_ = l_Lean_FileMap_toPosition(v___y_282_, v___y_285_);
lean_dec(v___y_285_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___x_295_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0));
if (v___y_280_ == 0)
{
lean_del_object(v___x_290_);
lean_dec_ref(v___y_278_);
v___y_242_ = v___y_279_;
v___y_243_ = v_a_288_;
v___y_244_ = v___x_295_;
v___y_245_ = v___y_281_;
v___y_246_ = v___x_294_;
v___y_247_ = v___y_283_;
v___y_248_ = v___x_292_;
v___y_249_ = v___y_238_;
v___y_250_ = v___y_239_;
goto v___jp_241_;
}
else
{
uint8_t v___x_296_; 
lean_inc(v_a_288_);
v___x_296_ = l_Lean_MessageData_hasTag(v___y_278_, v_a_288_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec_ref_known(v___x_294_, 1);
lean_dec_ref(v___x_292_);
lean_dec(v_a_288_);
v___x_297_ = lean_box(0);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_297_);
v___x_299_ = v___x_290_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
else
{
lean_del_object(v___x_290_);
v___y_242_ = v___y_279_;
v___y_243_ = v_a_288_;
v___y_244_ = v___x_295_;
v___y_245_ = v___y_281_;
v___y_246_ = v___x_294_;
v___y_247_ = v___y_283_;
v___y_248_ = v___x_292_;
v___y_249_ = v___y_238_;
v___y_250_ = v___y_239_;
goto v___jp_241_;
}
}
}
}
v___jp_302_:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Syntax_getTailPos_x3f(v___y_305_, v___y_304_);
lean_dec(v___y_305_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_inc(v___y_310_);
v___y_278_ = v___y_303_;
v___y_279_ = v___y_304_;
v___y_280_ = v___y_307_;
v___y_281_ = v___y_306_;
v___y_282_ = v___y_308_;
v___y_283_ = v___y_309_;
v___y_284_ = v___y_310_;
v___y_285_ = v___y_310_;
goto v___jp_277_;
}
else
{
lean_object* v_val_312_; 
v_val_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_val_312_);
lean_dec_ref_known(v___x_311_, 1);
v___y_278_ = v___y_303_;
v___y_279_ = v___y_304_;
v___y_280_ = v___y_307_;
v___y_281_ = v___y_306_;
v___y_282_ = v___y_308_;
v___y_283_ = v___y_309_;
v___y_284_ = v___y_310_;
v___y_285_ = v_val_312_;
goto v___jp_277_;
}
}
v___jp_313_:
{
lean_object* v_ref_321_; lean_object* v___x_322_; 
v_ref_321_ = l_Lean_replaceRef(v_ref_232_, v___y_318_);
v___x_322_ = l_Lean_Syntax_getPos_x3f(v_ref_321_, v___y_315_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___y_303_ = v___y_314_;
v___y_304_ = v___y_315_;
v___y_305_ = v_ref_321_;
v___y_306_ = v___y_317_;
v___y_307_ = v___y_316_;
v___y_308_ = v___y_319_;
v___y_309_ = v___y_320_;
v___y_310_ = v___x_323_;
goto v___jp_302_;
}
else
{
lean_object* v_val_324_; 
v_val_324_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_val_324_);
lean_dec_ref_known(v___x_322_, 1);
v___y_303_ = v___y_314_;
v___y_304_ = v___y_315_;
v___y_305_ = v_ref_321_;
v___y_306_ = v___y_317_;
v___y_307_ = v___y_316_;
v___y_308_ = v___y_319_;
v___y_309_ = v___y_320_;
v___y_310_ = v_val_324_;
goto v___jp_302_;
}
}
v___jp_326_:
{
if (v___y_333_ == 0)
{
v___y_314_ = v___y_327_;
v___y_315_ = v___y_332_;
v___y_316_ = v___y_329_;
v___y_317_ = v___y_328_;
v___y_318_ = v___y_330_;
v___y_319_ = v___y_331_;
v___y_320_ = v_severity_234_;
goto v___jp_313_;
}
else
{
v___y_314_ = v___y_327_;
v___y_315_ = v___y_332_;
v___y_316_ = v___y_329_;
v___y_317_ = v___y_328_;
v___y_318_ = v___y_330_;
v___y_319_ = v___y_331_;
v___y_320_ = v___x_325_;
goto v___jp_313_;
}
}
v___jp_334_:
{
if (v___y_335_ == 0)
{
lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_options_338_; lean_object* v_ref_339_; uint8_t v_suppressElabErrors_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___f_343_; uint8_t v___x_344_; uint8_t v___x_345_; 
v_fileName_336_ = lean_ctor_get(v___y_238_, 0);
v_fileMap_337_ = lean_ctor_get(v___y_238_, 1);
v_options_338_ = lean_ctor_get(v___y_238_, 2);
v_ref_339_ = lean_ctor_get(v___y_238_, 5);
v_suppressElabErrors_340_ = lean_ctor_get_uint8(v___y_238_, sizeof(void*)*14 + 1);
v___x_341_ = lean_box(v___y_335_);
v___x_342_ = lean_box(v_suppressElabErrors_340_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_343_, 0, v___x_341_);
lean_closure_set(v___f_343_, 1, v___x_342_);
v___x_344_ = 1;
v___x_345_ = l_Lean_instBEqMessageSeverity_beq(v_severity_234_, v___x_344_);
if (v___x_345_ == 0)
{
v___y_327_ = v___f_343_;
v___y_328_ = v_fileName_336_;
v___y_329_ = v_suppressElabErrors_340_;
v___y_330_ = v_ref_339_;
v___y_331_ = v_fileMap_337_;
v___y_332_ = v___y_335_;
v___y_333_ = v___x_345_;
goto v___jp_326_;
}
else
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = l_Lean_warningAsError;
v___x_347_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__5(v_options_338_, v___x_346_);
v___y_327_ = v___f_343_;
v___y_328_ = v_fileName_336_;
v___y_329_ = v_suppressElabErrors_340_;
v___y_330_ = v_ref_339_;
v___y_331_ = v_fileMap_337_;
v___y_332_ = v___y_335_;
v___y_333_ = v___x_347_;
goto v___jp_326_;
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec_ref(v_msgData_233_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_352_, lean_object* v_msgData_353_, lean_object* v_severity_354_, lean_object* v_isSilent_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v_severity_boxed_361_; uint8_t v_isSilent_boxed_362_; lean_object* v_res_363_; 
v_severity_boxed_361_ = lean_unbox(v_severity_354_);
v_isSilent_boxed_362_ = lean_unbox(v_isSilent_355_);
v_res_363_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_352_, v_msgData_353_, v_severity_boxed_361_, v_isSilent_boxed_362_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v_ref_352_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(lean_object* v_msgData_364_, uint8_t v_severity_365_, uint8_t v_isSilent_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_ref_379_; lean_object* v___x_380_; 
v_ref_379_ = lean_ctor_get(v___y_376_, 5);
v___x_380_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_379_, v_msgData_364_, v_severity_365_, v_isSilent_366_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0___boxed(lean_object* v_msgData_381_, lean_object* v_severity_382_, lean_object* v_isSilent_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
uint8_t v_severity_boxed_396_; uint8_t v_isSilent_boxed_397_; lean_object* v_res_398_; 
v_severity_boxed_396_ = lean_unbox(v_severity_382_);
v_isSilent_boxed_397_ = lean_unbox(v_isSilent_383_);
v_res_398_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(v_msgData_381_, v_severity_boxed_396_, v_isSilent_boxed_397_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0(lean_object* v_msgData_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; 
v___x_412_ = 2;
v___x_413_ = 0;
v___x_414_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(v_msgData_399_, v___x_412_, v___x_413_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0___boxed(lean_object* v_msgData_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0(v_msgData_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_428_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
switch(lean_obj_tag(v_x_446_))
{
case 0:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_464_ = lean_box(0);
v___x_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_465_, 0, v_x_447_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
return v___x_466_;
}
case 1:
{
uint8_t v_silent_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_silent_467_ = lean_ctor_get_uint8(v_x_446_, 0);
lean_dec_ref_known(v_x_446_, 0);
v___x_468_ = lean_st_ref_get(v_a_456_);
lean_inc_ref(v_x_447_);
v___x_469_ = l_Lean_Meta_Grind_Goal_grind(v_x_447_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_532_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_532_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_532_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_532_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
if (lean_obj_tag(v_a_470_) == 0)
{
lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_526_; 
lean_del_object(v___x_472_);
v_isSharedCheck_526_ = !lean_is_exclusive(v_a_470_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v_a_470_, 0);
lean_dec(v_unused_527_);
v___x_475_ = v_a_470_;
v_isShared_476_ = v_isSharedCheck_526_;
goto v_resetjp_474_;
}
else
{
lean_dec(v_a_470_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_526_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v_mctx_478_; lean_object* v_cache_479_; lean_object* v_zetaDeltaFVarIds_480_; lean_object* v_postponed_481_; lean_object* v_diag_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_524_; 
v___x_477_ = lean_st_ref_take(v_a_456_);
v_mctx_478_ = lean_ctor_get(v___x_468_, 0);
lean_inc_ref(v_mctx_478_);
lean_dec(v___x_468_);
v_cache_479_ = lean_ctor_get(v___x_477_, 1);
v_zetaDeltaFVarIds_480_ = lean_ctor_get(v___x_477_, 2);
v_postponed_481_ = lean_ctor_get(v___x_477_, 3);
v_diag_482_ = lean_ctor_get(v___x_477_, 4);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_477_, 0);
lean_dec(v_unused_525_);
v___x_484_ = v___x_477_;
v_isShared_485_ = v_isSharedCheck_524_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_diag_482_);
lean_inc(v_postponed_481_);
lean_inc(v_zetaDeltaFVarIds_480_);
lean_inc(v_cache_479_);
lean_dec(v___x_477_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_524_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v_mctx_478_);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_mctx_478_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_cache_479_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_zetaDeltaFVarIds_480_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_postponed_481_);
lean_ctor_set(v_reuseFailAlloc_523_, 4, v_diag_482_);
v___x_487_ = v_reuseFailAlloc_523_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; 
v___x_488_ = lean_st_ref_set(v_a_456_, v___x_487_);
if (v_silent_467_ == 0)
{
lean_object* v_mvarId_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
v_mvarId_489_ = lean_ctor_get(v_x_447_, 1);
v___x_490_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1);
lean_inc(v_mvarId_489_);
if (v_isShared_476_ == 0)
{
lean_ctor_set_tag(v___x_475_, 1);
lean_ctor_set(v___x_475_, 0, v_mvarId_489_);
v___x_492_ = v___x_475_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_mvarId_489_);
v___x_492_ = v_reuseFailAlloc_522_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = l_Lean_indentD(v___x_492_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_490_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_closure((void*)(l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0___boxed), 13, 1);
lean_closure_set(v___x_495_, 0, v___x_494_);
lean_inc(v_mvarId_489_);
v___x_496_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_489_, v___x_495_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v___x_497_; lean_object* v_specBackwardRuleCache_498_; lean_object* v_splitBackwardRuleCache_499_; lean_object* v_invariants_500_; lean_object* v_vcs_501_; lean_object* v_simpState_502_; lean_object* v_fuel_503_; lean_object* v_inlineHandledInvariants_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_513_; 
lean_dec_ref_known(v___x_496_, 1);
v___x_497_ = lean_st_ref_take(v_a_449_);
v_specBackwardRuleCache_498_ = lean_ctor_get(v___x_497_, 0);
v_splitBackwardRuleCache_499_ = lean_ctor_get(v___x_497_, 1);
v_invariants_500_ = lean_ctor_get(v___x_497_, 2);
v_vcs_501_ = lean_ctor_get(v___x_497_, 3);
v_simpState_502_ = lean_ctor_get(v___x_497_, 4);
v_fuel_503_ = lean_ctor_get(v___x_497_, 5);
v_inlineHandledInvariants_504_ = lean_ctor_get(v___x_497_, 6);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_513_ == 0)
{
v___x_506_ = v___x_497_;
v_isShared_507_ = v_isSharedCheck_513_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_inlineHandledInvariants_504_);
lean_inc(v_fuel_503_);
lean_inc(v_simpState_502_);
lean_inc(v_vcs_501_);
lean_inc(v_invariants_500_);
lean_inc(v_splitBackwardRuleCache_499_);
lean_inc(v_specBackwardRuleCache_498_);
lean_dec(v___x_497_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_513_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
uint8_t v___x_508_; lean_object* v___x_510_; 
v___x_508_ = 1;
if (v_isShared_507_ == 0)
{
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_specBackwardRuleCache_498_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_splitBackwardRuleCache_499_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_invariants_500_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_vcs_501_);
lean_ctor_set(v_reuseFailAlloc_512_, 4, v_simpState_502_);
lean_ctor_set(v_reuseFailAlloc_512_, 5, v_fuel_503_);
lean_ctor_set(v_reuseFailAlloc_512_, 6, v_inlineHandledInvariants_504_);
v___x_510_ = v_reuseFailAlloc_512_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; 
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*7, v___x_508_);
v___x_511_ = lean_st_ref_set(v_a_449_, v___x_510_);
goto v___jp_460_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v_x_447_);
v_a_514_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_496_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_496_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
else
{
lean_del_object(v___x_475_);
goto v___jp_460_;
}
}
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_530_; 
lean_dec(v___x_468_);
lean_dec_ref(v_x_447_);
v___x_528_ = lean_box(0);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_528_);
v___x_530_ = v___x_472_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v___x_468_);
lean_dec_ref(v_x_447_);
v_a_533_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_469_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_469_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
default: 
{
lean_object* v_tac_541_; lean_object* v_mvarId_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_tac_541_ = lean_ctor_get(v_x_446_, 0);
lean_inc(v_tac_541_);
lean_dec_ref_known(v_x_446_, 1);
v_mvarId_542_ = lean_ctor_get(v_x_447_, 1);
lean_inc(v_mvarId_542_);
lean_dec_ref(v_x_447_);
v___x_543_ = lean_box(0);
v___x_544_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4));
v___x_545_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5));
v___x_546_ = l_Lean_Elab_runTactic(v_mvarId_542_, v_tac_541_, v___x_544_, v___x_545_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v_fst_548_; lean_object* v___x_549_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v_fst_548_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_fst_548_);
lean_dec(v_a_547_);
v___x_549_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(v_fst_548_, v___x_543_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
return v___x_549_;
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_546_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_546_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
v___jp_460_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_box(0);
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v_x_447_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___boxed(lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(v_x_558_, v_x_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2(lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___redArg(v_x_573_, v_x_574_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2___boxed(lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__2(v_x_588_, v_x_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2(lean_object* v_ref_603_, lean_object* v_msgData_604_, uint8_t v_severity_605_, uint8_t v_isSilent_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_603_, v_msgData_604_, v_severity_605_, v_isSilent_606_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_620_, lean_object* v_msgData_621_, lean_object* v_severity_622_, lean_object* v_isSilent_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
uint8_t v_severity_boxed_636_; uint8_t v_isSilent_boxed_637_; lean_object* v_res_638_; 
v_severity_boxed_636_ = lean_unbox(v_severity_622_);
v_isSilent_boxed_637_ = lean_unbox(v_isSilent_623_);
v_res_638_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2(v_ref_620_, v_msgData_621_, v_severity_boxed_636_, v_isSilent_boxed_637_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v_ref_620_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(lean_object* v_mvarId_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; lean_object* v_mctx_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_st_ref_get(v___y_640_);
v_mctx_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc_ref(v_mctx_643_);
lean_dec(v___x_642_);
v___x_644_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_643_, v_mvarId_639_);
lean_dec_ref(v_mctx_643_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg___boxed(lean_object* v_mvarId_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mvarId_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec(v_mvarId_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(lean_object* v_mvarId_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mvarId_650_, v___y_654_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___boxed(lean_object* v_mvarId_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2(v_mvarId_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v_mvarId_659_);
return v_res_667_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_keys_668_, lean_object* v_i_669_, lean_object* v_k_670_){
_start:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_array_get_size(v_keys_668_);
v___x_672_ = lean_nat_dec_lt(v_i_669_, v___x_671_);
if (v___x_672_ == 0)
{
lean_dec(v_i_669_);
return v___x_672_;
}
else
{
lean_object* v_k_x27_673_; uint8_t v___x_674_; 
v_k_x27_673_ = lean_array_fget_borrowed(v_keys_668_, v_i_669_);
v___x_674_ = l_Lean_instBEqMVarId_beq(v_k_670_, v_k_x27_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = lean_nat_add(v_i_669_, v___x_675_);
lean_dec(v_i_669_);
v_i_669_ = v___x_676_;
goto _start;
}
else
{
lean_dec(v_i_669_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_keys_678_, lean_object* v_i_679_, lean_object* v_k_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_678_, v_i_679_, v_k_680_);
lean_dec(v_k_680_);
lean_dec_ref(v_keys_678_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; 
v___x_683_ = ((size_t)5ULL);
v___x_684_ = ((size_t)1ULL);
v___x_685_ = lean_usize_shift_left(v___x_684_, v___x_683_);
return v___x_685_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_686_; size_t v___x_687_; size_t v___x_688_; 
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_688_ = lean_usize_sub(v___x_687_, v___x_686_);
return v___x_688_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(lean_object* v_x_689_, size_t v_x_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_object* v_es_692_; lean_object* v___x_693_; size_t v___x_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v_j_697_; lean_object* v___x_698_; 
v_es_692_ = lean_ctor_get(v_x_689_, 0);
v___x_693_ = lean_box(2);
v___x_694_ = ((size_t)5ULL);
v___x_695_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_696_ = lean_usize_land(v_x_690_, v___x_695_);
v_j_697_ = lean_usize_to_nat(v___x_696_);
v___x_698_ = lean_array_get_borrowed(v___x_693_, v_es_692_, v_j_697_);
lean_dec(v_j_697_);
switch(lean_obj_tag(v___x_698_))
{
case 0:
{
lean_object* v_key_699_; uint8_t v___x_700_; 
v_key_699_ = lean_ctor_get(v___x_698_, 0);
v___x_700_ = l_Lean_instBEqMVarId_beq(v_x_691_, v_key_699_);
return v___x_700_;
}
case 1:
{
lean_object* v_node_701_; size_t v___x_702_; 
v_node_701_ = lean_ctor_get(v___x_698_, 0);
v___x_702_ = lean_usize_shift_right(v_x_690_, v___x_694_);
v_x_689_ = v_node_701_;
v_x_690_ = v___x_702_;
goto _start;
}
default: 
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
}
}
else
{
lean_object* v_ks_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_ks_705_ = lean_ctor_get(v_x_689_, 0);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_ks_705_, v___x_706_, v_x_691_);
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
size_t v_x_17592__boxed_711_; uint8_t v_res_712_; lean_object* v_r_713_; 
v_x_17592__boxed_711_ = lean_unbox_usize(v_x_709_);
lean_dec(v_x_709_);
v_res_712_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_708_, v_x_17592__boxed_711_, v_x_710_);
lean_dec(v_x_710_);
lean_dec_ref(v_x_708_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
uint64_t v___x_716_; size_t v___x_717_; uint8_t v___x_718_; 
v___x_716_ = l_Lean_instHashableMVarId_hash(v_x_715_);
v___x_717_ = lean_uint64_to_usize(v___x_716_);
v___x_718_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_714_, v___x_717_, v_x_715_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg___boxed(lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec_ref(v_x_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(lean_object* v_mvarId_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; lean_object* v_mctx_727_; lean_object* v_eAssignment_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_726_ = lean_st_ref_get(v___y_724_);
v_mctx_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_mctx_727_);
lean_dec(v___x_726_);
v_eAssignment_728_ = lean_ctor_get(v_mctx_727_, 8);
lean_inc_ref(v_eAssignment_728_);
lean_dec_ref(v_mctx_727_);
v___x_729_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_728_, v_mvarId_723_);
lean_dec_ref(v_eAssignment_728_);
v___x_730_ = lean_box(v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg___boxed(lean_object* v_mvarId_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec(v_mvarId_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
lean_object* v_ks_740_; lean_object* v_vs_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_765_; 
v_ks_740_ = lean_ctor_get(v_x_736_, 0);
v_vs_741_ = lean_ctor_get(v_x_736_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_736_);
if (v_isSharedCheck_765_ == 0)
{
v___x_743_ = v_x_736_;
v_isShared_744_ = v_isSharedCheck_765_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_vs_741_);
lean_inc(v_ks_740_);
lean_dec(v_x_736_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_765_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = lean_array_get_size(v_ks_740_);
v___x_746_ = lean_nat_dec_lt(v_x_737_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
lean_dec(v_x_737_);
v___x_747_ = lean_array_push(v_ks_740_, v_x_738_);
v___x_748_ = lean_array_push(v_vs_741_, v_x_739_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_748_);
lean_ctor_set(v___x_743_, 0, v___x_747_);
v___x_750_ = v___x_743_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
else
{
lean_object* v_k_x27_752_; uint8_t v___x_753_; 
v_k_x27_752_ = lean_array_fget_borrowed(v_ks_740_, v_x_737_);
v___x_753_ = l_Lean_instBEqMVarId_beq(v_x_738_, v_k_x27_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_755_; 
if (v_isShared_744_ == 0)
{
v___x_755_ = v___x_743_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_ks_740_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_vs_741_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_add(v_x_737_, v___x_756_);
lean_dec(v_x_737_);
v_x_736_ = v___x_755_;
v_x_737_ = v___x_757_;
goto _start;
}
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_760_ = lean_array_fset(v_ks_740_, v_x_737_, v_x_738_);
v___x_761_ = lean_array_fset(v_vs_741_, v_x_737_, v_x_739_);
lean_dec(v_x_737_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_761_);
lean_ctor_set(v___x_743_, 0, v___x_760_);
v___x_763_ = v___x_743_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_n_766_, lean_object* v_k_767_, lean_object* v_v_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_n_766_, v___x_769_, v_k_767_, v_v_768_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(lean_object* v_x_772_, size_t v_x_773_, size_t v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
lean_object* v_es_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v_j_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_es_777_ = lean_ctor_get(v_x_772_, 0);
v___x_778_ = ((size_t)5ULL);
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_781_ = lean_usize_land(v_x_773_, v___x_780_);
v_j_782_ = lean_usize_to_nat(v___x_781_);
v___x_783_ = lean_array_get_size(v_es_777_);
v___x_784_ = lean_nat_dec_lt(v_j_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec(v_j_782_);
lean_dec(v_x_776_);
lean_dec(v_x_775_);
return v_x_772_;
}
else
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_821_; 
lean_inc_ref(v_es_777_);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_x_772_, 0);
lean_dec(v_unused_822_);
v___x_786_ = v_x_772_;
v_isShared_787_ = v_isSharedCheck_821_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_x_772_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_821_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_v_788_; lean_object* v___x_789_; lean_object* v_xs_x27_790_; lean_object* v___y_792_; 
v_v_788_ = lean_array_fget(v_es_777_, v_j_782_);
v___x_789_ = lean_box(0);
v_xs_x27_790_ = lean_array_fset(v_es_777_, v_j_782_, v___x_789_);
switch(lean_obj_tag(v_v_788_))
{
case 0:
{
lean_object* v_key_797_; lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_808_; 
v_key_797_ = lean_ctor_get(v_v_788_, 0);
v_val_798_ = lean_ctor_get(v_v_788_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_v_788_);
if (v_isSharedCheck_808_ == 0)
{
v___x_800_ = v_v_788_;
v_isShared_801_ = v_isSharedCheck_808_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_inc(v_key_797_);
lean_dec(v_v_788_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_808_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
uint8_t v___x_802_; 
v___x_802_ = l_Lean_instBEqMVarId_beq(v_x_775_, v_key_797_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_del_object(v___x_800_);
v___x_803_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_797_, v_val_798_, v_x_775_, v_x_776_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___y_792_ = v___x_804_;
goto v___jp_791_;
}
else
{
lean_object* v___x_806_; 
lean_dec(v_val_798_);
lean_dec(v_key_797_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_x_776_);
lean_ctor_set(v___x_800_, 0, v_x_775_);
v___x_806_ = v___x_800_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_x_775_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_x_776_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v___y_792_ = v___x_806_;
goto v___jp_791_;
}
}
}
}
case 1:
{
lean_object* v_node_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
v_node_809_ = lean_ctor_get(v_v_788_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v_v_788_);
if (v_isSharedCheck_819_ == 0)
{
v___x_811_ = v_v_788_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_node_809_);
lean_dec(v_v_788_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_813_ = lean_usize_shift_right(v_x_773_, v___x_778_);
v___x_814_ = lean_usize_add(v_x_774_, v___x_779_);
v___x_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_node_809_, v___x_813_, v___x_814_, v_x_775_, v_x_776_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v___y_792_ = v___x_817_;
goto v___jp_791_;
}
}
}
default: 
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_x_775_);
lean_ctor_set(v___x_820_, 1, v_x_776_);
v___y_792_ = v___x_820_;
goto v___jp_791_;
}
}
v___jp_791_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_array_fset(v_xs_x27_790_, v_j_782_, v___y_792_);
lean_dec(v_j_782_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_793_);
v___x_795_ = v___x_786_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
else
{
lean_object* v_ks_823_; lean_object* v_vs_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_844_; 
v_ks_823_ = lean_ctor_get(v_x_772_, 0);
v_vs_824_ = lean_ctor_get(v_x_772_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_772_);
if (v_isSharedCheck_844_ == 0)
{
v___x_826_ = v_x_772_;
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_vs_824_);
lean_inc(v_ks_823_);
lean_dec(v_x_772_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_ks_823_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_vs_824_);
v___x_829_ = v_reuseFailAlloc_843_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v_newNode_830_; uint8_t v___y_832_; size_t v___x_838_; uint8_t v___x_839_; 
v_newNode_830_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v___x_829_, v_x_775_, v_x_776_);
v___x_838_ = ((size_t)7ULL);
v___x_839_ = lean_usize_dec_le(v___x_838_, v_x_774_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_840_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_830_);
v___x_841_ = lean_unsigned_to_nat(4u);
v___x_842_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
lean_dec(v___x_840_);
v___y_832_ = v___x_842_;
goto v___jp_831_;
}
else
{
v___y_832_ = v___x_839_;
goto v___jp_831_;
}
v___jp_831_:
{
if (v___y_832_ == 0)
{
lean_object* v_ks_833_; lean_object* v_vs_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_ks_833_ = lean_ctor_get(v_newNode_830_, 0);
lean_inc_ref(v_ks_833_);
v_vs_834_ = lean_ctor_get(v_newNode_830_, 1);
lean_inc_ref(v_vs_834_);
lean_dec_ref(v_newNode_830_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___closed__0);
v___x_837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_x_774_, v_ks_833_, v_vs_834_, v___x_835_, v___x_836_);
lean_dec_ref(v_vs_834_);
lean_dec_ref(v_ks_833_);
return v___x_837_;
}
else
{
return v_newNode_830_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(size_t v_depth_845_, lean_object* v_keys_846_, lean_object* v_vals_847_, lean_object* v_i_848_, lean_object* v_entries_849_){
_start:
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_array_get_size(v_keys_846_);
v___x_851_ = lean_nat_dec_lt(v_i_848_, v___x_850_);
if (v___x_851_ == 0)
{
lean_dec(v_i_848_);
return v_entries_849_;
}
else
{
lean_object* v_k_852_; lean_object* v_v_853_; uint64_t v___x_854_; size_t v_h_855_; size_t v___x_856_; lean_object* v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v_h_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_k_852_ = lean_array_fget_borrowed(v_keys_846_, v_i_848_);
v_v_853_ = lean_array_fget_borrowed(v_vals_847_, v_i_848_);
v___x_854_ = l_Lean_instHashableMVarId_hash(v_k_852_);
v_h_855_ = lean_uint64_to_usize(v___x_854_);
v___x_856_ = ((size_t)5ULL);
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_sub(v_depth_845_, v___x_858_);
v___x_860_ = lean_usize_mul(v___x_856_, v___x_859_);
v_h_861_ = lean_usize_shift_right(v_h_855_, v___x_860_);
v___x_862_ = lean_nat_add(v_i_848_, v___x_857_);
lean_dec(v_i_848_);
lean_inc(v_v_853_);
lean_inc(v_k_852_);
v___x_863_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_entries_849_, v_h_861_, v_depth_845_, v_k_852_, v_v_853_);
v_i_848_ = v___x_862_;
v_entries_849_ = v___x_863_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg___boxed(lean_object* v_depth_865_, lean_object* v_keys_866_, lean_object* v_vals_867_, lean_object* v_i_868_, lean_object* v_entries_869_){
_start:
{
size_t v_depth_boxed_870_; lean_object* v_res_871_; 
v_depth_boxed_870_ = lean_unbox_usize(v_depth_865_);
lean_dec(v_depth_865_);
v_res_871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_boxed_870_, v_keys_866_, v_vals_867_, v_i_868_, v_entries_869_);
lean_dec_ref(v_vals_867_);
lean_dec_ref(v_keys_866_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
size_t v_x_17747__boxed_877_; size_t v_x_17748__boxed_878_; lean_object* v_res_879_; 
v_x_17747__boxed_877_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_x_17748__boxed_878_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_res_879_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_872_, v_x_17747__boxed_877_, v_x_17748__boxed_878_, v_x_875_, v_x_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
uint64_t v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_883_ = l_Lean_instHashableMVarId_hash(v_x_881_);
v___x_884_ = lean_uint64_to_usize(v___x_883_);
v___x_885_ = ((size_t)1ULL);
v___x_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_880_, v___x_884_, v___x_885_, v_x_881_, v_x_882_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(lean_object* v_mvarId_887_, lean_object* v_val_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_mctx_892_; lean_object* v_cache_893_; lean_object* v_zetaDeltaFVarIds_894_; lean_object* v_postponed_895_; lean_object* v_diag_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_924_; 
v___x_891_ = lean_st_ref_take(v___y_889_);
v_mctx_892_ = lean_ctor_get(v___x_891_, 0);
v_cache_893_ = lean_ctor_get(v___x_891_, 1);
v_zetaDeltaFVarIds_894_ = lean_ctor_get(v___x_891_, 2);
v_postponed_895_ = lean_ctor_get(v___x_891_, 3);
v_diag_896_ = lean_ctor_get(v___x_891_, 4);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_924_ == 0)
{
v___x_898_ = v___x_891_;
v_isShared_899_ = v_isSharedCheck_924_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_diag_896_);
lean_inc(v_postponed_895_);
lean_inc(v_zetaDeltaFVarIds_894_);
lean_inc(v_cache_893_);
lean_inc(v_mctx_892_);
lean_dec(v___x_891_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_924_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_depth_900_; lean_object* v_levelAssignDepth_901_; lean_object* v_lmvarCounter_902_; lean_object* v_mvarCounter_903_; lean_object* v_lDecls_904_; lean_object* v_decls_905_; lean_object* v_userNames_906_; lean_object* v_lAssignment_907_; lean_object* v_eAssignment_908_; lean_object* v_dAssignment_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_923_; 
v_depth_900_ = lean_ctor_get(v_mctx_892_, 0);
v_levelAssignDepth_901_ = lean_ctor_get(v_mctx_892_, 1);
v_lmvarCounter_902_ = lean_ctor_get(v_mctx_892_, 2);
v_mvarCounter_903_ = lean_ctor_get(v_mctx_892_, 3);
v_lDecls_904_ = lean_ctor_get(v_mctx_892_, 4);
v_decls_905_ = lean_ctor_get(v_mctx_892_, 5);
v_userNames_906_ = lean_ctor_get(v_mctx_892_, 6);
v_lAssignment_907_ = lean_ctor_get(v_mctx_892_, 7);
v_eAssignment_908_ = lean_ctor_get(v_mctx_892_, 8);
v_dAssignment_909_ = lean_ctor_get(v_mctx_892_, 9);
v_isSharedCheck_923_ = !lean_is_exclusive(v_mctx_892_);
if (v_isSharedCheck_923_ == 0)
{
v___x_911_ = v_mctx_892_;
v_isShared_912_ = v_isSharedCheck_923_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_dAssignment_909_);
lean_inc(v_eAssignment_908_);
lean_inc(v_lAssignment_907_);
lean_inc(v_userNames_906_);
lean_inc(v_decls_905_);
lean_inc(v_lDecls_904_);
lean_inc(v_mvarCounter_903_);
lean_inc(v_lmvarCounter_902_);
lean_inc(v_levelAssignDepth_901_);
lean_inc(v_depth_900_);
lean_dec(v_mctx_892_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_923_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_913_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_eAssignment_908_, v_mvarId_887_, v_val_888_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 8, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_depth_900_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_levelAssignDepth_901_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_lmvarCounter_902_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_mvarCounter_903_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_lDecls_904_);
lean_ctor_set(v_reuseFailAlloc_922_, 5, v_decls_905_);
lean_ctor_set(v_reuseFailAlloc_922_, 6, v_userNames_906_);
lean_ctor_set(v_reuseFailAlloc_922_, 7, v_lAssignment_907_);
lean_ctor_set(v_reuseFailAlloc_922_, 8, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_922_, 9, v_dAssignment_909_);
v___x_915_ = v_reuseFailAlloc_922_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_915_);
v___x_917_ = v___x_898_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_cache_893_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_zetaDeltaFVarIds_894_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_postponed_895_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_diag_896_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_918_ = lean_st_ref_set(v___y_889_, v___x_917_);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg___boxed(lean_object* v_mvarId_925_, lean_object* v_val_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_925_, v_val_926_, v___y_927_);
lean_dec(v___y_927_);
return v_res_929_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2(void){
_start:
{
uint8_t v___x_936_; uint64_t v___x_937_; 
v___x_936_ = 1;
v___x_937_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(lean_object* v___f_938_, lean_object* v_mv_939_, lean_object* v_val_940_, lean_object* v_tac_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_955_; uint8_t v___x_956_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_fileName_995_; lean_object* v_fileMap_996_; lean_object* v_options_997_; lean_object* v_currRecDepth_998_; lean_object* v_maxRecDepth_999_; lean_object* v_ref_1000_; lean_object* v_currNamespace_1001_; lean_object* v_openDecls_1002_; lean_object* v_initHeartbeats_1003_; lean_object* v_maxHeartbeats_1004_; lean_object* v_quotContext_1005_; lean_object* v_currMacroScope_1006_; uint8_t v_diag_1007_; lean_object* v_cancelTk_x3f_1008_; uint8_t v_suppressElabErrors_1009_; lean_object* v_inheritedTraceOptions_1010_; lean_object* v___x_1011_; uint8_t v_foApprox_1012_; uint8_t v_ctxApprox_1013_; uint8_t v_quasiPatternApprox_1014_; uint8_t v_constApprox_1015_; uint8_t v_isDefEqStuckEx_1016_; uint8_t v_unificationHints_1017_; uint8_t v_proofIrrelevance_1018_; uint8_t v_assignSyntheticOpaque_1019_; uint8_t v_offsetCnstrs_1020_; uint8_t v_etaStruct_1021_; uint8_t v_univApprox_1022_; uint8_t v_iota_1023_; uint8_t v_beta_1024_; uint8_t v_proj_1025_; uint8_t v_zeta_1026_; uint8_t v_zetaDelta_1027_; uint8_t v_zetaUnused_1028_; uint8_t v_zetaHave_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1067_; 
v___x_949_ = lean_box(0);
v___x_950_ = lean_box(0);
v___x_951_ = 1;
v___x_955_ = lean_box(1);
v___x_956_ = 0;
v___x_993_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3));
v___x_994_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_994_, 0, v___x_949_);
lean_ctor_set(v___x_994_, 1, v___x_950_);
lean_ctor_set(v___x_994_, 2, v___x_949_);
lean_ctor_set(v___x_994_, 3, v___f_938_);
lean_ctor_set(v___x_994_, 4, v___x_955_);
lean_ctor_set(v___x_994_, 5, v___x_955_);
lean_ctor_set(v___x_994_, 6, v___x_949_);
lean_ctor_set(v___x_994_, 7, v___x_993_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8, v___x_951_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 1, v___x_951_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 2, v___x_951_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 3, v___x_951_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 4, v___x_956_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 5, v___x_956_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 6, v___x_956_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 7, v___x_956_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 8, v___x_951_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 9, v___x_956_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*8 + 10, v___x_951_);
v_fileName_995_ = lean_ctor_get(v___y_946_, 0);
v_fileMap_996_ = lean_ctor_get(v___y_946_, 1);
v_options_997_ = lean_ctor_get(v___y_946_, 2);
v_currRecDepth_998_ = lean_ctor_get(v___y_946_, 3);
v_maxRecDepth_999_ = lean_ctor_get(v___y_946_, 4);
v_ref_1000_ = lean_ctor_get(v___y_946_, 5);
v_currNamespace_1001_ = lean_ctor_get(v___y_946_, 6);
v_openDecls_1002_ = lean_ctor_get(v___y_946_, 7);
v_initHeartbeats_1003_ = lean_ctor_get(v___y_946_, 8);
v_maxHeartbeats_1004_ = lean_ctor_get(v___y_946_, 9);
v_quotContext_1005_ = lean_ctor_get(v___y_946_, 10);
v_currMacroScope_1006_ = lean_ctor_get(v___y_946_, 11);
v_diag_1007_ = lean_ctor_get_uint8(v___y_946_, sizeof(void*)*14);
v_cancelTk_x3f_1008_ = lean_ctor_get(v___y_946_, 12);
v_suppressElabErrors_1009_ = lean_ctor_get_uint8(v___y_946_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1010_ = lean_ctor_get(v___y_946_, 13);
v___x_1011_ = l_Lean_Meta_Context_config(v___y_944_);
v_foApprox_1012_ = lean_ctor_get_uint8(v___x_1011_, 0);
v_ctxApprox_1013_ = lean_ctor_get_uint8(v___x_1011_, 1);
v_quasiPatternApprox_1014_ = lean_ctor_get_uint8(v___x_1011_, 2);
v_constApprox_1015_ = lean_ctor_get_uint8(v___x_1011_, 3);
v_isDefEqStuckEx_1016_ = lean_ctor_get_uint8(v___x_1011_, 4);
v_unificationHints_1017_ = lean_ctor_get_uint8(v___x_1011_, 5);
v_proofIrrelevance_1018_ = lean_ctor_get_uint8(v___x_1011_, 6);
v_assignSyntheticOpaque_1019_ = lean_ctor_get_uint8(v___x_1011_, 7);
v_offsetCnstrs_1020_ = lean_ctor_get_uint8(v___x_1011_, 8);
v_etaStruct_1021_ = lean_ctor_get_uint8(v___x_1011_, 10);
v_univApprox_1022_ = lean_ctor_get_uint8(v___x_1011_, 11);
v_iota_1023_ = lean_ctor_get_uint8(v___x_1011_, 12);
v_beta_1024_ = lean_ctor_get_uint8(v___x_1011_, 13);
v_proj_1025_ = lean_ctor_get_uint8(v___x_1011_, 14);
v_zeta_1026_ = lean_ctor_get_uint8(v___x_1011_, 15);
v_zetaDelta_1027_ = lean_ctor_get_uint8(v___x_1011_, 16);
v_zetaUnused_1028_ = lean_ctor_get_uint8(v___x_1011_, 17);
v_zetaHave_1029_ = lean_ctor_get_uint8(v___x_1011_, 18);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1031_ = v___x_1011_;
v_isShared_1032_ = v_isSharedCheck_1067_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v___x_1011_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1067_;
goto v_resetjp_1030_;
}
v___jp_952_:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__0));
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
v___jp_957_:
{
lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_992_; 
v___x_958_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mv_939_, v___y_945_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_992_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_992_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_992_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v___x_963_; 
v___x_963_ = lean_unbox(v_a_959_);
lean_dec(v_a_959_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v_mv_939_);
v___x_964_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__1));
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_964_);
v___x_966_ = v___x_961_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
else
{
lean_object* v___x_968_; lean_object* v_a_969_; 
lean_del_object(v___x_961_);
v___x_968_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__2___redArg(v_mv_939_, v___y_945_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
if (lean_obj_tag(v_a_969_) == 1)
{
lean_object* v_val_970_; lean_object* v___x_971_; 
v_val_970_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_val_970_);
lean_dec_ref_known(v_a_969_, 1);
v___x_971_ = l_Lean_Meta_Sym_unfoldReducible(v_val_970_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_972_, v___y_943_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mv_939_, v_a_974_, v___y_945_);
lean_dec_ref(v___x_975_);
goto v___jp_952_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_mv_939_);
v_a_976_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_973_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec(v_mv_939_);
v_a_984_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_971_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_971_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_dec(v_a_969_);
lean_dec(v_mv_939_);
goto v___jp_952_;
}
}
}
}
v_resetjp_1030_:
{
uint8_t v_trackZetaDelta_1033_; lean_object* v_zetaDeltaSet_1034_; lean_object* v_lctx_1035_; lean_object* v_localInstances_1036_; lean_object* v_defEqCtx_x3f_1037_; lean_object* v_synthPendingDepth_1038_; lean_object* v_canUnfold_x3f_1039_; uint8_t v_univApprox_1040_; uint8_t v_inTypeClassResolution_1041_; uint8_t v_cacheInferType_1042_; uint8_t v___x_1043_; lean_object* v_config_1045_; 
v_trackZetaDelta_1033_ = lean_ctor_get_uint8(v___y_944_, sizeof(void*)*7);
v_zetaDeltaSet_1034_ = lean_ctor_get(v___y_944_, 1);
v_lctx_1035_ = lean_ctor_get(v___y_944_, 2);
v_localInstances_1036_ = lean_ctor_get(v___y_944_, 3);
v_defEqCtx_x3f_1037_ = lean_ctor_get(v___y_944_, 4);
v_synthPendingDepth_1038_ = lean_ctor_get(v___y_944_, 5);
v_canUnfold_x3f_1039_ = lean_ctor_get(v___y_944_, 6);
v_univApprox_1040_ = lean_ctor_get_uint8(v___y_944_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1041_ = lean_ctor_get_uint8(v___y_944_, sizeof(void*)*7 + 2);
v_cacheInferType_1042_ = lean_ctor_get_uint8(v___y_944_, sizeof(void*)*7 + 3);
v___x_1043_ = 1;
if (v_isShared_1032_ == 0)
{
v_config_1045_ = v___x_1031_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 0, v_foApprox_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 1, v_ctxApprox_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 2, v_quasiPatternApprox_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 3, v_constApprox_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 4, v_isDefEqStuckEx_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 5, v_unificationHints_1017_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 6, v_proofIrrelevance_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 7, v_assignSyntheticOpaque_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 8, v_offsetCnstrs_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 10, v_etaStruct_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 11, v_univApprox_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 12, v_iota_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 13, v_beta_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 14, v_proj_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 15, v_zeta_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 16, v_zetaDelta_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 17, v_zetaUnused_1028_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, 18, v_zetaHave_1029_);
v_config_1045_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
uint64_t v___x_1046_; uint64_t v___x_1047_; uint64_t v___x_1048_; lean_object* v___x_1049_; lean_object* v_ref_1050_; lean_object* v___x_1051_; uint64_t v___x_1052_; uint64_t v___x_1053_; uint64_t v_key_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_ctor_set_uint8(v_config_1045_, 9, v___x_1043_);
v___x_1046_ = l_Lean_Meta_Context_configKey(v___y_944_);
v___x_1047_ = 3ULL;
v___x_1048_ = lean_uint64_shift_right(v___x_1046_, v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5));
v_ref_1050_ = l_Lean_replaceRef(v_val_940_, v_ref_1000_);
lean_inc_ref(v_inheritedTraceOptions_1010_);
lean_inc(v_cancelTk_x3f_1008_);
lean_inc(v_currMacroScope_1006_);
lean_inc(v_quotContext_1005_);
lean_inc(v_maxHeartbeats_1004_);
lean_inc(v_initHeartbeats_1003_);
lean_inc(v_openDecls_1002_);
lean_inc(v_currNamespace_1001_);
lean_inc(v_maxRecDepth_999_);
lean_inc(v_currRecDepth_998_);
lean_inc_ref(v_options_997_);
lean_inc_ref(v_fileMap_996_);
lean_inc_ref(v_fileName_995_);
v___x_1051_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1051_, 0, v_fileName_995_);
lean_ctor_set(v___x_1051_, 1, v_fileMap_996_);
lean_ctor_set(v___x_1051_, 2, v_options_997_);
lean_ctor_set(v___x_1051_, 3, v_currRecDepth_998_);
lean_ctor_set(v___x_1051_, 4, v_maxRecDepth_999_);
lean_ctor_set(v___x_1051_, 5, v_ref_1050_);
lean_ctor_set(v___x_1051_, 6, v_currNamespace_1001_);
lean_ctor_set(v___x_1051_, 7, v_openDecls_1002_);
lean_ctor_set(v___x_1051_, 8, v_initHeartbeats_1003_);
lean_ctor_set(v___x_1051_, 9, v_maxHeartbeats_1004_);
lean_ctor_set(v___x_1051_, 10, v_quotContext_1005_);
lean_ctor_set(v___x_1051_, 11, v_currMacroScope_1006_);
lean_ctor_set(v___x_1051_, 12, v_cancelTk_x3f_1008_);
lean_ctor_set(v___x_1051_, 13, v_inheritedTraceOptions_1010_);
lean_ctor_set_uint8(v___x_1051_, sizeof(void*)*14, v_diag_1007_);
lean_ctor_set_uint8(v___x_1051_, sizeof(void*)*14 + 1, v_suppressElabErrors_1009_);
v___x_1052_ = lean_uint64_shift_left(v___x_1048_, v___x_1047_);
v___x_1053_ = lean_uint64_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___closed__2);
v_key_1054_ = lean_uint64_lor(v___x_1052_, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1055_, 0, v_config_1045_);
lean_ctor_set_uint64(v___x_1055_, sizeof(void*)*1, v_key_1054_);
lean_inc(v_canUnfold_x3f_1039_);
lean_inc(v_synthPendingDepth_1038_);
lean_inc(v_defEqCtx_x3f_1037_);
lean_inc_ref(v_localInstances_1036_);
lean_inc_ref(v_lctx_1035_);
lean_inc(v_zetaDeltaSet_1034_);
v___x_1056_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v_zetaDeltaSet_1034_);
lean_ctor_set(v___x_1056_, 2, v_lctx_1035_);
lean_ctor_set(v___x_1056_, 3, v_localInstances_1036_);
lean_ctor_set(v___x_1056_, 4, v_defEqCtx_x3f_1037_);
lean_ctor_set(v___x_1056_, 5, v_synthPendingDepth_1038_);
lean_ctor_set(v___x_1056_, 6, v_canUnfold_x3f_1039_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*7, v_trackZetaDelta_1033_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*7 + 1, v_univApprox_1040_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1041_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*7 + 3, v_cacheInferType_1042_);
lean_inc(v_mv_939_);
v___x_1057_ = l_Lean_Elab_runTactic(v_mv_939_, v_tac_941_, v___x_994_, v___x_1049_, v___x_1056_, v___y_945_, v___x_1051_, v___y_947_);
lean_dec_ref_known(v___x_1051_, 14);
lean_dec_ref_known(v___x_1056_, 7);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_dec_ref_known(v___x_1057_, 1);
goto v___jp_957_;
}
else
{
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_dec_ref_known(v___x_1057_, 1);
goto v___jp_957_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec(v_mv_939_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1057_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1___boxed(lean_object* v___f_1068_, lean_object* v_mv_1069_, lean_object* v_val_1070_, lean_object* v_tac_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_1068_, v_mv_1069_, v_val_1070_, v_tac_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_val_1070_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(lean_object* v_a_1080_, lean_object* v_x_1081_){
_start:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_box(0);
return v___x_1082_;
}
else
{
lean_object* v_key_1083_; lean_object* v_value_1084_; lean_object* v_tail_1085_; uint8_t v___x_1086_; 
v_key_1083_ = lean_ctor_get(v_x_1081_, 0);
v_value_1084_ = lean_ctor_get(v_x_1081_, 1);
v_tail_1085_ = lean_ctor_get(v_x_1081_, 2);
v___x_1086_ = lean_nat_dec_eq(v_key_1083_, v_a_1080_);
if (v___x_1086_ == 0)
{
v_x_1081_ = v_tail_1085_;
goto _start;
}
else
{
lean_object* v___x_1088_; 
lean_inc(v_value_1084_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_value_1084_);
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_a_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_1089_, v_x_1090_);
lean_dec(v_x_1090_);
lean_dec(v_a_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(lean_object* v_m_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_buckets_1094_; lean_object* v___x_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; uint64_t v___x_1098_; uint64_t v_fold_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_buckets_1094_ = lean_ctor_get(v_m_1092_, 1);
v___x_1095_ = lean_array_get_size(v_buckets_1094_);
v___x_1096_ = lean_uint64_of_nat(v_a_1093_);
v___x_1097_ = 32ULL;
v___x_1098_ = lean_uint64_shift_right(v___x_1096_, v___x_1097_);
v_fold_1099_ = lean_uint64_xor(v___x_1096_, v___x_1098_);
v___x_1100_ = 16ULL;
v___x_1101_ = lean_uint64_shift_right(v_fold_1099_, v___x_1100_);
v___x_1102_ = lean_uint64_xor(v_fold_1099_, v___x_1101_);
v___x_1103_ = lean_uint64_to_usize(v___x_1102_);
v___x_1104_ = lean_usize_of_nat(v___x_1095_);
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_sub(v___x_1104_, v___x_1105_);
v___x_1107_ = lean_usize_land(v___x_1103_, v___x_1106_);
v___x_1108_ = lean_array_uget_borrowed(v_buckets_1094_, v___x_1107_);
v___x_1109_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_1093_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg___boxed(lean_object* v_m_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_m_1110_);
return v_res_1112_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20(void){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Array_mkArray0(lean_box(0));
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(lean_object* v_invariantAlts_1175_, lean_object* v_n_1176_, lean_object* v_mv_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___y_1186_; uint8_t v___y_1187_; lean_object* v___y_1192_; lean_object* v___x_1205_; 
v___x_1205_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_invariantAlts_1175_, v_n_1176_);
if (lean_obj_tag(v___x_1205_) == 1)
{
lean_object* v_val_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1277_; 
v_val_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1277_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_val_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1277_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___f_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___f_1210_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2));
v___x_1211_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__3));
lean_inc(v_val_1206_);
v___x_1212_ = l_Lean_Syntax_isOfKind(v_val_1206_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__5));
lean_inc(v_val_1206_);
v___x_1214_ = l_Lean_Syntax_isOfKind(v_val_1206_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_dec(v_val_1206_);
lean_dec(v_mv_1177_);
v___x_1215_ = lean_box(v___x_1214_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1215_);
v___x_1217_ = v___x_1208_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = l_Lean_Syntax_getArg(v_val_1206_, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__7));
lean_inc(v___x_1220_);
v___x_1222_ = l_Lean_Syntax_isOfKind(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
lean_dec(v___x_1220_);
lean_dec(v_val_1206_);
lean_dec(v_mv_1177_);
v___x_1223_ = lean_box(v___x_1222_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1223_);
v___x_1225_ = v___x_1208_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
else
{
lean_object* v_ref_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_args_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_del_object(v___x_1208_);
v_ref_1227_ = lean_ctor_get(v_a_1182_, 5);
v___x_1228_ = l_Lean_Syntax_getArg(v___x_1220_, v___x_1219_);
lean_dec(v___x_1220_);
v___x_1229_ = lean_unsigned_to_nat(3u);
v___x_1230_ = l_Lean_Syntax_getArg(v_val_1206_, v___x_1229_);
v_args_1231_ = l_Lean_Syntax_getArgs(v___x_1228_);
lean_dec(v___x_1228_);
v___x_1232_ = l_Lean_SourceInfo_fromRef(v_ref_1227_, v___x_1212_);
v___x_1233_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__9));
v___x_1234_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__10));
lean_inc_n(v___x_1232_, 11);
v___x_1235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1232_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__12));
v___x_1237_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__14));
v___x_1238_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__16));
v___x_1239_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__18));
v___x_1240_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__19));
v___x_1241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1232_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20, &l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__20);
v___x_1243_ = l_Array_append___redArg(v___x_1242_, v_args_1231_);
lean_dec_ref(v_args_1231_);
v___x_1244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1232_);
lean_ctor_set(v___x_1244_, 1, v___x_1238_);
lean_ctor_set(v___x_1244_, 2, v___x_1243_);
v___x_1245_ = l_Lean_Syntax_node2(v___x_1232_, v___x_1239_, v___x_1241_, v___x_1244_);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__21));
v___x_1247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1232_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22));
v___x_1249_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23));
v___x_1250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1232_);
lean_ctor_set(v___x_1250_, 1, v___x_1248_);
v___x_1251_ = l_Lean_Syntax_node2(v___x_1232_, v___x_1249_, v___x_1250_, v___x_1230_);
v___x_1252_ = l_Lean_Syntax_node3(v___x_1232_, v___x_1238_, v___x_1245_, v___x_1247_, v___x_1251_);
v___x_1253_ = l_Lean_Syntax_node1(v___x_1232_, v___x_1237_, v___x_1252_);
v___x_1254_ = l_Lean_Syntax_node1(v___x_1232_, v___x_1236_, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__24));
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1232_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = l_Lean_Syntax_node3(v___x_1232_, v___x_1233_, v___x_1235_, v___x_1254_, v___x_1256_);
v___x_1258_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_1210_, v_mv_1177_, v_val_1206_, v___x_1257_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_val_1206_);
v___y_1192_ = v___x_1258_;
goto v___jp_1191_;
}
}
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = l_Lean_Syntax_getArg(v_val_1206_, v___x_1259_);
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__26));
v___x_1262_ = l_Lean_Syntax_isOfKind(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
lean_dec(v_val_1206_);
lean_dec(v_mv_1177_);
v___x_1263_ = lean_box(v___x_1262_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1263_);
v___x_1265_ = v___x_1208_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
lean_object* v_ref_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_del_object(v___x_1208_);
v_ref_1267_ = lean_ctor_get(v_a_1182_, 5);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = l_Lean_Syntax_getArg(v_val_1206_, v___x_1268_);
v___x_1270_ = 0;
v___x_1271_ = l_Lean_SourceInfo_fromRef(v_ref_1267_, v___x_1270_);
v___x_1272_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__22));
v___x_1273_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___closed__23));
lean_inc(v___x_1271_);
v___x_1274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1271_);
lean_ctor_set(v___x_1274_, 1, v___x_1272_);
v___x_1275_ = l_Lean_Syntax_node2(v___x_1271_, v___x_1273_, v___x_1274_, v___x_1269_);
v___x_1276_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___lam__1(v___f_1210_, v_mv_1177_, v_val_1206_, v___x_1275_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_val_1206_);
v___y_1192_ = v___x_1276_;
goto v___jp_1191_;
}
}
}
}
else
{
uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v___x_1205_);
lean_dec(v_mv_1177_);
v___x_1278_ = 0;
v___x_1279_ = lean_box(v___x_1278_);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
v___jp_1185_:
{
if (v___y_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v___y_1186_);
v___x_1188_ = lean_box(v___y_1187_);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___y_1186_);
return v___x_1190_;
}
}
v___jp_1191_:
{
if (lean_obj_tag(v___y_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
v_a_1193_ = lean_ctor_get(v___y_1192_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___y_1192_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1195_ = v___y_1192_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___y_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_a_1197_; lean_object* v___x_1199_; 
v_a_1197_ = lean_ctor_get(v_a_1193_, 0);
lean_inc(v_a_1197_);
lean_dec(v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v_a_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; uint8_t v___x_1203_; 
v_a_1202_ = lean_ctor_get(v___y_1192_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___y_1192_, 1);
v___x_1203_ = l_Lean_Exception_isInterrupt(v_a_1202_);
if (v___x_1203_ == 0)
{
uint8_t v___x_1204_; 
lean_inc(v_a_1202_);
v___x_1204_ = l_Lean_Exception_isRuntime(v_a_1202_);
v___y_1186_ = v_a_1202_;
v___y_1187_ = v___x_1204_;
goto v___jp_1185_;
}
else
{
v___y_1186_ = v_a_1202_;
v___y_1187_ = v___x_1203_;
goto v___jp_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant___boxed(lean_object* v_invariantAlts_1281_, lean_object* v_n_1282_, lean_object* v_mv_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_invariantAlts_1281_, v_n_1282_, v_mv_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_n_1282_);
lean_dec_ref(v_invariantAlts_1281_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(lean_object* v_00_u03b2_1292_, lean_object* v_m_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___redArg(v_m_1293_, v_a_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0___boxed(lean_object* v_00_u03b2_1296_, lean_object* v_m_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0(v_00_u03b2_1296_, v_m_1297_, v_a_1298_);
lean_dec(v_a_1298_);
lean_dec_ref(v_m_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(lean_object* v_mvarId_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___redArg(v_mvarId_1300_, v___y_1304_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1___boxed(lean_object* v_mvarId_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1(v_mvarId_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_mvarId_1309_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(lean_object* v_mvarId_1318_, lean_object* v_val_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___redArg(v_mvarId_1318_, v_val_1319_, v___y_1323_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3___boxed(lean_object* v_mvarId_1328_, lean_object* v_val_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3(v_mvarId_1328_, v_val_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(lean_object* v_00_u03b2_1338_, lean_object* v_a_1339_, lean_object* v_x_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___redArg(v_a_1339_, v_x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1342_, lean_object* v_a_1343_, lean_object* v_x_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__0_spec__0(v_00_u03b2_1342_, v_a_1343_, v_x_1344_);
lean_dec(v_x_1344_);
lean_dec(v_a_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(lean_object* v_00_u03b2_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
uint8_t v___x_1349_; 
v___x_1349_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_x_1347_, v_x_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1350_, lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2(v_00_u03b2_1350_, v_x_1351_, v_x_1352_);
lean_dec(v_x_1352_);
lean_dec_ref(v_x_1351_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5(lean_object* v_00_u03b2_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5___redArg(v_x_1356_, v_x_1357_, v_x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1360_, lean_object* v_x_1361_, size_t v_x_1362_, lean_object* v_x_1363_){
_start:
{
uint8_t v___x_1364_; 
v___x_1364_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___redArg(v_x_1361_, v_x_1362_, v_x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
size_t v_x_18672__boxed_1369_; uint8_t v_res_1370_; lean_object* v_r_1371_; 
v_x_18672__boxed_1369_ = lean_unbox_usize(v_x_1367_);
lean_dec(v_x_1367_);
v_res_1370_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4(v_00_u03b2_1365_, v_x_1366_, v_x_18672__boxed_1369_, v_x_1368_);
lean_dec(v_x_1368_);
lean_dec_ref(v_x_1366_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1372_, lean_object* v_x_1373_, size_t v_x_1374_, size_t v_x_1375_, lean_object* v_x_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___redArg(v_x_1373_, v_x_1374_, v_x_1375_, v_x_1376_, v_x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_){
_start:
{
size_t v_x_18683__boxed_1385_; size_t v_x_18684__boxed_1386_; lean_object* v_res_1387_; 
v_x_18683__boxed_1385_ = lean_unbox_usize(v_x_1381_);
lean_dec(v_x_1381_);
v_x_18684__boxed_1386_ = lean_unbox_usize(v_x_1382_);
lean_dec(v_x_1382_);
v_res_1387_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7(v_00_u03b2_1379_, v_x_1380_, v_x_18683__boxed_1385_, v_x_18684__boxed_1386_, v_x_1383_, v_x_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_1388_, lean_object* v_keys_1389_, lean_object* v_vals_1390_, lean_object* v_heq_1391_, lean_object* v_i_1392_, lean_object* v_k_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___redArg(v_keys_1389_, v_i_1392_, v_k_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b2_1395_, lean_object* v_keys_1396_, lean_object* v_vals_1397_, lean_object* v_heq_1398_, lean_object* v_i_1399_, lean_object* v_k_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2_spec__4_spec__6(v_00_u03b2_1395_, v_keys_1396_, v_vals_1397_, v_heq_1398_, v_i_1399_, v_k_1400_);
lean_dec(v_k_1400_);
lean_dec_ref(v_vals_1397_);
lean_dec_ref(v_keys_1396_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_1403_, lean_object* v_n_1404_, lean_object* v_k_1405_, lean_object* v_v_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9___redArg(v_n_1404_, v_k_1405_, v_v_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(lean_object* v_00_u03b2_1408_, size_t v_depth_1409_, lean_object* v_keys_1410_, lean_object* v_vals_1411_, lean_object* v_heq_1412_, lean_object* v_i_1413_, lean_object* v_entries_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___redArg(v_depth_1409_, v_keys_1410_, v_vals_1411_, v_i_1413_, v_entries_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1416_, lean_object* v_depth_1417_, lean_object* v_keys_1418_, lean_object* v_vals_1419_, lean_object* v_heq_1420_, lean_object* v_i_1421_, lean_object* v_entries_1422_){
_start:
{
size_t v_depth_boxed_1423_; lean_object* v_res_1424_; 
v_depth_boxed_1423_ = lean_unbox_usize(v_depth_1417_);
lean_dec(v_depth_1417_);
v_res_1424_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__10(v_00_u03b2_1416_, v_depth_boxed_1423_, v_keys_1418_, v_vals_1419_, v_heq_1420_, v_i_1421_, v_entries_1422_);
lean_dec_ref(v_vals_1419_);
lean_dec_ref(v_keys_1418_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_00_u03b2_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_x_1426_, v_x_1427_, v_x_1428_, v_x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_1431_, lean_object* v_x_1432_){
_start:
{
if (lean_obj_tag(v_x_1432_) == 0)
{
uint8_t v___x_1433_; 
v___x_1433_ = 0;
return v___x_1433_;
}
else
{
lean_object* v_key_1434_; lean_object* v_tail_1435_; uint8_t v___x_1436_; 
v_key_1434_ = lean_ctor_get(v_x_1432_, 0);
v_tail_1435_ = lean_ctor_get(v_x_1432_, 2);
v___x_1436_ = lean_nat_dec_eq(v_key_1434_, v_a_1431_);
if (v___x_1436_ == 0)
{
v_x_1432_ = v_tail_1435_;
goto _start;
}
else
{
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_1438_, lean_object* v_x_1439_){
_start:
{
uint8_t v_res_1440_; lean_object* v_r_1441_; 
v_res_1440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1438_, v_x_1439_);
lean_dec(v_x_1439_);
lean_dec(v_a_1438_);
v_r_1441_ = lean_box(v_res_1440_);
return v_r_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
if (lean_obj_tag(v_x_1443_) == 0)
{
return v_x_1442_;
}
else
{
lean_object* v_key_1444_; lean_object* v_value_1445_; lean_object* v_tail_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1469_; 
v_key_1444_ = lean_ctor_get(v_x_1443_, 0);
v_value_1445_ = lean_ctor_get(v_x_1443_, 1);
v_tail_1446_ = lean_ctor_get(v_x_1443_, 2);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_x_1443_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1448_ = v_x_1443_;
v_isShared_1449_ = v_isSharedCheck_1469_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_tail_1446_);
lean_inc(v_value_1445_);
lean_inc(v_key_1444_);
lean_dec(v_x_1443_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1469_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; uint64_t v___x_1451_; uint64_t v___x_1452_; uint64_t v___x_1453_; uint64_t v_fold_1454_; uint64_t v___x_1455_; uint64_t v___x_1456_; uint64_t v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1450_ = lean_array_get_size(v_x_1442_);
v___x_1451_ = lean_uint64_of_nat(v_key_1444_);
v___x_1452_ = 32ULL;
v___x_1453_ = lean_uint64_shift_right(v___x_1451_, v___x_1452_);
v_fold_1454_ = lean_uint64_xor(v___x_1451_, v___x_1453_);
v___x_1455_ = 16ULL;
v___x_1456_ = lean_uint64_shift_right(v_fold_1454_, v___x_1455_);
v___x_1457_ = lean_uint64_xor(v_fold_1454_, v___x_1456_);
v___x_1458_ = lean_uint64_to_usize(v___x_1457_);
v___x_1459_ = lean_usize_of_nat(v___x_1450_);
v___x_1460_ = ((size_t)1ULL);
v___x_1461_ = lean_usize_sub(v___x_1459_, v___x_1460_);
v___x_1462_ = lean_usize_land(v___x_1458_, v___x_1461_);
v___x_1463_ = lean_array_uget_borrowed(v_x_1442_, v___x_1462_);
lean_inc(v___x_1463_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 2, v___x_1463_);
v___x_1465_ = v___x_1448_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_key_1444_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_value_1445_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_array_uset(v_x_1442_, v___x_1462_, v___x_1465_);
v_x_1442_ = v___x_1466_;
v_x_1443_ = v_tail_1446_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1470_, lean_object* v_source_1471_, lean_object* v_target_1472_){
_start:
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1473_ = lean_array_get_size(v_source_1471_);
v___x_1474_ = lean_nat_dec_lt(v_i_1470_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_dec_ref(v_source_1471_);
lean_dec(v_i_1470_);
return v_target_1472_;
}
else
{
lean_object* v_es_1475_; lean_object* v___x_1476_; lean_object* v_source_1477_; lean_object* v_target_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_es_1475_ = lean_array_fget(v_source_1471_, v_i_1470_);
v___x_1476_ = lean_box(0);
v_source_1477_ = lean_array_fset(v_source_1471_, v_i_1470_, v___x_1476_);
v_target_1478_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1472_, v_es_1475_);
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = lean_nat_add(v_i_1470_, v___x_1479_);
lean_dec(v_i_1470_);
v_i_1470_ = v___x_1480_;
v_source_1471_ = v_source_1477_;
v_target_1472_ = v_target_1478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v_nbuckets_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1483_ = lean_array_get_size(v_data_1482_);
v___x_1484_ = lean_unsigned_to_nat(2u);
v_nbuckets_1485_ = lean_nat_mul(v___x_1483_, v___x_1484_);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_mk_array(v_nbuckets_1485_, v___x_1487_);
v___x_1489_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_1486_, v_data_1482_, v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_1490_, lean_object* v_a_1491_, lean_object* v_b_1492_){
_start:
{
lean_object* v_size_1493_; lean_object* v_buckets_1494_; lean_object* v___x_1495_; uint64_t v___x_1496_; uint64_t v___x_1497_; uint64_t v___x_1498_; uint64_t v_fold_1499_; uint64_t v___x_1500_; uint64_t v___x_1501_; uint64_t v___x_1502_; size_t v___x_1503_; size_t v___x_1504_; size_t v___x_1505_; size_t v___x_1506_; size_t v___x_1507_; lean_object* v_bkt_1508_; uint8_t v___x_1509_; 
v_size_1493_ = lean_ctor_get(v_m_1490_, 0);
v_buckets_1494_ = lean_ctor_get(v_m_1490_, 1);
v___x_1495_ = lean_array_get_size(v_buckets_1494_);
v___x_1496_ = lean_uint64_of_nat(v_a_1491_);
v___x_1497_ = 32ULL;
v___x_1498_ = lean_uint64_shift_right(v___x_1496_, v___x_1497_);
v_fold_1499_ = lean_uint64_xor(v___x_1496_, v___x_1498_);
v___x_1500_ = 16ULL;
v___x_1501_ = lean_uint64_shift_right(v_fold_1499_, v___x_1500_);
v___x_1502_ = lean_uint64_xor(v_fold_1499_, v___x_1501_);
v___x_1503_ = lean_uint64_to_usize(v___x_1502_);
v___x_1504_ = lean_usize_of_nat(v___x_1495_);
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_sub(v___x_1504_, v___x_1505_);
v___x_1507_ = lean_usize_land(v___x_1503_, v___x_1506_);
v_bkt_1508_ = lean_array_uget_borrowed(v_buckets_1494_, v___x_1507_);
v___x_1509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1491_, v_bkt_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1530_; 
lean_inc_ref(v_buckets_1494_);
lean_inc(v_size_1493_);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_m_1490_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; lean_object* v_unused_1532_; 
v_unused_1531_ = lean_ctor_get(v_m_1490_, 1);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_m_1490_, 0);
lean_dec(v_unused_1532_);
v___x_1511_ = v_m_1490_;
v_isShared_1512_ = v_isSharedCheck_1530_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v_m_1490_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1530_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v_size_x27_1514_; lean_object* v___x_1515_; lean_object* v_buckets_x27_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1513_ = lean_unsigned_to_nat(1u);
v_size_x27_1514_ = lean_nat_add(v_size_1493_, v___x_1513_);
lean_dec(v_size_1493_);
lean_inc(v_bkt_1508_);
v___x_1515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1515_, 0, v_a_1491_);
lean_ctor_set(v___x_1515_, 1, v_b_1492_);
lean_ctor_set(v___x_1515_, 2, v_bkt_1508_);
v_buckets_x27_1516_ = lean_array_uset(v_buckets_1494_, v___x_1507_, v___x_1515_);
v___x_1517_ = lean_unsigned_to_nat(4u);
v___x_1518_ = lean_nat_mul(v_size_x27_1514_, v___x_1517_);
v___x_1519_ = lean_unsigned_to_nat(3u);
v___x_1520_ = lean_nat_div(v___x_1518_, v___x_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_array_get_size(v_buckets_x27_1516_);
v___x_1522_ = lean_nat_dec_le(v___x_1520_, v___x_1521_);
lean_dec(v___x_1520_);
if (v___x_1522_ == 0)
{
lean_object* v_val_1523_; lean_object* v___x_1525_; 
v_val_1523_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_1516_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v_val_1523_);
lean_ctor_set(v___x_1511_, 0, v_size_x27_1514_);
v___x_1525_ = v___x_1511_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_size_x27_1514_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_val_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
else
{
lean_object* v___x_1528_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v_buckets_x27_1516_);
lean_ctor_set(v___x_1511_, 0, v_size_x27_1514_);
v___x_1528_ = v___x_1511_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_size_x27_1514_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_buckets_x27_1516_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_dec(v_b_1492_);
lean_dec(v_a_1491_);
return v_m_1490_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_1533_, lean_object* v_as_x27_1534_, lean_object* v_b_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
if (lean_obj_tag(v_as_x27_1534_) == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref(v___x_1533_);
v___x_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1545_, 0, v_b_1535_);
return v___x_1545_;
}
else
{
lean_object* v_head_1546_; lean_object* v_tail_1547_; lean_object* v___x_1548_; 
v_head_1546_ = lean_ctor_get(v_as_x27_1534_, 0);
v_tail_1547_ = lean_ctor_get(v_as_x27_1534_, 1);
lean_inc(v_head_1546_);
v___x_1548_ = l_Lean_MVarId_getType(v_head_1546_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; uint8_t v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
lean_inc_ref(v___x_1533_);
v___x_1550_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_1533_, v_a_1549_);
lean_dec(v_a_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_inc(v_head_1546_);
v___x_1551_ = lean_array_push(v_b_1535_, v_head_1546_);
v_as_x27_1534_ = v_tail_1547_;
v_b_1535_ = v___x_1551_;
goto _start;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v_specBackwardRuleCache_1555_; lean_object* v_splitBackwardRuleCache_1556_; lean_object* v_invariants_1557_; lean_object* v_vcs_1558_; lean_object* v_simpState_1559_; lean_object* v_fuel_1560_; lean_object* v_inlineHandledInvariants_1561_; uint8_t v_preTacFailed_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1618_; 
v___x_1553_ = lean_st_ref_get(v___y_1537_);
v___x_1554_ = lean_st_ref_take(v___y_1537_);
v_specBackwardRuleCache_1555_ = lean_ctor_get(v___x_1554_, 0);
v_splitBackwardRuleCache_1556_ = lean_ctor_get(v___x_1554_, 1);
v_invariants_1557_ = lean_ctor_get(v___x_1554_, 2);
v_vcs_1558_ = lean_ctor_get(v___x_1554_, 3);
v_simpState_1559_ = lean_ctor_get(v___x_1554_, 4);
v_fuel_1560_ = lean_ctor_get(v___x_1554_, 5);
v_inlineHandledInvariants_1561_ = lean_ctor_get(v___x_1554_, 6);
v_preTacFailed_1562_ = lean_ctor_get_uint8(v___x_1554_, sizeof(void*)*7);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1564_ = v___x_1554_;
v_isShared_1565_ = v_isSharedCheck_1618_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_inlineHandledInvariants_1561_);
lean_inc(v_fuel_1560_);
lean_inc(v_simpState_1559_);
lean_inc(v_vcs_1558_);
lean_inc(v_invariants_1557_);
lean_inc(v_splitBackwardRuleCache_1556_);
lean_inc(v_specBackwardRuleCache_1555_);
lean_dec(v___x_1554_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1618_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; lean_object* v___x_1568_; 
lean_inc(v_head_1546_);
v___x_1566_ = lean_array_push(v_invariants_1557_, v_head_1546_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 2, v___x_1566_);
v___x_1568_ = v___x_1564_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_specBackwardRuleCache_1555_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_splitBackwardRuleCache_1556_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_vcs_1558_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_simpState_1559_);
lean_ctor_set(v_reuseFailAlloc_1617_, 5, v_fuel_1560_);
lean_ctor_set(v_reuseFailAlloc_1617_, 6, v_inlineHandledInvariants_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1617_, sizeof(void*)*7, v_preTacFailed_1562_);
v___x_1568_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; lean_object* v_invariants_1570_; lean_object* v_invariantAlts_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1569_ = lean_st_ref_set(v___y_1537_, v___x_1568_);
v_invariants_1570_ = lean_ctor_get(v___x_1553_, 2);
lean_inc_ref(v_invariants_1570_);
lean_dec(v___x_1553_);
v_invariantAlts_1571_ = lean_ctor_get(v___y_1536_, 18);
v___x_1572_ = lean_array_get_size(v_invariants_1570_);
lean_dec_ref(v_invariants_1570_);
v___x_1573_ = lean_unsigned_to_nat(1u);
v___x_1574_ = lean_nat_add(v___x_1572_, v___x_1573_);
lean_inc(v_head_1546_);
v___x_1575_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_invariantAlts_1571_, v___x_1574_, v_head_1546_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; uint8_t v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
v___x_1577_ = lean_unbox(v_a_1576_);
lean_dec(v_a_1576_);
if (v___x_1577_ == 0)
{
uint8_t v___x_1578_; lean_object* v___x_1579_; 
lean_dec(v___x_1574_);
v___x_1578_ = 2;
lean_inc(v_head_1546_);
v___x_1579_ = l_Lean_MVarId_setKind___redArg(v_head_1546_, v___x_1578_, v___y_1541_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec_ref_known(v___x_1579_, 1);
v_as_x27_1534_ = v_tail_1547_;
goto _start;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_b_1535_);
lean_dec_ref(v___x_1533_);
v_a_1581_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1579_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1579_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v___x_1589_; lean_object* v_specBackwardRuleCache_1590_; lean_object* v_splitBackwardRuleCache_1591_; lean_object* v_invariants_1592_; lean_object* v_vcs_1593_; lean_object* v_simpState_1594_; lean_object* v_fuel_1595_; lean_object* v_inlineHandledInvariants_1596_; uint8_t v_preTacFailed_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1608_; 
v___x_1589_ = lean_st_ref_take(v___y_1537_);
v_specBackwardRuleCache_1590_ = lean_ctor_get(v___x_1589_, 0);
v_splitBackwardRuleCache_1591_ = lean_ctor_get(v___x_1589_, 1);
v_invariants_1592_ = lean_ctor_get(v___x_1589_, 2);
v_vcs_1593_ = lean_ctor_get(v___x_1589_, 3);
v_simpState_1594_ = lean_ctor_get(v___x_1589_, 4);
v_fuel_1595_ = lean_ctor_get(v___x_1589_, 5);
v_inlineHandledInvariants_1596_ = lean_ctor_get(v___x_1589_, 6);
v_preTacFailed_1597_ = lean_ctor_get_uint8(v___x_1589_, sizeof(void*)*7);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1599_ = v___x_1589_;
v_isShared_1600_ = v_isSharedCheck_1608_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_inlineHandledInvariants_1596_);
lean_inc(v_fuel_1595_);
lean_inc(v_simpState_1594_);
lean_inc(v_vcs_1593_);
lean_inc(v_invariants_1592_);
lean_inc(v_splitBackwardRuleCache_1591_);
lean_inc(v_specBackwardRuleCache_1590_);
lean_dec(v___x_1589_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1608_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1601_ = lean_box(0);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_1596_, v___x_1574_, v___x_1601_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 6, v___x_1602_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_specBackwardRuleCache_1590_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_splitBackwardRuleCache_1591_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_invariants_1592_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_vcs_1593_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_simpState_1594_);
lean_ctor_set(v_reuseFailAlloc_1607_, 5, v_fuel_1595_);
lean_ctor_set(v_reuseFailAlloc_1607_, 6, v___x_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1607_, sizeof(void*)*7, v_preTacFailed_1597_);
v___x_1604_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_st_ref_set(v___y_1537_, v___x_1604_);
v_as_x27_1534_ = v_tail_1547_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v___x_1574_);
lean_dec_ref(v_b_1535_);
lean_dec_ref(v___x_1533_);
v_a_1609_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1575_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1575_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_b_1535_);
lean_dec_ref(v___x_1533_);
v_a_1619_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1548_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1548_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_1627_, lean_object* v_as_x27_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1627_, v_as_x27_1628_, v_b_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v_as_x27_1628_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; lean_object* v_env_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1655_ = lean_st_ref_get(v_a_1653_);
v_env_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc_ref(v_env_1656_);
lean_dec(v___x_1655_);
v___x_1657_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_1658_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_1656_, v_subgoals_1642_, v___x_1657_, v_a_1643_, v_a_1644_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_subgoals_1659_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1673_, lean_object* v_m_1674_, lean_object* v_a_1675_, lean_object* v_b_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1674_, v_a_1675_, v_b_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1678_, lean_object* v_as_1679_, lean_object* v_as_x27_1680_, lean_object* v_b_1681_, lean_object* v_a_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1678_, v_as_x27_1680_, v_b_1681_, v___y_1683_, v___y_1684_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1696_ = _args[0];
lean_object* v_as_1697_ = _args[1];
lean_object* v_as_x27_1698_ = _args[2];
lean_object* v_b_1699_ = _args[3];
lean_object* v_a_1700_ = _args[4];
lean_object* v___y_1701_ = _args[5];
lean_object* v___y_1702_ = _args[6];
lean_object* v___y_1703_ = _args[7];
lean_object* v___y_1704_ = _args[8];
lean_object* v___y_1705_ = _args[9];
lean_object* v___y_1706_ = _args[10];
lean_object* v___y_1707_ = _args[11];
lean_object* v___y_1708_ = _args[12];
lean_object* v___y_1709_ = _args[13];
lean_object* v___y_1710_ = _args[14];
lean_object* v___y_1711_ = _args[15];
lean_object* v___y_1712_ = _args[16];
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(v___x_1696_, v_as_1697_, v_as_x27_1698_, v_b_1699_, v_a_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v_as_x27_1698_);
lean_dec(v_as_1697_);
return v_res_1713_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1714_, lean_object* v_a_1715_, lean_object* v_x_1716_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1715_, v_x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1718_, lean_object* v_a_1719_, lean_object* v_x_1720_){
_start:
{
uint8_t v_res_1721_; lean_object* v_r_1722_; 
v_res_1721_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1718_, v_a_1719_, v_x_1720_);
lean_dec(v_x_1720_);
lean_dec(v_a_1719_);
v_r_1722_ = lean_box(v_res_1721_);
return v_r_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1723_, lean_object* v_data_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1726_, lean_object* v_i_1727_, lean_object* v_source_1728_, lean_object* v_target_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1727_, v_source_1728_, v_target_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1732_, v_x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(lean_object* v_as_x27_1735_, lean_object* v_b_1736_, lean_object* v___y_1737_){
_start:
{
if (lean_obj_tag(v_as_x27_1735_) == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_b_1736_);
return v___x_1739_;
}
else
{
lean_object* v_head_1740_; lean_object* v_tail_1741_; lean_object* v_mvarId_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; 
v_head_1740_ = lean_ctor_get(v_as_x27_1735_, 0);
v_tail_1741_ = lean_ctor_get(v_as_x27_1735_, 1);
v_mvarId_1742_ = lean_ctor_get(v_head_1740_, 1);
v___x_1743_ = 2;
lean_inc(v_mvarId_1742_);
v___x_1744_ = l_Lean_MVarId_setKind___redArg(v_mvarId_1742_, v___x_1743_, v___y_1737_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref_known(v___x_1744_, 1);
lean_inc(v_head_1740_);
v___x_1745_ = lean_array_push(v_b_1736_, v_head_1740_);
v_as_x27_1735_ = v_tail_1741_;
v_b_1736_ = v___x_1745_;
goto _start;
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v_b_1736_);
v_a_1747_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1744_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1744_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg___boxed(lean_object* v_as_x27_1755_, lean_object* v_b_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(v_as_x27_1755_, v_b_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec(v_as_x27_1755_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(lean_object* v_goal_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v_preTac_1775_; uint8_t v_trivial_1776_; lean_object* v___x_1777_; 
v_preTac_1775_ = lean_ctor_get(v_a_1763_, 17);
v_trivial_1776_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*19);
v___x_1777_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(v_preTac_1775_, v_goal_1762_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v_mvarId_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___closed__0));
if (v_trivial_1776_ == 0)
{
lean_object* v_mvarId_1849_; 
v_mvarId_1849_ = lean_ctor_get(v_a_1778_, 1);
lean_inc(v_mvarId_1849_);
v_mvarId_1781_ = v_mvarId_1849_;
v___y_1782_ = v_a_1763_;
v___y_1783_ = v_a_1764_;
v___y_1784_ = v_a_1765_;
v___y_1785_ = v_a_1766_;
v___y_1786_ = v_a_1767_;
v___y_1787_ = v_a_1768_;
v___y_1788_ = v_a_1769_;
v___y_1789_ = v_a_1770_;
v___y_1790_ = v_a_1771_;
v___y_1791_ = v_a_1772_;
v___y_1792_ = v_a_1773_;
goto v___jp_1780_;
}
else
{
lean_object* v_mvarId_1850_; lean_object* v___x_1851_; 
v_mvarId_1850_ = lean_ctor_get(v_a_1778_, 1);
lean_inc(v_mvarId_1850_);
v___x_1851_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(v_mvarId_1850_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1861_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
if (lean_obj_tag(v_a_1852_) == 1)
{
lean_object* v_val_1856_; 
lean_del_object(v___x_1854_);
v_val_1856_ = lean_ctor_get(v_a_1852_, 0);
lean_inc(v_val_1856_);
lean_dec_ref_known(v_a_1852_, 1);
v_mvarId_1781_ = v_val_1856_;
v___y_1782_ = v_a_1763_;
v___y_1783_ = v_a_1764_;
v___y_1784_ = v_a_1765_;
v___y_1785_ = v_a_1766_;
v___y_1786_ = v_a_1767_;
v___y_1787_ = v_a_1768_;
v___y_1788_ = v_a_1769_;
v___y_1789_ = v_a_1770_;
v___y_1790_ = v_a_1771_;
v___y_1791_ = v_a_1772_;
v___y_1792_ = v_a_1773_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec(v_a_1852_);
lean_dec(v_a_1778_);
v___x_1857_ = lean_box(0);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec(v_a_1778_);
v_a_1862_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1851_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1851_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
v___jp_1780_:
{
lean_object* v_toGoalState_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1847_; 
v_toGoalState_1793_ = lean_ctor_get(v_a_1778_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_a_1778_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v_a_1778_, 1);
lean_dec(v_unused_1848_);
v___x_1795_ = v_a_1778_;
v_isShared_1796_ = v_isSharedCheck_1847_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_toGoalState_1793_);
lean_dec(v_a_1778_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1847_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v_preTac_1797_; lean_object* v___x_1799_; 
v_preTac_1797_ = lean_ctor_get(v___y_1782_, 17);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 1, v_mvarId_1781_);
v___x_1799_ = v___x_1795_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_toGoalState_1793_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_mvarId_1781_);
v___x_1799_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1800_; 
lean_inc(v_preTac_1797_);
v___x_1800_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(v_preTac_1797_, v___x_1799_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1802_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(v_a_1801_, v___x_1779_, v___y_1790_);
lean_dec(v_a_1801_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1829_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1829_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1829_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v_specBackwardRuleCache_1808_; lean_object* v_splitBackwardRuleCache_1809_; lean_object* v_invariants_1810_; lean_object* v_vcs_1811_; lean_object* v_simpState_1812_; lean_object* v_fuel_1813_; lean_object* v_inlineHandledInvariants_1814_; uint8_t v_preTacFailed_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1828_; 
v___x_1807_ = lean_st_ref_take(v___y_1783_);
v_specBackwardRuleCache_1808_ = lean_ctor_get(v___x_1807_, 0);
v_splitBackwardRuleCache_1809_ = lean_ctor_get(v___x_1807_, 1);
v_invariants_1810_ = lean_ctor_get(v___x_1807_, 2);
v_vcs_1811_ = lean_ctor_get(v___x_1807_, 3);
v_simpState_1812_ = lean_ctor_get(v___x_1807_, 4);
v_fuel_1813_ = lean_ctor_get(v___x_1807_, 5);
v_inlineHandledInvariants_1814_ = lean_ctor_get(v___x_1807_, 6);
v_preTacFailed_1815_ = lean_ctor_get_uint8(v___x_1807_, sizeof(void*)*7);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1817_ = v___x_1807_;
v_isShared_1818_ = v_isSharedCheck_1828_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_inlineHandledInvariants_1814_);
lean_inc(v_fuel_1813_);
lean_inc(v_simpState_1812_);
lean_inc(v_vcs_1811_);
lean_inc(v_invariants_1810_);
lean_inc(v_splitBackwardRuleCache_1809_);
lean_inc(v_specBackwardRuleCache_1808_);
lean_dec(v___x_1807_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1828_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = l_Array_append___redArg(v_vcs_1811_, v_a_1803_);
lean_dec(v_a_1803_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 3, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_specBackwardRuleCache_1808_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_splitBackwardRuleCache_1809_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_invariants_1810_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_simpState_1812_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_fuel_1813_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_inlineHandledInvariants_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*7, v_preTacFailed_1815_);
v___x_1821_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1822_ = lean_st_ref_set(v___y_1783_, v___x_1821_);
v___x_1823_ = lean_box(0);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1823_);
v___x_1825_ = v___x_1805_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_a_1830_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1802_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1802_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1800_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1800_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1777_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1777_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(lean_object* v_goal_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0(lean_object* v_as_1892_, lean_object* v_as_x27_1893_, lean_object* v_b_1894_, lean_object* v_a_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(v_as_x27_1893_, v_b_1894_, v___y_1904_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___boxed(lean_object* v_as_1909_, lean_object* v_as_x27_1910_, lean_object* v_b_1911_, lean_object* v_a_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0(v_as_1909_, v_as_x27_1910_, v_b_1911_, v_a_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v_as_x27_1910_);
lean_dec(v_as_1909_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(lean_object* v_msg_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_ref_1932_; lean_object* v___x_1933_; lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1942_; 
v_ref_1932_ = lean_ctor_get(v___y_1929_, 5);
v___x_1933_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(v_msg_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1942_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1942_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_inc(v_ref_1932_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_ref_1932_);
lean_ctor_set(v___x_1938_, 1, v_a_1934_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 1);
lean_ctor_set(v___x_1936_, 0, v___x_1938_);
v___x_1940_ = v___x_1936_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg___boxed(lean_object* v_msg_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(v_msg_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(lean_object* v_00_u03b1_1950_, lean_object* v_msg_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(v_msg_1951_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(lean_object* v_00_u03b1_1965_, lean_object* v_msg_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(v_00_u03b1_1965_, v_msg_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(lean_object* v_goal_1980_, lean_object* v_scope_1981_, size_t v_sz_1982_, size_t v_i_1983_, lean_object* v_bs_1984_){
_start:
{
uint8_t v___x_1985_; 
v___x_1985_ = lean_usize_dec_lt(v_i_1983_, v_sz_1982_);
if (v___x_1985_ == 0)
{
lean_dec_ref(v_scope_1981_);
return v_bs_1984_;
}
else
{
lean_object* v_toGoalState_1986_; lean_object* v_v_1987_; lean_object* v___x_1988_; lean_object* v_bs_x27_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v_toGoalState_1986_ = lean_ctor_get(v_goal_1980_, 0);
v_v_1987_ = lean_array_uget(v_bs_1984_, v_i_1983_);
v___x_1988_ = lean_unsigned_to_nat(0u);
v_bs_x27_1989_ = lean_array_uset(v_bs_1984_, v_i_1983_, v___x_1988_);
lean_inc_ref(v_toGoalState_1986_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_toGoalState_1986_);
lean_ctor_set(v___x_1990_, 1, v_v_1987_);
lean_inc_ref(v_scope_1981_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v_scope_1981_);
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_add(v_i_1983_, v___x_1992_);
v___x_1994_ = lean_array_uset(v_bs_x27_1989_, v_i_1983_, v___x_1991_);
v_i_1983_ = v___x_1993_;
v_bs_1984_ = v___x_1994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3___boxed(lean_object* v_goal_1996_, lean_object* v_scope_1997_, lean_object* v_sz_1998_, lean_object* v_i_1999_, lean_object* v_bs_2000_){
_start:
{
size_t v_sz_boxed_2001_; size_t v_i_boxed_2002_; lean_object* v_res_2003_; 
v_sz_boxed_2001_ = lean_unbox_usize(v_sz_1998_);
lean_dec(v_sz_1998_);
v_i_boxed_2002_ = lean_unbox_usize(v_i_1999_);
lean_dec(v_i_1999_);
v_res_2003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(v_goal_1996_, v_scope_1997_, v_sz_boxed_2001_, v_i_boxed_2002_, v_bs_2000_);
lean_dec_ref(v_goal_1996_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(lean_object* v_a_2004_, lean_object* v_scope_2005_, lean_object* v___x_2006_, lean_object* v_goal_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; size_t v_sz_2021_; size_t v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2020_ = l_Array_reverse___redArg(v_a_2004_);
v_sz_2021_ = lean_array_size(v___x_2020_);
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(v_goal_2007_, v_scope_2005_, v_sz_2021_, v___x_2022_, v___x_2020_);
v___x_2024_ = l_Array_append___redArg(v___x_2006_, v___x_2023_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2___boxed(lean_object* v_a_2027_, lean_object* v_scope_2028_, lean_object* v___x_2029_, lean_object* v_goal_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_2027_, v_scope_2028_, v___x_2029_, v_goal_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec_ref(v_goal_2030_);
return v_res_2043_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0));
v___x_2046_ = l_Lean_stringToMessageData(v___x_2045_);
return v___x_2046_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2));
v___x_2049_ = l_Lean_stringToMessageData(v___x_2048_);
return v___x_2049_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4));
v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2(lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
if (lean_obj_tag(v_a_2056_) == 0)
{
lean_object* v___x_2058_; 
v___x_2058_ = l_List_reverse___redArg(v_a_2057_);
return v___x_2058_;
}
else
{
lean_object* v_head_2059_; lean_object* v_tail_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2088_; 
v_head_2059_ = lean_ctor_get(v_a_2056_, 0);
v_tail_2060_ = lean_ctor_get(v_a_2056_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_a_2056_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2062_ = v_a_2056_;
v_isShared_2063_ = v_isSharedCheck_2088_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_tail_2060_);
lean_inc(v_head_2059_);
lean_dec(v_a_2056_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2088_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___y_2065_; 
switch(lean_obj_tag(v_head_2059_))
{
case 0:
{
lean_object* v_declName_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_declName_2070_ = lean_ctor_get(v_head_2059_, 0);
lean_inc(v_declName_2070_);
lean_dec_ref_known(v_head_2059_, 1);
v___x_2071_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1);
v___x_2072_ = l_Lean_MessageData_ofName(v_declName_2070_);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___y_2065_ = v___x_2073_;
goto v___jp_2064_;
}
case 1:
{
lean_object* v_fvarId_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_fvarId_2074_ = lean_ctor_get(v_head_2059_, 0);
lean_inc(v_fvarId_2074_);
lean_dec_ref_known(v_head_2059_, 1);
v___x_2075_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3);
v___x_2076_ = l_Lean_mkFVar(v_fvarId_2074_);
v___x_2077_ = l_Lean_MessageData_ofExpr(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2075_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___y_2065_ = v___x_2078_;
goto v___jp_2064_;
}
default: 
{
lean_object* v_ref_2079_; lean_object* v_proof_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_ref_2079_ = lean_ctor_get(v_head_2059_, 1);
lean_inc(v_ref_2079_);
v_proof_2080_ = lean_ctor_get(v_head_2059_, 2);
lean_inc_ref(v_proof_2080_);
lean_dec_ref_known(v_head_2059_, 3);
v___x_2081_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5);
v___x_2082_ = l_Lean_MessageData_ofSyntax(v_ref_2079_);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7);
v___x_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = l_Lean_MessageData_ofExpr(v_proof_2080_);
v___x_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___y_2065_ = v___x_2087_;
goto v___jp_2064_;
}
}
v___jp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v_a_2057_);
lean_ctor_set(v___x_2062_, 0, v___y_2065_);
v___x_2067_ = v___x_2062_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___y_2065_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_a_2057_);
v___x_2067_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v_a_2056_ = v_tail_2060_;
v_a_2057_ = v___x_2067_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(size_t v_sz_2089_, size_t v_i_2090_, lean_object* v_bs_2091_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_usize_dec_lt(v_i_2090_, v_sz_2089_);
if (v___x_2092_ == 0)
{
return v_bs_2091_;
}
else
{
lean_object* v_v_2093_; lean_object* v_proof_2094_; lean_object* v___x_2095_; lean_object* v_bs_x27_2096_; size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v_v_2093_ = lean_array_uget_borrowed(v_bs_2091_, v_i_2090_);
v_proof_2094_ = lean_ctor_get(v_v_2093_, 1);
lean_inc_ref(v_proof_2094_);
v___x_2095_ = lean_unsigned_to_nat(0u);
v_bs_x27_2096_ = lean_array_uset(v_bs_2091_, v_i_2090_, v___x_2095_);
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_i_2090_, v___x_2097_);
v___x_2099_ = lean_array_uset(v_bs_x27_2096_, v_i_2090_, v_proof_2094_);
v_i_2090_ = v___x_2098_;
v_bs_2091_ = v___x_2099_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(lean_object* v_sz_2101_, lean_object* v_i_2102_, lean_object* v_bs_2103_){
_start:
{
size_t v_sz_boxed_2104_; size_t v_i_boxed_2105_; lean_object* v_res_2106_; 
v_sz_boxed_2104_ = lean_unbox_usize(v_sz_2101_);
lean_dec(v_sz_2101_);
v_i_boxed_2105_ = lean_unbox_usize(v_i_2102_);
lean_dec(v_i_2102_);
v_res_2106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_sz_boxed_2104_, v_i_boxed_2105_, v_bs_2103_);
return v_res_2106_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0));
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
return v___x_2109_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2));
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4));
v___x_2115_ = l_Lean_stringToMessageData(v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6));
v___x_2118_ = l_Lean_stringToMessageData(v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8));
v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1(uint8_t v___x_2122_, lean_object* v_monad_2123_, lean_object* v_e_2124_, lean_object* v_thms_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
if (v___x_2122_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; size_t v_sz_2147_; size_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2138_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1);
v___x_2139_ = l_Lean_MessageData_ofExpr(v_monad_2123_);
v___x_2140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3);
v___x_2142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2140_);
lean_ctor_set(v___x_2142_, 1, v___x_2141_);
v___x_2143_ = l_Lean_MessageData_ofExpr(v_e_2124_);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2142_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
v___x_2145_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2144_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v_sz_2147_ = lean_array_size(v_thms_2125_);
v___x_2148_ = ((size_t)0ULL);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_sz_2147_, v___x_2148_, v_thms_2125_);
v___x_2150_ = lean_array_to_list(v___x_2149_);
v___x_2151_ = lean_box(0);
v___x_2152_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2(v___x_2150_, v___x_2151_);
v___x_2153_ = l_Lean_MessageData_ofList(v___x_2152_);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2146_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(v___x_2156_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v_thms_2125_);
lean_dec_ref(v_monad_2123_);
v___x_2158_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9);
v___x_2159_ = l_Lean_MessageData_ofExpr(v_e_2124_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(v___x_2162_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___boxed(lean_object* v___x_2164_, lean_object* v_monad_2165_, lean_object* v_e_2166_, lean_object* v_thms_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
uint8_t v___x_79070__boxed_2180_; lean_object* v_res_2181_; 
v___x_79070__boxed_2180_ = lean_unbox(v___x_2164_);
v_res_2181_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1(v___x_79070__boxed_2180_, v_monad_2165_, v_e_2166_, v_thms_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(lean_object* v_goal_2182_, lean_object* v___x_2183_, lean_object* v_target_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_2182_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2205_; 
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2205_ == 0)
{
lean_object* v_unused_2206_; 
v_unused_2206_ = lean_ctor_get(v___x_2197_, 0);
lean_dec(v_unused_2206_);
v___x_2199_ = v___x_2197_;
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
else
{
lean_dec(v___x_2197_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2205_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2183_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2201_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec_ref(v___x_2183_);
v_a_2207_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2197_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2197_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0___boxed(lean_object* v_goal_2215_, lean_object* v___x_2216_, lean_object* v_target_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(v_goal_2215_, v___x_2216_, v_target_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec_ref(v_target_2217_);
return v_res_2230_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0));
v___x_2233_ = l_Lean_stringToMessageData(v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(lean_object* v_a_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___y_2248_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2268_ = lean_array_get_size(v_a_2234_);
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = lean_nat_sub(v___x_2268_, v___x_2269_);
v___x_2271_ = lean_nat_dec_lt(v___x_2270_, v___x_2268_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; 
lean_dec(v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2234_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_2236_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; lean_object* v_goal_2276_; lean_object* v_scope_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
v___x_2275_ = lean_array_fget_borrowed(v_a_2234_, v___x_2270_);
lean_dec(v___x_2270_);
v_goal_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc_ref(v_goal_2276_);
v_scope_2277_ = lean_ctor_get(v___x_2275_, 1);
lean_inc_ref(v_scope_2277_);
v___x_2278_ = lean_array_pop(v_a_2234_);
v___x_2279_ = lean_unbox(v_a_2274_);
lean_dec(v_a_2274_);
if (v___x_2279_ == 0)
{
lean_object* v_mvarId_2280_; lean_object* v___x_2281_; 
v_mvarId_2280_ = lean_ctor_get(v_goal_2276_, 1);
lean_inc(v_mvarId_2280_);
v___x_2281_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_2277_, v_mvarId_2280_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
switch(lean_obj_tag(v_a_2282_))
{
case 2:
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2303_; 
lean_inc(v_mvarId_2280_);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_goal_2276_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; lean_object* v_unused_2305_; 
v_unused_2304_ = lean_ctor_get(v_goal_2276_, 1);
lean_dec(v_unused_2304_);
v_unused_2305_ = lean_ctor_get(v_goal_2276_, 0);
lean_dec(v_unused_2305_);
v___x_2284_ = v_goal_2276_;
v_isShared_2285_ = v_isSharedCheck_2303_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v_goal_2276_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2303_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_e_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v_e_2286_ = lean_ctor_get(v_a_2282_, 0);
lean_inc_ref(v_e_2286_);
lean_dec_ref_known(v_a_2282_, 1);
v___x_2287_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1);
v___x_2288_ = l_Lean_MessageData_ofExpr(v_e_2286_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set_tag(v___x_2284_, 7);
lean_ctor_set(v___x_2284_, 1, v___x_2288_);
lean_ctor_set(v___x_2284_, 0, v___x_2287_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_alloc_closure((void*)(l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed), 14, 2);
lean_closure_set(v___x_2291_, 0, lean_box(0));
lean_closure_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_2280_, v___x_2291_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_dec_ref_known(v___x_2292_, 1);
v_a_2234_ = v___x_2278_;
goto _start;
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v___x_2278_);
v_a_2294_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2292_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2292_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
}
case 3:
{
uint8_t v_errorOnMissingSpec_2306_; 
v_errorOnMissingSpec_2306_ = lean_ctor_get_uint8(v___y_2235_, sizeof(void*)*19 + 2);
if (v_errorOnMissingSpec_2306_ == 0)
{
lean_object* v___x_2307_; 
lean_dec_ref_known(v_a_2282_, 3);
v___x_2307_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_2276_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_dec_ref_known(v___x_2307_, 1);
v_a_2234_ = v___x_2278_;
goto _start;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v___x_2278_);
v_a_2309_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2307_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2307_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
else
{
lean_object* v_e_2317_; lean_object* v_monad_2318_; lean_object* v_thms_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___y_2324_; lean_object* v___x_2325_; 
lean_inc(v_mvarId_2280_);
lean_dec_ref(v_goal_2276_);
v_e_2317_ = lean_ctor_get(v_a_2282_, 0);
lean_inc_ref(v_e_2317_);
v_monad_2318_ = lean_ctor_get(v_a_2282_, 1);
lean_inc_ref(v_monad_2318_);
v_thms_2319_ = lean_ctor_get(v_a_2282_, 2);
lean_inc_ref(v_thms_2319_);
lean_dec_ref_known(v_a_2282_, 3);
v___x_2320_ = lean_array_get_size(v_thms_2319_);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_nat_dec_eq(v___x_2320_, v___x_2321_);
v___x_2323_ = lean_box(v___x_2322_);
v___y_2324_ = lean_alloc_closure((void*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___boxed), 16, 4);
lean_closure_set(v___y_2324_, 0, v___x_2323_);
lean_closure_set(v___y_2324_, 1, v_monad_2318_);
lean_closure_set(v___y_2324_, 2, v_e_2317_);
lean_closure_set(v___y_2324_, 3, v_thms_2319_);
v___x_2325_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_2280_, v___y_2324_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref_known(v___x_2325_, 1);
v_a_2234_ = v___x_2278_;
goto _start;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v___x_2278_);
v_a_2327_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2325_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2325_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
case 4:
{
lean_object* v_scope_2335_; lean_object* v_subgoals_2336_; lean_object* v___x_2337_; 
v_scope_2335_ = lean_ctor_get(v_a_2282_, 0);
lean_inc_ref(v_scope_2335_);
v_subgoals_2336_ = lean_ctor_get(v_a_2282_, 1);
lean_inc(v_subgoals_2336_);
lean_dec_ref_known(v_a_2282_, 2);
v___x_2337_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_2336_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v_subgoals_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = lean_array_get_size(v_a_2338_);
v___x_2340_ = lean_nat_dec_lt(v___x_2269_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
v___x_2341_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_2338_, v_scope_2335_, v___x_2278_, v_goal_2276_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec_ref(v_goal_2276_);
v___y_2248_ = v___x_2341_;
goto v___jp_2247_;
}
else
{
lean_object* v_preTac_2342_; lean_object* v___x_2343_; 
v_preTac_2342_ = lean_ctor_get(v___y_2235_, 17);
v___x_2343_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(v_preTac_2342_, v_goal_2276_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2345_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_2338_, v_scope_2335_, v___x_2278_, v_a_2344_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v_a_2344_);
v___y_2248_ = v___x_2345_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_a_2338_);
lean_dec_ref(v_scope_2335_);
lean_dec_ref(v___x_2278_);
v_a_2346_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2343_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2343_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v_scope_2335_);
lean_dec_ref(v___x_2278_);
lean_dec_ref(v_goal_2276_);
v_a_2354_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2337_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2337_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
default: 
{
lean_object* v_target_2362_; lean_object* v___x_2363_; 
v_target_2362_ = lean_ctor_get(v_a_2282_, 0);
lean_inc_ref(v_target_2362_);
lean_dec(v_a_2282_);
v___x_2363_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(v_goal_2276_, v___x_2278_, v_target_2362_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec_ref(v_target_2362_);
v___y_2248_ = v___x_2363_;
goto v___jp_2247_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v___x_2278_);
lean_dec_ref(v_goal_2276_);
v_a_2364_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2281_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2281_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v___x_2372_; 
lean_dec_ref(v_scope_2277_);
v___x_2372_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_2276_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_dec_ref_known(v___x_2372_, 1);
v_a_2234_ = v___x_2278_;
goto _start;
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v___x_2278_);
v_a_2374_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2372_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2372_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v___x_2270_);
lean_dec_ref(v_a_2234_);
v_a_2382_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2273_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2273_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
v___jp_2247_:
{
if (lean_obj_tag(v___y_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2259_; 
v_a_2249_ = lean_ctor_get(v___y_2248_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___y_2248_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2251_ = v___y_2248_;
v_isShared_2252_ = v_isSharedCheck_2259_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___y_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2259_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
if (lean_obj_tag(v_a_2249_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; 
v_a_2253_ = lean_ctor_get(v_a_2249_, 0);
lean_inc(v_a_2253_);
lean_dec_ref_known(v_a_2249_, 1);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v_a_2253_);
v___x_2255_ = v___x_2251_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
else
{
lean_object* v_a_2257_; 
lean_del_object(v___x_2251_);
v_a_2257_ = lean_ctor_get(v_a_2249_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v_a_2249_, 1);
v_a_2234_ = v_a_2257_;
goto _start;
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_a_2260_ = lean_ctor_get(v___y_2248_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___y_2248_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___y_2248_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___y_2248_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___boxed(lean_object* v_a_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v_a_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object* v_scope_2404_, lean_object* v_goal_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_toGoalState_2418_; lean_object* v_mvarId_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2458_; 
v_toGoalState_2418_ = lean_ctor_get(v_goal_2405_, 0);
v_mvarId_2419_ = lean_ctor_get(v_goal_2405_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_goal_2405_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2421_ = v_goal_2405_;
v_isShared_2422_ = v_isSharedCheck_2458_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_mvarId_2419_);
lean_inc(v_toGoalState_2418_);
lean_dec(v_goal_2405_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2458_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_2419_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v_a_2424_);
v___x_2426_ = v___x_2421_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_toGoalState_2418_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_a_2424_);
v___x_2426_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v_scope_2404_);
v___x_2428_ = lean_unsigned_to_nat(1u);
v___x_2429_ = lean_mk_empty_array_with_capacity(v___x_2428_);
v___x_2430_ = lean_array_push(v___x_2429_, v___x_2427_);
v___x_2431_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v___x_2430_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2439_; 
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v___x_2431_, 0);
lean_dec(v_unused_2440_);
v___x_2433_ = v___x_2431_;
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
else
{
lean_dec(v___x_2431_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2439_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2435_ = lean_box(0);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2435_);
v___x_2437_ = v___x_2433_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
v_a_2441_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2431_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2431_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_del_object(v___x_2421_);
lean_dec_ref(v_toGoalState_2418_);
lean_dec_ref(v_scope_2404_);
v_a_2450_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2423_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2423_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object* v_scope_2459_, lean_object* v_goal_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_scope_2459_, v_goal_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4(lean_object* v_inst_2474_, lean_object* v_a_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v_a_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___boxed(lean_object* v_inst_2489_, lean_object* v_a_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4(v_inst_2489_, v_a_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(lean_object* v_as_2505_, lean_object* v_i_2506_, lean_object* v_j_2507_, lean_object* v_bs_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_zero_2514_; uint8_t v_isZero_2515_; 
v_zero_2514_ = lean_unsigned_to_nat(0u);
v_isZero_2515_ = lean_nat_dec_eq(v_i_2506_, v_zero_2514_);
if (v_isZero_2515_ == 1)
{
lean_object* v___x_2516_; 
lean_dec(v_j_2507_);
lean_dec(v_i_2506_);
v___x_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_bs_2508_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; lean_object* v_mvarId_2518_; lean_object* v___x_2519_; 
v___x_2517_ = lean_array_fget_borrowed(v_as_2505_, v_j_2507_);
v_mvarId_2518_ = lean_ctor_get(v___x_2517_, 1);
lean_inc(v_mvarId_2518_);
v___x_2519_ = l_Lean_MVarId_getTag(v_mvarId_2518_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2521_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___closed__0));
v___x_2522_ = lean_unsigned_to_nat(1u);
v___x_2523_ = lean_nat_add(v_j_2507_, v___x_2522_);
lean_dec(v_j_2507_);
lean_inc(v___x_2523_);
v___x_2524_ = l_Nat_reprFast(v___x_2523_);
v___x_2525_ = lean_string_append(v___x_2521_, v___x_2524_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = lean_box(0);
v___x_2527_ = l_Lean_Name_str___override(v___x_2526_, v___x_2525_);
v___x_2528_ = lean_erase_macro_scopes(v_a_2520_);
v___x_2529_ = l_Lean_Name_append(v___x_2527_, v___x_2528_);
lean_inc(v_mvarId_2518_);
v___x_2530_ = l_Lean_MVarId_setTag___redArg(v_mvarId_2518_, v___x_2529_, v___y_2510_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_n_2532_; lean_object* v___x_2533_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v_n_2532_ = lean_nat_sub(v_i_2506_, v___x_2522_);
lean_dec(v_i_2506_);
v___x_2533_ = lean_array_push(v_bs_2508_, v_a_2531_);
v_i_2506_ = v_n_2532_;
v_j_2507_ = v___x_2523_;
v_bs_2508_ = v___x_2533_;
goto _start;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v___x_2523_);
lean_dec_ref(v_bs_2508_);
lean_dec(v_i_2506_);
v_a_2535_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2530_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2530_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v_bs_2508_);
lean_dec(v_j_2507_);
lean_dec(v_i_2506_);
v_a_2543_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2519_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2519_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg___boxed(lean_object* v_as_2551_, lean_object* v_i_2552_, lean_object* v_j_2553_, lean_object* v_bs_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_as_2551_, v_i_2552_, v_j_2553_, v_bs_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec_ref(v_as_2551_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(lean_object* v_as_2562_, lean_object* v_i_2563_, lean_object* v_j_2564_, lean_object* v_bs_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_zero_2568_; uint8_t v_isZero_2569_; 
v_zero_2568_ = lean_unsigned_to_nat(0u);
v_isZero_2569_ = lean_nat_dec_eq(v_i_2563_, v_zero_2568_);
if (v_isZero_2569_ == 1)
{
lean_object* v___x_2570_; 
lean_dec(v_j_2564_);
lean_dec(v_i_2563_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_bs_2565_);
return v___x_2570_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2571_ = lean_array_fget_borrowed(v_as_2562_, v_j_2564_);
v___x_2572_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___closed__0));
v___x_2573_ = lean_unsigned_to_nat(1u);
v___x_2574_ = lean_nat_add(v_j_2564_, v___x_2573_);
lean_dec(v_j_2564_);
lean_inc(v___x_2574_);
v___x_2575_ = l_Nat_reprFast(v___x_2574_);
v___x_2576_ = lean_string_append(v___x_2572_, v___x_2575_);
lean_dec_ref(v___x_2575_);
v___x_2577_ = lean_box(0);
v___x_2578_ = l_Lean_Name_str___override(v___x_2577_, v___x_2576_);
lean_inc(v___x_2571_);
v___x_2579_ = l_Lean_MVarId_setTag___redArg(v___x_2571_, v___x_2578_, v___y_2566_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v_n_2581_; lean_object* v___x_2582_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v_n_2581_ = lean_nat_sub(v_i_2563_, v___x_2573_);
lean_dec(v_i_2563_);
v___x_2582_ = lean_array_push(v_bs_2565_, v_a_2580_);
v_i_2563_ = v_n_2581_;
v_j_2564_ = v___x_2574_;
v_bs_2565_ = v___x_2582_;
goto _start;
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v___x_2574_);
lean_dec_ref(v_bs_2565_);
lean_dec(v_i_2563_);
v_a_2584_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2579_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2579_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg___boxed(lean_object* v_as_2592_, lean_object* v_i_2593_, lean_object* v_j_2594_, lean_object* v_bs_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_as_2592_, v_i_2593_, v_j_2594_, v_bs_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v_as_2592_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(lean_object* v_mvarId_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; lean_object* v_mctx_2603_; lean_object* v_eAssignment_2604_; uint8_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2602_ = lean_st_ref_get(v___y_2600_);
v_mctx_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc_ref(v_mctx_2603_);
lean_dec(v___x_2602_);
v_eAssignment_2604_ = lean_ctor_get(v_mctx_2603_, 8);
lean_inc_ref(v_eAssignment_2604_);
lean_dec_ref(v_mctx_2603_);
v___x_2605_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant_spec__1_spec__2___redArg(v_eAssignment_2604_, v_mvarId_2599_);
lean_dec_ref(v_eAssignment_2604_);
v___x_2606_ = lean_box(v___x_2605_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg___boxed(lean_object* v_mvarId_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec(v_mvarId_2608_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(lean_object* v_as_2612_, size_t v_i_2613_, size_t v_stop_2614_, lean_object* v_b_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_a_2627_; uint8_t v___x_2631_; 
v___x_2631_ = lean_usize_dec_eq(v_i_2613_, v_stop_2614_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v_mvarId_2635_; lean_object* v___x_2636_; 
v___x_2632_ = lean_array_uget_borrowed(v_as_2612_, v_i_2613_);
v_mvarId_2635_ = lean_ctor_get(v___x_2632_, 1);
v___x_2636_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_2635_, v___y_2622_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; uint8_t v___x_2638_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v___x_2638_ = lean_unbox(v_a_2637_);
lean_dec(v_a_2637_);
if (v___x_2638_ == 0)
{
goto v___jp_2633_;
}
else
{
v_a_2627_ = v_b_2615_;
goto v___jp_2626_;
}
}
else
{
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2639_; uint8_t v___x_2640_; 
v_a_2639_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2636_, 1);
v___x_2640_ = lean_unbox(v_a_2639_);
lean_dec(v_a_2639_);
if (v___x_2640_ == 0)
{
v_a_2627_ = v_b_2615_;
goto v___jp_2626_;
}
else
{
goto v___jp_2633_;
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec_ref(v_b_2615_);
v_a_2641_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2636_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2636_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
v___jp_2633_:
{
lean_object* v___x_2634_; 
lean_inc(v___x_2632_);
v___x_2634_ = lean_array_push(v_b_2615_, v___x_2632_);
v_a_2627_ = v___x_2634_;
goto v___jp_2626_;
}
}
else
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_b_2615_);
return v___x_2649_;
}
v___jp_2626_:
{
size_t v___x_2628_; size_t v___x_2629_; 
v___x_2628_ = ((size_t)1ULL);
v___x_2629_ = lean_usize_add(v_i_2613_, v___x_2628_);
v_i_2613_ = v___x_2629_;
v_b_2615_ = v_a_2627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3___boxed(lean_object* v_as_2650_, lean_object* v_i_2651_, lean_object* v_stop_2652_, lean_object* v_b_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
size_t v_i_boxed_2664_; size_t v_stop_boxed_2665_; lean_object* v_res_2666_; 
v_i_boxed_2664_ = lean_unbox_usize(v_i_2651_);
lean_dec(v_i_2651_);
v_stop_boxed_2665_ = lean_unbox_usize(v_stop_2652_);
lean_dec(v_stop_2652_);
v_res_2666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_as_2650_, v_i_boxed_2664_, v_stop_boxed_2665_, v_b_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v_as_2650_);
return v_res_2666_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_unsigned_to_nat(16u);
v___x_2669_ = lean_mk_array(v___x_2668_, v___x_2667_);
return v___x_2669_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__0);
v___x_2671_ = lean_unsigned_to_nat(0u);
v___x_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v___x_2670_);
return v___x_2672_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2(void){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2673_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__2);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__3);
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
lean_ctor_set(v___x_2678_, 1, v___x_2676_);
lean_ctor_set(v___x_2678_, 2, v___x_2676_);
lean_ctor_set(v___x_2678_, 3, v___x_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object* v_goal_2679_, lean_object* v_ctx_2680_, lean_object* v_scope_2681_, lean_object* v_stepLimit_x3f_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___y_2694_; lean_object* v___y_2695_; uint8_t v___y_2696_; lean_object* v_a_2697_; lean_object* v___y_2701_; lean_object* v___y_2702_; uint8_t v___y_2703_; lean_object* v___y_2704_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___y_2719_; 
v___x_2714_ = lean_unsigned_to_nat(0u);
v___x_2715_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__1);
v___x_2716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_2717_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_run___closed__4);
if (lean_obj_tag(v_stepLimit_x3f_2682_) == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_box(1);
v___y_2719_ = v___x_2767_;
goto v___jp_2718_;
}
else
{
lean_object* v_val_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_val_2768_ = lean_ctor_get(v_stepLimit_x3f_2682_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_stepLimit_x3f_2682_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v_stepLimit_x3f_2682_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_val_2768_);
lean_dec(v_stepLimit_x3f_2682_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_val_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v___y_2719_ = v___x_2773_;
goto v___jp_2718_;
}
}
}
v___jp_2693_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2698_, 0, v___y_2694_);
lean_ctor_set(v___x_2698_, 1, v_a_2697_);
lean_ctor_set(v___x_2698_, 2, v___y_2695_);
lean_ctor_set_uint8(v___x_2698_, sizeof(void*)*3, v___y_2696_);
v___x_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
return v___x_2699_;
}
v___jp_2700_:
{
if (lean_obj_tag(v___y_2704_) == 0)
{
lean_object* v_a_2705_; 
v_a_2705_ = lean_ctor_get(v___y_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___y_2704_, 1);
v___y_2694_ = v___y_2701_;
v___y_2695_ = v___y_2702_;
v___y_2696_ = v___y_2703_;
v_a_2697_ = v_a_2705_;
goto v___jp_2693_;
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v___y_2702_);
lean_dec_ref(v___y_2701_);
v_a_2706_ = lean_ctor_get(v___y_2704_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___y_2704_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___y_2704_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___y_2704_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
v___jp_2718_:
{
uint8_t v___x_2720_; lean_object* v_initState_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2720_ = 0;
v_initState_2721_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v_initState_2721_, 0, v___x_2715_);
lean_ctor_set(v_initState_2721_, 1, v___x_2715_);
lean_ctor_set(v_initState_2721_, 2, v___x_2716_);
lean_ctor_set(v_initState_2721_, 3, v___x_2716_);
lean_ctor_set(v_initState_2721_, 4, v___x_2717_);
lean_ctor_set(v_initState_2721_, 5, v___y_2719_);
lean_ctor_set(v_initState_2721_, 6, v___x_2715_);
lean_ctor_set_uint8(v_initState_2721_, sizeof(void*)*7, v___x_2720_);
v___x_2722_ = lean_st_mk_ref(v_initState_2721_);
v___x_2723_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_scope_2681_, v_goal_2679_, v_ctx_2680_, v___x_2722_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; lean_object* v_invariants_2725_; lean_object* v_vcs_2726_; lean_object* v_inlineHandledInvariants_2727_; uint8_t v_preTacFailed_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_dec_ref_known(v___x_2723_, 1);
v___x_2724_ = lean_st_ref_get(v___x_2722_);
lean_dec(v___x_2722_);
v_invariants_2725_ = lean_ctor_get(v___x_2724_, 2);
lean_inc_ref(v_invariants_2725_);
v_vcs_2726_ = lean_ctor_get(v___x_2724_, 3);
lean_inc_ref(v_vcs_2726_);
v_inlineHandledInvariants_2727_ = lean_ctor_get(v___x_2724_, 6);
lean_inc_ref(v_inlineHandledInvariants_2727_);
v_preTacFailed_2728_ = lean_ctor_get_uint8(v___x_2724_, sizeof(void*)*7);
lean_dec(v___x_2724_);
v___x_2729_ = lean_array_get_size(v_invariants_2725_);
v___x_2730_ = lean_mk_empty_array_with_capacity(v___x_2729_);
v___x_2731_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_invariants_2725_, v___x_2729_, v___x_2714_, v___x_2730_, v_a_2689_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2731_, 1);
v___x_2732_ = lean_array_get_size(v_vcs_2726_);
v___x_2733_ = lean_mk_empty_array_with_capacity(v___x_2732_);
v___x_2734_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_vcs_2726_, v___x_2732_, v___x_2714_, v___x_2733_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2734_) == 0)
{
uint8_t v___x_2735_; 
lean_dec_ref_known(v___x_2734_, 1);
v___x_2735_ = lean_nat_dec_lt(v___x_2714_, v___x_2732_);
if (v___x_2735_ == 0)
{
lean_dec_ref(v_vcs_2726_);
v___y_2694_ = v_invariants_2725_;
v___y_2695_ = v_inlineHandledInvariants_2727_;
v___y_2696_ = v_preTacFailed_2728_;
v_a_2697_ = v___x_2716_;
goto v___jp_2693_;
}
else
{
uint8_t v___x_2736_; 
v___x_2736_ = lean_nat_dec_le(v___x_2732_, v___x_2732_);
if (v___x_2736_ == 0)
{
if (v___x_2735_ == 0)
{
lean_dec_ref(v_vcs_2726_);
v___y_2694_ = v_invariants_2725_;
v___y_2695_ = v_inlineHandledInvariants_2727_;
v___y_2696_ = v_preTacFailed_2728_;
v_a_2697_ = v___x_2716_;
goto v___jp_2693_;
}
else
{
size_t v___x_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = ((size_t)0ULL);
v___x_2738_ = lean_usize_of_nat(v___x_2732_);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_vcs_2726_, v___x_2737_, v___x_2738_, v___x_2716_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec_ref(v_vcs_2726_);
v___y_2701_ = v_invariants_2725_;
v___y_2702_ = v_inlineHandledInvariants_2727_;
v___y_2703_ = v_preTacFailed_2728_;
v___y_2704_ = v___x_2739_;
goto v___jp_2700_;
}
}
else
{
size_t v___x_2740_; size_t v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = ((size_t)0ULL);
v___x_2741_ = lean_usize_of_nat(v___x_2732_);
v___x_2742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__3(v_vcs_2726_, v___x_2740_, v___x_2741_, v___x_2716_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec_ref(v_vcs_2726_);
v___y_2701_ = v_invariants_2725_;
v___y_2702_ = v_inlineHandledInvariants_2727_;
v___y_2703_ = v_preTacFailed_2728_;
v___y_2704_ = v___x_2742_;
goto v___jp_2700_;
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v_inlineHandledInvariants_2727_);
lean_dec_ref(v_vcs_2726_);
lean_dec_ref(v_invariants_2725_);
v_a_2743_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2734_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2734_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v_inlineHandledInvariants_2727_);
lean_dec_ref(v_vcs_2726_);
lean_dec_ref(v_invariants_2725_);
v_a_2751_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2731_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2731_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v___x_2722_);
v_a_2759_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2723_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2723_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run___boxed(lean_object* v_goal_2776_, lean_object* v_ctx_2777_, lean_object* v_scope_2778_, lean_object* v_stepLimit_x3f_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run(v_goal_2776_, v_ctx_2777_, v_scope_2778_, v_stepLimit_x3f_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_a_2780_);
lean_dec_ref(v_ctx_2777_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(lean_object* v_mvarId_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___redArg(v_mvarId_2791_, v___y_2798_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0___boxed(lean_object* v_mvarId_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__0(v_mvarId_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec(v_mvarId_2803_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(lean_object* v_as_2815_, lean_object* v_i_2816_, lean_object* v_j_2817_, lean_object* v_inv_2818_, lean_object* v_bs_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___redArg(v_as_2815_, v_i_2816_, v_j_2817_, v_bs_2819_, v___y_2826_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1___boxed(lean_object* v_as_2831_, lean_object* v_i_2832_, lean_object* v_j_2833_, lean_object* v_inv_2834_, lean_object* v_bs_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__1(v_as_2831_, v_i_2832_, v_j_2833_, v_inv_2834_, v_bs_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v_as_2831_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(lean_object* v_as_2847_, lean_object* v_i_2848_, lean_object* v_j_2849_, lean_object* v_inv_2850_, lean_object* v_bs_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___redArg(v_as_2847_, v_i_2848_, v_j_2849_, v_bs_2851_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2___boxed(lean_object* v_as_2863_, lean_object* v_i_2864_, lean_object* v_j_2865_, lean_object* v_inv_2866_, lean_object* v_bs_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_run_spec__2(v_as_2863_, v_i_2864_, v_j_2865_, v_inv_2866_, v_bs_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v_as_2863_);
return v_res_2878_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Grind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
}
#ifdef __cplusplus
}
#endif
