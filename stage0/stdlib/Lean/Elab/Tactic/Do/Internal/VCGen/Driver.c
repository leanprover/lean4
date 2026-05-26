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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_setTag___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_setKind___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
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
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkGoalCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__4_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__8_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__11_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__13_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "renameI"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__17_value),LEAN_SCALAR_PTR_LITERAL(20, 41, 101, 89, 107, 117, 242, 244)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rename_i"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__19_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__20;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__22_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__25_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__26_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "vc"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg___closed__0 = (const lean_object*)&l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__3(lean_object* v_msgData_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v_mctx_114_; lean_object* v_lctx_115_; lean_object* v_options_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_111_ = lean_st_ref_get(v___y_109_);
v_env_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_env_112_);
lean_dec(v___x_111_);
v___x_113_ = lean_st_ref_get(v___y_107_);
v_mctx_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_mctx_114_);
lean_dec(v___x_113_);
v_lctx_115_ = lean_ctor_get(v___y_106_, 2);
v_options_116_ = lean_ctor_get(v___y_108_, 2);
lean_inc_ref(v_options_116_);
lean_inc_ref(v_lctx_115_);
v___x_117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_117_, 0, v_env_112_);
lean_ctor_set(v___x_117_, 1, v_mctx_114_);
lean_ctor_set(v___x_117_, 2, v_lctx_115_);
lean_ctor_set(v___x_117_, 3, v_options_116_);
v___x_118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_msgData_105_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_msgData_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__3(v_msgData_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0(uint8_t v___y_135_, uint8_t v_suppressElabErrors_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 1)
{
lean_object* v_pre_138_; 
v_pre_138_ = lean_ctor_get(v_x_137_, 0);
switch(lean_obj_tag(v_pre_138_))
{
case 1:
{
lean_object* v_pre_139_; 
v_pre_139_ = lean_ctor_get(v_pre_138_, 0);
switch(lean_obj_tag(v_pre_139_))
{
case 0:
{
lean_object* v_str_140_; lean_object* v_str_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_str_140_ = lean_ctor_get(v_x_137_, 1);
v_str_141_ = lean_ctor_get(v_pre_138_, 1);
v___x_142_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__0));
v___x_143_ = lean_string_dec_eq(v_str_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__1));
v___x_145_ = lean_string_dec_eq(v_str_141_, v___x_144_);
if (v___x_145_ == 0)
{
return v___y_135_;
}
else
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__2));
v___x_147_ = lean_string_dec_eq(v_str_140_, v___x_146_);
if (v___x_147_ == 0)
{
return v___y_135_;
}
else
{
return v_suppressElabErrors_136_;
}
}
}
else
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__3));
v___x_149_ = lean_string_dec_eq(v_str_140_, v___x_148_);
if (v___x_149_ == 0)
{
return v___y_135_;
}
else
{
return v_suppressElabErrors_136_;
}
}
}
case 1:
{
lean_object* v_pre_150_; 
v_pre_150_ = lean_ctor_get(v_pre_139_, 0);
if (lean_obj_tag(v_pre_150_) == 0)
{
lean_object* v_str_151_; lean_object* v_str_152_; lean_object* v_str_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_str_151_ = lean_ctor_get(v_x_137_, 1);
v_str_152_ = lean_ctor_get(v_pre_138_, 1);
v_str_153_ = lean_ctor_get(v_pre_139_, 1);
v___x_154_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__4));
v___x_155_ = lean_string_dec_eq(v_str_153_, v___x_154_);
if (v___x_155_ == 0)
{
return v___y_135_;
}
else
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__5));
v___x_157_ = lean_string_dec_eq(v_str_152_, v___x_156_);
if (v___x_157_ == 0)
{
return v___y_135_;
}
else
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__6));
v___x_159_ = lean_string_dec_eq(v_str_151_, v___x_158_);
if (v___x_159_ == 0)
{
return v___y_135_;
}
else
{
return v_suppressElabErrors_136_;
}
}
}
}
else
{
return v___y_135_;
}
}
default: 
{
return v___y_135_;
}
}
}
case 0:
{
lean_object* v_str_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_str_160_ = lean_ctor_get(v_x_137_, 1);
v___x_161_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___closed__7));
v___x_162_ = lean_string_dec_eq(v_str_160_, v___x_161_);
if (v___x_162_ == 0)
{
return v___y_135_;
}
else
{
return v_suppressElabErrors_136_;
}
}
default: 
{
return v___y_135_;
}
}
}
else
{
return v___y_135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_163_, lean_object* v_suppressElabErrors_164_, lean_object* v_x_165_){
_start:
{
uint8_t v___y_41453__boxed_166_; uint8_t v_suppressElabErrors_boxed_167_; uint8_t v_res_168_; lean_object* v_r_169_; 
v___y_41453__boxed_166_ = lean_unbox(v___y_163_);
v_suppressElabErrors_boxed_167_ = lean_unbox(v_suppressElabErrors_164_);
v_res_168_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0(v___y_41453__boxed_166_, v_suppressElabErrors_boxed_167_, v_x_165_);
lean_dec(v_x_165_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(lean_object* v_opts_170_, lean_object* v_opt_171_){
_start:
{
lean_object* v_name_172_; lean_object* v_defValue_173_; lean_object* v_map_174_; lean_object* v___x_175_; 
v_name_172_ = lean_ctor_get(v_opt_171_, 0);
v_defValue_173_ = lean_ctor_get(v_opt_171_, 1);
v_map_174_ = lean_ctor_get(v_opts_170_, 0);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_174_, v_name_172_);
if (lean_obj_tag(v___x_175_) == 0)
{
uint8_t v___x_176_; 
v___x_176_ = lean_unbox(v_defValue_173_);
return v___x_176_;
}
else
{
lean_object* v_val_177_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_175_, 1);
if (lean_obj_tag(v_val_177_) == 1)
{
uint8_t v_v_178_; 
v_v_178_ = lean_ctor_get_uint8(v_val_177_, 0);
lean_dec_ref_known(v_val_177_, 0);
return v_v_178_;
}
else
{
uint8_t v___x_179_; 
lean_dec(v_val_177_);
v___x_179_ = lean_unbox(v_defValue_173_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_opts_180_, lean_object* v_opt_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(v_opts_180_, v_opt_181_);
lean_dec_ref(v_opt_181_);
lean_dec_ref(v_opts_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_185_, lean_object* v_msgData_186_, uint8_t v_severity_187_, uint8_t v_isSilent_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; uint8_t v___y_199_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_231_; uint8_t v___y_232_; lean_object* v___y_233_; uint8_t v___y_234_; lean_object* v___y_235_; uint8_t v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_256_; uint8_t v___y_257_; lean_object* v___y_258_; uint8_t v___y_259_; uint8_t v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_267_; lean_object* v___y_268_; uint8_t v___y_269_; lean_object* v___y_270_; uint8_t v___y_271_; lean_object* v___y_272_; uint8_t v___y_273_; uint8_t v___x_278_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; uint8_t v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; uint8_t v___y_286_; uint8_t v___y_288_; uint8_t v___x_303_; 
v___x_278_ = 2;
v___x_303_ = l_Lean_instBEqMessageSeverity_beq(v_severity_187_, v___x_278_);
if (v___x_303_ == 0)
{
v___y_288_ = v___x_303_;
goto v___jp_287_;
}
else
{
uint8_t v___x_304_; 
lean_inc_ref(v_msgData_186_);
v___x_304_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_186_);
v___y_288_ = v___x_304_;
goto v___jp_287_;
}
v___jp_194_:
{
lean_object* v___x_204_; lean_object* v_currNamespace_205_; lean_object* v_openDecls_206_; lean_object* v_env_207_; lean_object* v_nextMacroScope_208_; lean_object* v_ngen_209_; lean_object* v_auxDeclNGen_210_; lean_object* v_traceState_211_; lean_object* v_cache_212_; lean_object* v_messages_213_; lean_object* v_infoState_214_; lean_object* v_snapshotTasks_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_229_; 
v___x_204_ = lean_st_ref_take(v___y_203_);
v_currNamespace_205_ = lean_ctor_get(v___y_202_, 6);
v_openDecls_206_ = lean_ctor_get(v___y_202_, 7);
v_env_207_ = lean_ctor_get(v___x_204_, 0);
v_nextMacroScope_208_ = lean_ctor_get(v___x_204_, 1);
v_ngen_209_ = lean_ctor_get(v___x_204_, 2);
v_auxDeclNGen_210_ = lean_ctor_get(v___x_204_, 3);
v_traceState_211_ = lean_ctor_get(v___x_204_, 4);
v_cache_212_ = lean_ctor_get(v___x_204_, 5);
v_messages_213_ = lean_ctor_get(v___x_204_, 6);
v_infoState_214_ = lean_ctor_get(v___x_204_, 7);
v_snapshotTasks_215_ = lean_ctor_get(v___x_204_, 8);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_229_ == 0)
{
v___x_217_ = v___x_204_;
v_isShared_218_ = v_isSharedCheck_229_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snapshotTasks_215_);
lean_inc(v_infoState_214_);
lean_inc(v_messages_213_);
lean_inc(v_cache_212_);
lean_inc(v_traceState_211_);
lean_inc(v_auxDeclNGen_210_);
lean_inc(v_ngen_209_);
lean_inc(v_nextMacroScope_208_);
lean_inc(v_env_207_);
lean_dec(v___x_204_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_229_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
lean_inc(v_openDecls_206_);
lean_inc(v_currNamespace_205_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v_currNamespace_205_);
lean_ctor_set(v___x_219_, 1, v_openDecls_206_);
v___x_220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
lean_ctor_set(v___x_220_, 1, v___y_196_);
lean_inc_ref(v___y_198_);
lean_inc_ref(v___y_201_);
v___x_221_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_221_, 0, v___y_201_);
lean_ctor_set(v___x_221_, 1, v___y_197_);
lean_ctor_set(v___x_221_, 2, v___y_200_);
lean_ctor_set(v___x_221_, 3, v___y_198_);
lean_ctor_set(v___x_221_, 4, v___x_220_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*5, v___y_199_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*5 + 1, v___y_195_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*5 + 2, v_isSilent_188_);
v___x_222_ = l_Lean_MessageLog_add(v___x_221_, v_messages_213_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 6, v___x_222_);
v___x_224_ = v___x_217_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_env_207_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_nextMacroScope_208_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_ngen_209_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_auxDeclNGen_210_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_traceState_211_);
lean_ctor_set(v_reuseFailAlloc_228_, 5, v_cache_212_);
lean_ctor_set(v_reuseFailAlloc_228_, 6, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_228_, 7, v_infoState_214_);
lean_ctor_set(v_reuseFailAlloc_228_, 8, v_snapshotTasks_215_);
v___x_224_ = v_reuseFailAlloc_228_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_st_ref_set(v___y_203_, v___x_224_);
v___x_226_ = lean_box(0);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
}
v___jp_230_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_254_; 
v___x_239_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_186_);
v___x_240_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__3(v___x_239_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_254_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_inc_ref_n(v___y_233_, 2);
v___x_245_ = l_Lean_FileMap_toPosition(v___y_233_, v___y_235_);
lean_dec(v___y_235_);
v___x_246_ = l_Lean_FileMap_toPosition(v___y_233_, v___y_238_);
lean_dec(v___y_238_);
v___x_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
v___x_248_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___closed__0));
if (v___y_234_ == 0)
{
lean_del_object(v___x_243_);
lean_dec_ref(v___y_231_);
v___y_195_ = v___y_232_;
v___y_196_ = v_a_241_;
v___y_197_ = v___x_245_;
v___y_198_ = v___x_248_;
v___y_199_ = v___y_236_;
v___y_200_ = v___x_247_;
v___y_201_ = v___y_237_;
v___y_202_ = v___y_191_;
v___y_203_ = v___y_192_;
goto v___jp_194_;
}
else
{
uint8_t v___x_249_; 
lean_inc(v_a_241_);
v___x_249_ = l_Lean_MessageData_hasTag(v___y_231_, v_a_241_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_dec_ref_known(v___x_247_, 1);
lean_dec_ref(v___x_245_);
lean_dec(v_a_241_);
v___x_250_ = lean_box(0);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_250_);
v___x_252_ = v___x_243_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
else
{
lean_del_object(v___x_243_);
v___y_195_ = v___y_232_;
v___y_196_ = v_a_241_;
v___y_197_ = v___x_245_;
v___y_198_ = v___x_248_;
v___y_199_ = v___y_236_;
v___y_200_ = v___x_247_;
v___y_201_ = v___y_237_;
v___y_202_ = v___y_191_;
v___y_203_ = v___y_192_;
goto v___jp_194_;
}
}
}
}
v___jp_255_:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Syntax_getTailPos_x3f(v___y_261_, v___y_260_);
lean_dec(v___y_261_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_inc(v___y_263_);
v___y_231_ = v___y_256_;
v___y_232_ = v___y_257_;
v___y_233_ = v___y_258_;
v___y_234_ = v___y_259_;
v___y_235_ = v___y_263_;
v___y_236_ = v___y_260_;
v___y_237_ = v___y_262_;
v___y_238_ = v___y_263_;
goto v___jp_230_;
}
else
{
lean_object* v_val_265_; 
v_val_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v___x_264_, 1);
v___y_231_ = v___y_256_;
v___y_232_ = v___y_257_;
v___y_233_ = v___y_258_;
v___y_234_ = v___y_259_;
v___y_235_ = v___y_263_;
v___y_236_ = v___y_260_;
v___y_237_ = v___y_262_;
v___y_238_ = v_val_265_;
goto v___jp_230_;
}
}
v___jp_266_:
{
lean_object* v_ref_274_; lean_object* v___x_275_; 
v_ref_274_ = l_Lean_replaceRef(v_ref_185_, v___y_270_);
v___x_275_ = l_Lean_Syntax_getPos_x3f(v_ref_274_, v___y_271_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_276_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___y_256_ = v___y_267_;
v___y_257_ = v___y_273_;
v___y_258_ = v___y_268_;
v___y_259_ = v___y_269_;
v___y_260_ = v___y_271_;
v___y_261_ = v_ref_274_;
v___y_262_ = v___y_272_;
v___y_263_ = v___x_276_;
goto v___jp_255_;
}
else
{
lean_object* v_val_277_; 
v_val_277_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v___x_275_, 1);
v___y_256_ = v___y_267_;
v___y_257_ = v___y_273_;
v___y_258_ = v___y_268_;
v___y_259_ = v___y_269_;
v___y_260_ = v___y_271_;
v___y_261_ = v_ref_274_;
v___y_262_ = v___y_272_;
v___y_263_ = v_val_277_;
goto v___jp_255_;
}
}
v___jp_279_:
{
if (v___y_286_ == 0)
{
v___y_267_ = v___y_280_;
v___y_268_ = v___y_281_;
v___y_269_ = v___y_283_;
v___y_270_ = v___y_282_;
v___y_271_ = v___y_285_;
v___y_272_ = v___y_284_;
v___y_273_ = v_severity_187_;
goto v___jp_266_;
}
else
{
v___y_267_ = v___y_280_;
v___y_268_ = v___y_281_;
v___y_269_ = v___y_283_;
v___y_270_ = v___y_282_;
v___y_271_ = v___y_285_;
v___y_272_ = v___y_284_;
v___y_273_ = v___x_278_;
goto v___jp_266_;
}
}
v___jp_287_:
{
if (v___y_288_ == 0)
{
lean_object* v_fileName_289_; lean_object* v_fileMap_290_; lean_object* v_options_291_; lean_object* v_ref_292_; uint8_t v_suppressElabErrors_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___f_296_; uint8_t v___x_297_; uint8_t v___x_298_; 
v_fileName_289_ = lean_ctor_get(v___y_191_, 0);
v_fileMap_290_ = lean_ctor_get(v___y_191_, 1);
v_options_291_ = lean_ctor_get(v___y_191_, 2);
v_ref_292_ = lean_ctor_get(v___y_191_, 5);
v_suppressElabErrors_293_ = lean_ctor_get_uint8(v___y_191_, sizeof(void*)*14 + 1);
v___x_294_ = lean_box(v___y_288_);
v___x_295_ = lean_box(v_suppressElabErrors_293_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_296_, 0, v___x_294_);
lean_closure_set(v___f_296_, 1, v___x_295_);
v___x_297_ = 1;
v___x_298_ = l_Lean_instBEqMessageSeverity_beq(v_severity_187_, v___x_297_);
if (v___x_298_ == 0)
{
v___y_280_ = v___f_296_;
v___y_281_ = v_fileMap_290_;
v___y_282_ = v_ref_292_;
v___y_283_ = v_suppressElabErrors_293_;
v___y_284_ = v_fileName_289_;
v___y_285_ = v___y_288_;
v___y_286_ = v___x_298_;
goto v___jp_279_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = l_Lean_warningAsError;
v___x_300_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__4(v_options_291_, v___x_299_);
v___y_280_ = v___f_296_;
v___y_281_ = v_fileMap_290_;
v___y_282_ = v_ref_292_;
v___y_283_ = v_suppressElabErrors_293_;
v___y_284_ = v_fileName_289_;
v___y_285_ = v___y_288_;
v___y_286_ = v___x_300_;
goto v___jp_279_;
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref(v_msgData_186_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_305_, lean_object* v_msgData_306_, lean_object* v_severity_307_, lean_object* v_isSilent_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
uint8_t v_severity_boxed_314_; uint8_t v_isSilent_boxed_315_; lean_object* v_res_316_; 
v_severity_boxed_314_ = lean_unbox(v_severity_307_);
v_isSilent_boxed_315_ = lean_unbox(v_isSilent_308_);
v_res_316_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_305_, v_msgData_306_, v_severity_boxed_314_, v_isSilent_boxed_315_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v_ref_305_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(lean_object* v_msgData_317_, uint8_t v_severity_318_, uint8_t v_isSilent_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_ref_332_; lean_object* v___x_333_; 
v_ref_332_ = lean_ctor_get(v___y_329_, 5);
v___x_333_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_332_, v_msgData_317_, v_severity_318_, v_isSilent_319_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0___boxed(lean_object* v_msgData_334_, lean_object* v_severity_335_, lean_object* v_isSilent_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
uint8_t v_severity_boxed_349_; uint8_t v_isSilent_boxed_350_; lean_object* v_res_351_; 
v_severity_boxed_349_ = lean_unbox(v_severity_335_);
v_isSilent_boxed_350_ = lean_unbox(v_isSilent_336_);
v_res_351_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(v_msgData_334_, v_severity_boxed_349_, v_isSilent_boxed_350_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0(lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; 
v___x_365_ = 2;
v___x_366_ = 0;
v___x_367_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0(v_msgData_352_, v___x_365_, v___x_366_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0___boxed(lean_object* v_msgData_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0(v_msgData_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
return v_res_381_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__0));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
switch(lean_obj_tag(v_x_399_))
{
case 0:
{
lean_object* v_mvarId_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_434_; 
v_mvarId_425_ = lean_ctor_get(v_x_400_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v_x_400_, 0);
lean_dec(v_unused_435_);
v___x_427_ = v_x_400_;
v_isShared_428_ = v_isSharedCheck_434_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_mvarId_425_);
lean_dec(v_x_400_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_434_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_box(0);
if (v_isShared_428_ == 0)
{
lean_ctor_set_tag(v___x_427_, 1);
lean_ctor_set(v___x_427_, 1, v___x_429_);
lean_ctor_set(v___x_427_, 0, v_mvarId_425_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_mvarId_425_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_433_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
case 1:
{
uint8_t v_silent_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_silent_436_ = lean_ctor_get_uint8(v_x_399_, 0);
lean_dec_ref_known(v_x_399_, 0);
v___x_437_ = lean_st_ref_get(v_a_409_);
lean_inc_ref(v_x_400_);
v___x_438_ = l_Lean_Meta_Grind_Goal_grind(v_x_400_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_502_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_502_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_502_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_502_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
if (lean_obj_tag(v_a_439_) == 0)
{
lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_496_; 
lean_del_object(v___x_441_);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; 
v_unused_497_ = lean_ctor_get(v_a_439_, 0);
lean_dec(v_unused_497_);
v___x_444_ = v_a_439_;
v_isShared_445_ = v_isSharedCheck_496_;
goto v_resetjp_443_;
}
else
{
lean_dec(v_a_439_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_496_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v_mctx_447_; lean_object* v_cache_448_; lean_object* v_zetaDeltaFVarIds_449_; lean_object* v_postponed_450_; lean_object* v_diag_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_494_; 
v___x_446_ = lean_st_ref_take(v_a_409_);
v_mctx_447_ = lean_ctor_get(v___x_437_, 0);
lean_inc_ref(v_mctx_447_);
lean_dec(v___x_437_);
v_cache_448_ = lean_ctor_get(v___x_446_, 1);
v_zetaDeltaFVarIds_449_ = lean_ctor_get(v___x_446_, 2);
v_postponed_450_ = lean_ctor_get(v___x_446_, 3);
v_diag_451_ = lean_ctor_get(v___x_446_, 4);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_494_ == 0)
{
lean_object* v_unused_495_; 
v_unused_495_ = lean_ctor_get(v___x_446_, 0);
lean_dec(v_unused_495_);
v___x_453_ = v___x_446_;
v_isShared_454_ = v_isSharedCheck_494_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_diag_451_);
lean_inc(v_postponed_450_);
lean_inc(v_zetaDeltaFVarIds_449_);
lean_inc(v_cache_448_);
lean_dec(v___x_446_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_494_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v_mctx_447_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_mctx_447_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_cache_448_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_zetaDeltaFVarIds_449_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_postponed_450_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v_diag_451_);
v___x_456_ = v_reuseFailAlloc_493_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_st_ref_set(v_a_409_, v___x_456_);
if (v_silent_436_ == 0)
{
lean_object* v_mvarId_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v_mvarId_458_ = lean_ctor_get(v_x_400_, 1);
v___x_459_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__1);
lean_inc(v_mvarId_458_);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 0, v_mvarId_458_);
v___x_461_ = v___x_444_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_mvarId_458_);
v___x_461_ = v_reuseFailAlloc_492_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_462_ = l_Lean_indentD(v___x_461_);
v___x_463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_459_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_alloc_closure((void*)(l_Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0___boxed), 13, 1);
lean_closure_set(v___x_464_, 0, v___x_463_);
lean_inc(v_mvarId_458_);
v___x_465_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_458_, v___x_464_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; lean_object* v_specBackwardRuleCache_467_; lean_object* v_splitBackwardRuleCache_468_; lean_object* v_invariants_469_; lean_object* v_vcs_470_; lean_object* v_simpState_471_; lean_object* v_jps_472_; lean_object* v_fuel_473_; lean_object* v_inlineHandledInvariants_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref_known(v___x_465_, 1);
v___x_466_ = lean_st_ref_take(v_a_402_);
v_specBackwardRuleCache_467_ = lean_ctor_get(v___x_466_, 0);
v_splitBackwardRuleCache_468_ = lean_ctor_get(v___x_466_, 1);
v_invariants_469_ = lean_ctor_get(v___x_466_, 2);
v_vcs_470_ = lean_ctor_get(v___x_466_, 3);
v_simpState_471_ = lean_ctor_get(v___x_466_, 4);
v_jps_472_ = lean_ctor_get(v___x_466_, 5);
v_fuel_473_ = lean_ctor_get(v___x_466_, 6);
v_inlineHandledInvariants_474_ = lean_ctor_get(v___x_466_, 7);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_483_ == 0)
{
v___x_476_ = v___x_466_;
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_inlineHandledInvariants_474_);
lean_inc(v_fuel_473_);
lean_inc(v_jps_472_);
lean_inc(v_simpState_471_);
lean_inc(v_vcs_470_);
lean_inc(v_invariants_469_);
lean_inc(v_splitBackwardRuleCache_468_);
lean_inc(v_specBackwardRuleCache_467_);
lean_dec(v___x_466_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___x_478_; lean_object* v___x_480_; 
v___x_478_ = 1;
if (v_isShared_477_ == 0)
{
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_specBackwardRuleCache_467_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_splitBackwardRuleCache_468_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_invariants_469_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_vcs_470_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_simpState_471_);
lean_ctor_set(v_reuseFailAlloc_482_, 5, v_jps_472_);
lean_ctor_set(v_reuseFailAlloc_482_, 6, v_fuel_473_);
lean_ctor_set(v_reuseFailAlloc_482_, 7, v_inlineHandledInvariants_474_);
v___x_480_ = v_reuseFailAlloc_482_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; 
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*8, v___x_478_);
v___x_481_ = lean_st_ref_set(v_a_402_, v___x_480_);
goto v___jp_413_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v_x_400_);
v_a_484_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_465_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_465_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
else
{
lean_del_object(v___x_444_);
goto v___jp_413_;
}
}
}
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_dec(v___x_437_);
lean_dec_ref(v_x_400_);
v___x_498_ = lean_box(0);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_498_);
v___x_500_ = v___x_441_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v___x_437_);
lean_dec_ref(v_x_400_);
v_a_503_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_438_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_438_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
default: 
{
lean_object* v_tac_511_; lean_object* v_mvarId_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_tac_511_ = lean_ctor_get(v_x_399_, 0);
lean_inc(v_tac_511_);
lean_dec_ref_known(v_x_399_, 1);
v_mvarId_512_ = lean_ctor_get(v_x_400_, 1);
lean_inc(v_mvarId_512_);
lean_dec_ref(v_x_400_);
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__4));
v___x_514_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5));
v___x_515_ = l_Lean_Elab_runTactic(v_mvarId_512_, v_tac_511_, v___x_513_, v___x_514_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_524_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v_fst_520_; lean_object* v___x_522_; 
v_fst_520_ = lean_ctor_get(v_a_516_, 0);
lean_inc(v_fst_520_);
lean_dec(v_a_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v_fst_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_fst_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
v_a_525_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_515_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_515_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
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
}
v___jp_413_:
{
lean_object* v_mvarId_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_423_; 
v_mvarId_414_ = lean_ctor_get(v_x_400_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_x_400_, 0);
lean_dec(v_unused_424_);
v___x_416_ = v_x_400_;
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_mvarId_414_);
lean_dec(v_x_400_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_box(0);
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 1);
lean_ctor_set(v___x_416_, 1, v___x_418_);
lean_ctor_set(v___x_416_, 0, v_mvarId_414_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_mvarId_414_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_418_);
v___x_420_ = v_reuseFailAlloc_422_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; 
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___boxed(lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(v_x_533_, v_x_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2(lean_object* v_ref_548_, lean_object* v_msgData_549_, uint8_t v_severity_550_, uint8_t v_isSilent_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___redArg(v_ref_548_, v_msgData_549_, v_severity_550_, v_isSilent_551_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2___boxed(lean_object* v_ref_565_, lean_object* v_msgData_566_, lean_object* v_severity_567_, lean_object* v_isSilent_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v_severity_boxed_581_; uint8_t v_isSilent_boxed_582_; lean_object* v_res_583_; 
v_severity_boxed_581_ = lean_unbox(v_severity_567_);
v_isSilent_boxed_582_ = lean_unbox(v_isSilent_568_);
v_res_583_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2(v_ref_565_, v_msgData_566_, v_severity_boxed_581_, v_isSilent_boxed_582_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v_ref_565_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___redArg(lean_object* v_mvarId_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; lean_object* v_mctx_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_st_ref_get(v___y_585_);
v_mctx_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_mctx_588_);
lean_dec(v___x_587_);
v___x_589_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_588_, v_mvarId_584_);
lean_dec_ref(v_mctx_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___redArg___boxed(lean_object* v_mvarId_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___redArg(v_mvarId_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec(v_mvarId_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1(lean_object* v_mvarId_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___redArg(v_mvarId_595_, v___y_604_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___boxed(lean_object* v_mvarId_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1(v_mvarId_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v_mvarId_609_);
return v_res_622_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_keys_623_, lean_object* v_i_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_array_get_size(v_keys_623_);
v___x_627_ = lean_nat_dec_lt(v_i_624_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v_i_624_);
return v___x_627_;
}
else
{
lean_object* v_k_x27_628_; uint8_t v___x_629_; 
v_k_x27_628_ = lean_array_fget_borrowed(v_keys_623_, v_i_624_);
v___x_629_ = l_Lean_instBEqMVarId_beq(v_k_625_, v_k_x27_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_i_624_, v___x_630_);
lean_dec(v_i_624_);
v_i_624_ = v___x_631_;
goto _start;
}
else
{
lean_dec(v_i_624_);
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_keys_633_, lean_object* v_i_634_, lean_object* v_k_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_633_, v_i_634_, v_k_635_);
lean_dec(v_k_635_);
lean_dec_ref(v_keys_633_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; 
v___x_638_ = ((size_t)5ULL);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_shift_left(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_641_; size_t v___x_642_; size_t v___x_643_; 
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_643_ = lean_usize_sub(v___x_642_, v___x_641_);
return v___x_643_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg(lean_object* v_x_644_, size_t v_x_645_, lean_object* v_x_646_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_object* v_es_647_; lean_object* v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v_j_652_; lean_object* v___x_653_; 
v_es_647_ = lean_ctor_get(v_x_644_, 0);
v___x_648_ = lean_box(2);
v___x_649_ = ((size_t)5ULL);
v___x_650_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_651_ = lean_usize_land(v_x_645_, v___x_650_);
v_j_652_ = lean_usize_to_nat(v___x_651_);
v___x_653_ = lean_array_get_borrowed(v___x_648_, v_es_647_, v_j_652_);
lean_dec(v_j_652_);
switch(lean_obj_tag(v___x_653_))
{
case 0:
{
lean_object* v_key_654_; uint8_t v___x_655_; 
v_key_654_ = lean_ctor_get(v___x_653_, 0);
v___x_655_ = l_Lean_instBEqMVarId_beq(v_x_646_, v_key_654_);
return v___x_655_;
}
case 1:
{
lean_object* v_node_656_; size_t v___x_657_; 
v_node_656_ = lean_ctor_get(v___x_653_, 0);
v___x_657_ = lean_usize_shift_right(v_x_645_, v___x_649_);
v_x_644_ = v_node_656_;
v_x_645_ = v___x_657_;
goto _start;
}
default: 
{
uint8_t v___x_659_; 
v___x_659_ = 0;
return v___x_659_;
}
}
}
else
{
lean_object* v_ks_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_ks_660_ = lean_ctor_get(v_x_644_, 0);
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_660_, v___x_661_, v_x_646_);
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
size_t v_x_48391__boxed_666_; uint8_t v_res_667_; lean_object* v_r_668_; 
v_x_48391__boxed_666_ = lean_unbox_usize(v_x_664_);
lean_dec(v_x_664_);
v_res_667_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg(v_x_663_, v_x_48391__boxed_666_, v_x_665_);
lean_dec(v_x_665_);
lean_dec_ref(v_x_663_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___redArg(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
uint64_t v___x_671_; size_t v___x_672_; uint8_t v___x_673_; 
v___x_671_ = l_Lean_instHashableMVarId_hash(v_x_670_);
v___x_672_ = lean_uint64_to_usize(v___x_671_);
v___x_673_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg(v_x_669_, v___x_672_, v_x_670_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___redArg___boxed(lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___redArg(v_x_674_, v_x_675_);
lean_dec(v_x_675_);
lean_dec_ref(v_x_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___redArg(lean_object* v_mvarId_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; lean_object* v_mctx_682_; lean_object* v_eAssignment_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_681_ = lean_st_ref_get(v___y_679_);
v_mctx_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref(v_mctx_682_);
lean_dec(v___x_681_);
v_eAssignment_683_ = lean_ctor_get(v_mctx_682_, 8);
lean_inc_ref(v_eAssignment_683_);
lean_dec_ref(v_mctx_682_);
v___x_684_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___redArg(v_eAssignment_683_, v_mvarId_678_);
lean_dec_ref(v_eAssignment_683_);
v___x_685_ = lean_box(v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___redArg___boxed(lean_object* v_mvarId_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___redArg(v_mvarId_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec(v_mvarId_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8_spec__10___redArg(lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v_ks_695_; lean_object* v_vs_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_720_; 
v_ks_695_ = lean_ctor_get(v_x_691_, 0);
v_vs_696_ = lean_ctor_get(v_x_691_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_720_ == 0)
{
v___x_698_ = v_x_691_;
v_isShared_699_ = v_isSharedCheck_720_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_vs_696_);
lean_inc(v_ks_695_);
lean_dec(v_x_691_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_720_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_array_get_size(v_ks_695_);
v___x_701_ = lean_nat_dec_lt(v_x_692_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
lean_dec(v_x_692_);
v___x_702_ = lean_array_push(v_ks_695_, v_x_693_);
v___x_703_ = lean_array_push(v_vs_696_, v_x_694_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_703_);
lean_ctor_set(v___x_698_, 0, v___x_702_);
v___x_705_ = v___x_698_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v_k_x27_707_; uint8_t v___x_708_; 
v_k_x27_707_ = lean_array_fget_borrowed(v_ks_695_, v_x_692_);
v___x_708_ = l_Lean_instBEqMVarId_beq(v_x_693_, v_k_x27_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; 
if (v_isShared_699_ == 0)
{
v___x_710_ = v___x_698_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_ks_695_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_vs_696_);
v___x_710_ = v_reuseFailAlloc_714_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_add(v_x_692_, v___x_711_);
lean_dec(v_x_692_);
v_x_691_ = v___x_710_;
v_x_692_ = v___x_712_;
goto _start;
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_715_ = lean_array_fset(v_ks_695_, v_x_692_, v_x_693_);
v___x_716_ = lean_array_fset(v_vs_696_, v_x_692_, v_x_694_);
lean_dec(v_x_692_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_716_);
lean_ctor_set(v___x_698_, 0, v___x_715_);
v___x_718_ = v___x_698_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_n_721_, lean_object* v_k_722_, lean_object* v_v_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8_spec__10___redArg(v_n_721_, v___x_724_, v_k_722_, v_v_723_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg(lean_object* v_x_727_, size_t v_x_728_, size_t v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_727_) == 0)
{
lean_object* v_es_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; lean_object* v_j_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_es_732_ = lean_ctor_get(v_x_727_, 0);
v___x_733_ = ((size_t)5ULL);
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_736_ = lean_usize_land(v_x_728_, v___x_735_);
v_j_737_ = lean_usize_to_nat(v___x_736_);
v___x_738_ = lean_array_get_size(v_es_732_);
v___x_739_ = lean_nat_dec_lt(v_j_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_dec(v_j_737_);
lean_dec(v_x_731_);
lean_dec(v_x_730_);
return v_x_727_;
}
else
{
lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_776_; 
lean_inc_ref(v_es_732_);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_x_727_, 0);
lean_dec(v_unused_777_);
v___x_741_ = v_x_727_;
v_isShared_742_ = v_isSharedCheck_776_;
goto v_resetjp_740_;
}
else
{
lean_dec(v_x_727_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_776_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v_v_743_; lean_object* v___x_744_; lean_object* v_xs_x27_745_; lean_object* v___y_747_; 
v_v_743_ = lean_array_fget(v_es_732_, v_j_737_);
v___x_744_ = lean_box(0);
v_xs_x27_745_ = lean_array_fset(v_es_732_, v_j_737_, v___x_744_);
switch(lean_obj_tag(v_v_743_))
{
case 0:
{
lean_object* v_key_752_; lean_object* v_val_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_763_; 
v_key_752_ = lean_ctor_get(v_v_743_, 0);
v_val_753_ = lean_ctor_get(v_v_743_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_v_743_);
if (v_isSharedCheck_763_ == 0)
{
v___x_755_ = v_v_743_;
v_isShared_756_ = v_isSharedCheck_763_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_val_753_);
lean_inc(v_key_752_);
lean_dec(v_v_743_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_763_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
uint8_t v___x_757_; 
v___x_757_ = l_Lean_instBEqMVarId_beq(v_x_730_, v_key_752_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; 
lean_del_object(v___x_755_);
v___x_758_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_752_, v_val_753_, v_x_730_, v_x_731_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
v___y_747_ = v___x_759_;
goto v___jp_746_;
}
else
{
lean_object* v___x_761_; 
lean_dec(v_val_753_);
lean_dec(v_key_752_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v_x_731_);
lean_ctor_set(v___x_755_, 0, v_x_730_);
v___x_761_ = v___x_755_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_x_730_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_x_731_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
v___y_747_ = v___x_761_;
goto v___jp_746_;
}
}
}
}
case 1:
{
lean_object* v_node_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_774_; 
v_node_764_ = lean_ctor_get(v_v_743_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_v_743_);
if (v_isSharedCheck_774_ == 0)
{
v___x_766_ = v_v_743_;
v_isShared_767_ = v_isSharedCheck_774_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_node_764_);
lean_dec(v_v_743_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_774_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_768_ = lean_usize_shift_right(v_x_728_, v___x_733_);
v___x_769_ = lean_usize_add(v_x_729_, v___x_734_);
v___x_770_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg(v_node_764_, v___x_768_, v___x_769_, v_x_730_, v_x_731_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_770_);
v___x_772_ = v___x_766_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v___y_747_ = v___x_772_;
goto v___jp_746_;
}
}
}
default: 
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v_x_730_);
lean_ctor_set(v___x_775_, 1, v_x_731_);
v___y_747_ = v___x_775_;
goto v___jp_746_;
}
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_array_fset(v_xs_x27_745_, v_j_737_, v___y_747_);
lean_dec(v_j_737_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_748_);
v___x_750_ = v___x_741_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
else
{
lean_object* v_ks_778_; lean_object* v_vs_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_799_; 
v_ks_778_ = lean_ctor_get(v_x_727_, 0);
v_vs_779_ = lean_ctor_get(v_x_727_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_727_);
if (v_isSharedCheck_799_ == 0)
{
v___x_781_ = v_x_727_;
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_vs_779_);
lean_inc(v_ks_778_);
lean_dec(v_x_727_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_ks_778_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_vs_779_);
v___x_784_ = v_reuseFailAlloc_798_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v_newNode_785_; uint8_t v___y_787_; size_t v___x_793_; uint8_t v___x_794_; 
v_newNode_785_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8___redArg(v___x_784_, v_x_730_, v_x_731_);
v___x_793_ = ((size_t)7ULL);
v___x_794_ = lean_usize_dec_le(v___x_793_, v_x_729_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_785_);
v___x_796_ = lean_unsigned_to_nat(4u);
v___x_797_ = lean_nat_dec_lt(v___x_795_, v___x_796_);
lean_dec(v___x_795_);
v___y_787_ = v___x_797_;
goto v___jp_786_;
}
else
{
v___y_787_ = v___x_794_;
goto v___jp_786_;
}
v___jp_786_:
{
if (v___y_787_ == 0)
{
lean_object* v_ks_788_; lean_object* v_vs_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_ks_788_ = lean_ctor_get(v_newNode_785_, 0);
lean_inc_ref(v_ks_788_);
v_vs_789_ = lean_ctor_get(v_newNode_785_, 1);
lean_inc_ref(v_vs_789_);
lean_dec_ref(v_newNode_785_);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg___closed__0);
v___x_792_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___redArg(v_x_729_, v_ks_788_, v_vs_789_, v___x_790_, v___x_791_);
lean_dec_ref(v_vs_789_);
lean_dec_ref(v_ks_788_);
return v___x_792_;
}
else
{
return v_newNode_785_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___redArg(size_t v_depth_800_, lean_object* v_keys_801_, lean_object* v_vals_802_, lean_object* v_i_803_, lean_object* v_entries_804_){
_start:
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_array_get_size(v_keys_801_);
v___x_806_ = lean_nat_dec_lt(v_i_803_, v___x_805_);
if (v___x_806_ == 0)
{
lean_dec(v_i_803_);
return v_entries_804_;
}
else
{
lean_object* v_k_807_; lean_object* v_v_808_; uint64_t v___x_809_; size_t v_h_810_; size_t v___x_811_; lean_object* v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v_h_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_k_807_ = lean_array_fget_borrowed(v_keys_801_, v_i_803_);
v_v_808_ = lean_array_fget_borrowed(v_vals_802_, v_i_803_);
v___x_809_ = l_Lean_instHashableMVarId_hash(v_k_807_);
v_h_810_ = lean_uint64_to_usize(v___x_809_);
v___x_811_ = ((size_t)5ULL);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_sub(v_depth_800_, v___x_813_);
v___x_815_ = lean_usize_mul(v___x_811_, v___x_814_);
v_h_816_ = lean_usize_shift_right(v_h_810_, v___x_815_);
v___x_817_ = lean_nat_add(v_i_803_, v___x_812_);
lean_dec(v_i_803_);
lean_inc(v_v_808_);
lean_inc(v_k_807_);
v___x_818_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg(v_entries_804_, v_h_816_, v_depth_800_, v_k_807_, v_v_808_);
v_i_803_ = v___x_817_;
v_entries_804_ = v___x_818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_depth_820_, lean_object* v_keys_821_, lean_object* v_vals_822_, lean_object* v_i_823_, lean_object* v_entries_824_){
_start:
{
size_t v_depth_boxed_825_; lean_object* v_res_826_; 
v_depth_boxed_825_ = lean_unbox_usize(v_depth_820_);
lean_dec(v_depth_820_);
v_res_826_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___redArg(v_depth_boxed_825_, v_keys_821_, v_vals_822_, v_i_823_, v_entries_824_);
lean_dec_ref(v_vals_822_);
lean_dec_ref(v_keys_821_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
size_t v_x_48546__boxed_832_; size_t v_x_48547__boxed_833_; lean_object* v_res_834_; 
v_x_48546__boxed_832_ = lean_unbox_usize(v_x_828_);
lean_dec(v_x_828_);
v_x_48547__boxed_833_ = lean_unbox_usize(v_x_829_);
lean_dec(v_x_829_);
v_res_834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg(v_x_827_, v_x_48546__boxed_832_, v_x_48547__boxed_833_, v_x_830_, v_x_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3___redArg(lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
uint64_t v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v___x_838_ = l_Lean_instHashableMVarId_hash(v_x_836_);
v___x_839_ = lean_uint64_to_usize(v___x_838_);
v___x_840_ = ((size_t)1ULL);
v___x_841_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg(v_x_835_, v___x_839_, v___x_840_, v_x_836_, v_x_837_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___redArg(lean_object* v_mvarId_842_, lean_object* v_val_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___x_846_; lean_object* v_mctx_847_; lean_object* v_cache_848_; lean_object* v_zetaDeltaFVarIds_849_; lean_object* v_postponed_850_; lean_object* v_diag_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_879_; 
v___x_846_ = lean_st_ref_take(v___y_844_);
v_mctx_847_ = lean_ctor_get(v___x_846_, 0);
v_cache_848_ = lean_ctor_get(v___x_846_, 1);
v_zetaDeltaFVarIds_849_ = lean_ctor_get(v___x_846_, 2);
v_postponed_850_ = lean_ctor_get(v___x_846_, 3);
v_diag_851_ = lean_ctor_get(v___x_846_, 4);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_879_ == 0)
{
v___x_853_ = v___x_846_;
v_isShared_854_ = v_isSharedCheck_879_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_diag_851_);
lean_inc(v_postponed_850_);
lean_inc(v_zetaDeltaFVarIds_849_);
lean_inc(v_cache_848_);
lean_inc(v_mctx_847_);
lean_dec(v___x_846_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_879_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_depth_855_; lean_object* v_levelAssignDepth_856_; lean_object* v_lmvarCounter_857_; lean_object* v_mvarCounter_858_; lean_object* v_lDecls_859_; lean_object* v_decls_860_; lean_object* v_userNames_861_; lean_object* v_lAssignment_862_; lean_object* v_eAssignment_863_; lean_object* v_dAssignment_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_878_; 
v_depth_855_ = lean_ctor_get(v_mctx_847_, 0);
v_levelAssignDepth_856_ = lean_ctor_get(v_mctx_847_, 1);
v_lmvarCounter_857_ = lean_ctor_get(v_mctx_847_, 2);
v_mvarCounter_858_ = lean_ctor_get(v_mctx_847_, 3);
v_lDecls_859_ = lean_ctor_get(v_mctx_847_, 4);
v_decls_860_ = lean_ctor_get(v_mctx_847_, 5);
v_userNames_861_ = lean_ctor_get(v_mctx_847_, 6);
v_lAssignment_862_ = lean_ctor_get(v_mctx_847_, 7);
v_eAssignment_863_ = lean_ctor_get(v_mctx_847_, 8);
v_dAssignment_864_ = lean_ctor_get(v_mctx_847_, 9);
v_isSharedCheck_878_ = !lean_is_exclusive(v_mctx_847_);
if (v_isSharedCheck_878_ == 0)
{
v___x_866_ = v_mctx_847_;
v_isShared_867_ = v_isSharedCheck_878_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_dAssignment_864_);
lean_inc(v_eAssignment_863_);
lean_inc(v_lAssignment_862_);
lean_inc(v_userNames_861_);
lean_inc(v_decls_860_);
lean_inc(v_lDecls_859_);
lean_inc(v_mvarCounter_858_);
lean_inc(v_lmvarCounter_857_);
lean_inc(v_levelAssignDepth_856_);
lean_inc(v_depth_855_);
lean_dec(v_mctx_847_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_878_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3___redArg(v_eAssignment_863_, v_mvarId_842_, v_val_843_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 8, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_depth_855_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_levelAssignDepth_856_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_lmvarCounter_857_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_mvarCounter_858_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v_lDecls_859_);
lean_ctor_set(v_reuseFailAlloc_877_, 5, v_decls_860_);
lean_ctor_set(v_reuseFailAlloc_877_, 6, v_userNames_861_);
lean_ctor_set(v_reuseFailAlloc_877_, 7, v_lAssignment_862_);
lean_ctor_set(v_reuseFailAlloc_877_, 8, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_877_, 9, v_dAssignment_864_);
v___x_870_ = v_reuseFailAlloc_877_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_870_);
v___x_872_ = v___x_853_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_cache_848_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_zetaDeltaFVarIds_849_);
lean_ctor_set(v_reuseFailAlloc_876_, 3, v_postponed_850_);
lean_ctor_set(v_reuseFailAlloc_876_, 4, v_diag_851_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = lean_st_ref_set(v___y_844_, v___x_872_);
v___x_874_ = lean_box(0);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___redArg___boxed(lean_object* v_mvarId_880_, lean_object* v_val_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___redArg(v_mvarId_880_, v_val_881_, v___y_882_);
lean_dec(v___y_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1(lean_object* v___f_891_, lean_object* v_mv_892_, lean_object* v_tac_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_906_ = lean_box(0);
v___x_907_ = lean_box(0);
v___x_908_ = 1;
v___x_912_ = lean_box(1);
v___x_913_ = 0;
v___x_914_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__3));
v___x_915_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_915_, 0, v___x_906_);
lean_ctor_set(v___x_915_, 1, v___x_907_);
lean_ctor_set(v___x_915_, 2, v___x_906_);
lean_ctor_set(v___x_915_, 3, v___f_891_);
lean_ctor_set(v___x_915_, 4, v___x_912_);
lean_ctor_set(v___x_915_, 5, v___x_912_);
lean_ctor_set(v___x_915_, 6, v___x_906_);
lean_ctor_set(v___x_915_, 7, v___x_914_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8, v___x_908_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 1, v___x_908_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 2, v___x_908_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 3, v___x_908_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 4, v___x_913_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 5, v___x_913_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 6, v___x_913_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 7, v___x_913_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 8, v___x_908_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 9, v___x_913_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*8 + 10, v___x_908_);
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__5));
lean_inc(v_mv_892_);
v___x_917_ = l_Lean_Elab_runTactic(v_mv_892_, v_tac_893_, v___x_915_, v___x_916_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref_known(v___x_917_, 1);
v___x_918_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___redArg(v_mv_892_, v___y_902_);
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_952_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_952_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_952_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
uint8_t v___x_923_; 
v___x_923_ = lean_unbox(v_a_919_);
lean_dec(v_a_919_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_926_; 
lean_dec(v_mv_892_);
v___x_924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___closed__1));
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
else
{
lean_object* v___x_928_; lean_object* v_a_929_; 
lean_del_object(v___x_921_);
v___x_928_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__1___redArg(v_mv_892_, v___y_902_);
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
if (lean_obj_tag(v_a_929_) == 1)
{
lean_object* v_val_930_; lean_object* v___x_931_; 
v_val_930_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v_a_929_, 1);
v___x_931_ = l_Lean_Meta_Sym_unfoldReducible(v_val_930_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_932_, v___y_900_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v___x_935_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___redArg(v_mv_892_, v_a_934_, v___y_902_);
lean_dec_ref(v___x_935_);
goto v___jp_909_;
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_mv_892_);
v_a_936_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_933_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec(v_mv_892_);
v_a_944_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_931_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_931_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_dec(v_a_929_);
lean_dec(v_mv_892_);
goto v___jp_909_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_mv_892_);
v_a_953_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_917_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_917_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
v___jp_909_:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___closed__0));
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1___boxed(lean_object* v___f_961_, lean_object* v_mv_962_, lean_object* v_tac_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1(v___f_961_, v_mv_962_, v_tac_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___redArg(lean_object* v_a_977_, lean_object* v_x_978_){
_start:
{
if (lean_obj_tag(v_x_978_) == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_box(0);
return v___x_979_;
}
else
{
lean_object* v_key_980_; lean_object* v_value_981_; lean_object* v_tail_982_; uint8_t v___x_983_; 
v_key_980_ = lean_ctor_get(v_x_978_, 0);
v_value_981_ = lean_ctor_get(v_x_978_, 1);
v_tail_982_ = lean_ctor_get(v_x_978_, 2);
v___x_983_ = lean_nat_dec_eq(v_key_980_, v_a_977_);
if (v___x_983_ == 0)
{
v_x_978_ = v_tail_982_;
goto _start;
}
else
{
lean_object* v___x_985_; 
lean_inc(v_value_981_);
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v_value_981_);
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___redArg___boxed(lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___redArg(v_a_986_, v_x_987_);
lean_dec(v_x_987_);
lean_dec(v_a_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___redArg(lean_object* v_m_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_buckets_991_; lean_object* v___x_992_; uint64_t v___x_993_; uint64_t v___x_994_; uint64_t v___x_995_; uint64_t v_fold_996_; uint64_t v___x_997_; uint64_t v___x_998_; uint64_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_buckets_991_ = lean_ctor_get(v_m_989_, 1);
v___x_992_ = lean_array_get_size(v_buckets_991_);
v___x_993_ = lean_uint64_of_nat(v_a_990_);
v___x_994_ = 32ULL;
v___x_995_ = lean_uint64_shift_right(v___x_993_, v___x_994_);
v_fold_996_ = lean_uint64_xor(v___x_993_, v___x_995_);
v___x_997_ = 16ULL;
v___x_998_ = lean_uint64_shift_right(v_fold_996_, v___x_997_);
v___x_999_ = lean_uint64_xor(v_fold_996_, v___x_998_);
v___x_1000_ = lean_uint64_to_usize(v___x_999_);
v___x_1001_ = lean_usize_of_nat(v___x_992_);
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_sub(v___x_1001_, v___x_1002_);
v___x_1004_ = lean_usize_land(v___x_1000_, v___x_1003_);
v___x_1005_ = lean_array_uget_borrowed(v_buckets_991_, v___x_1004_);
v___x_1006_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___redArg(v_a_990_, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___redArg___boxed(lean_object* v_m_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___redArg(v_m_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_m_1007_);
return v_res_1009_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__20(void){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Array_mkArray0(lean_box(0));
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant(lean_object* v_n_1072_, lean_object* v_mv_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___y_1087_; uint8_t v___y_1088_; lean_object* v___y_1093_; lean_object* v_invariantAlts_1106_; lean_object* v___x_1107_; 
v_invariantAlts_1106_ = lean_ctor_get(v_a_1074_, 19);
v___x_1107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___redArg(v_invariantAlts_1106_, v_n_1072_);
if (lean_obj_tag(v___x_1107_) == 1)
{
lean_object* v_val_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1179_; 
v_val_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1179_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_val_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1179_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___f_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___f_1112_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run___closed__2));
v___x_1113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__3));
lean_inc(v_val_1108_);
v___x_1114_ = l_Lean_Syntax_isOfKind(v_val_1108_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__5));
lean_inc(v_val_1108_);
v___x_1116_ = l_Lean_Syntax_isOfKind(v_val_1108_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
lean_dec(v_val_1108_);
lean_dec(v_mv_1073_);
v___x_1117_ = lean_box(v___x_1116_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1117_);
v___x_1119_ = v___x_1110_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = l_Lean_Syntax_getArg(v_val_1108_, v___x_1121_);
v___x_1123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__7));
lean_inc(v___x_1122_);
v___x_1124_ = l_Lean_Syntax_isOfKind(v___x_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_dec(v___x_1122_);
lean_dec(v_val_1108_);
lean_dec(v_mv_1073_);
v___x_1125_ = lean_box(v___x_1124_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1125_);
v___x_1127_ = v___x_1110_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
lean_object* v_ref_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_del_object(v___x_1110_);
v_ref_1129_ = lean_ctor_get(v_a_1083_, 5);
v___x_1130_ = l_Lean_Syntax_getArg(v___x_1122_, v___x_1121_);
lean_dec(v___x_1122_);
v___x_1131_ = lean_unsigned_to_nat(3u);
v___x_1132_ = l_Lean_Syntax_getArg(v_val_1108_, v___x_1131_);
lean_dec(v_val_1108_);
v___x_1133_ = l_Lean_Syntax_getArgs(v___x_1130_);
lean_dec(v___x_1130_);
v___x_1134_ = l_Lean_SourceInfo_fromRef(v_ref_1129_, v___x_1114_);
v___x_1135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__9));
v___x_1136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__10));
lean_inc_n(v___x_1134_, 11);
v___x_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1134_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__12));
v___x_1139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__14));
v___x_1140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__16));
v___x_1141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__18));
v___x_1142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__19));
v___x_1143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1134_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__20, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__20_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__20);
v___x_1145_ = l_Array_append___redArg(v___x_1144_, v___x_1133_);
lean_dec_ref(v___x_1133_);
v___x_1146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1134_);
lean_ctor_set(v___x_1146_, 1, v___x_1140_);
lean_ctor_set(v___x_1146_, 2, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_node2(v___x_1134_, v___x_1141_, v___x_1143_, v___x_1146_);
v___x_1148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__21));
v___x_1149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1134_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__22));
v___x_1151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23));
v___x_1152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1134_);
lean_ctor_set(v___x_1152_, 1, v___x_1150_);
v___x_1153_ = l_Lean_Syntax_node2(v___x_1134_, v___x_1151_, v___x_1152_, v___x_1132_);
v___x_1154_ = l_Lean_Syntax_node3(v___x_1134_, v___x_1140_, v___x_1147_, v___x_1149_, v___x_1153_);
v___x_1155_ = l_Lean_Syntax_node1(v___x_1134_, v___x_1139_, v___x_1154_);
v___x_1156_ = l_Lean_Syntax_node1(v___x_1134_, v___x_1138_, v___x_1155_);
v___x_1157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__24));
v___x_1158_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1134_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_Syntax_node3(v___x_1134_, v___x_1135_, v___x_1137_, v___x_1156_, v___x_1158_);
v___x_1160_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1(v___f_1112_, v_mv_1073_, v___x_1159_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
v___y_1093_ = v___x_1160_;
goto v___jp_1092_;
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = l_Lean_Syntax_getArg(v_val_1108_, v___x_1161_);
v___x_1163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__26));
v___x_1164_ = l_Lean_Syntax_isOfKind(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
lean_dec(v_val_1108_);
lean_dec(v_mv_1073_);
v___x_1165_ = lean_box(v___x_1164_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1165_);
v___x_1167_ = v___x_1110_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
else
{
lean_object* v_ref_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_del_object(v___x_1110_);
v_ref_1169_ = lean_ctor_get(v_a_1083_, 5);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = l_Lean_Syntax_getArg(v_val_1108_, v___x_1170_);
lean_dec(v_val_1108_);
v___x_1172_ = 0;
v___x_1173_ = l_Lean_SourceInfo_fromRef(v_ref_1169_, v___x_1172_);
v___x_1174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__22));
v___x_1175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___closed__23));
lean_inc(v___x_1173_);
v___x_1176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1173_);
lean_ctor_set(v___x_1176_, 1, v___x_1174_);
v___x_1177_ = l_Lean_Syntax_node2(v___x_1173_, v___x_1175_, v___x_1176_, v___x_1171_);
v___x_1178_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___lam__1(v___f_1112_, v_mv_1073_, v___x_1177_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
v___y_1093_ = v___x_1178_;
goto v___jp_1092_;
}
}
}
}
else
{
uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v___x_1107_);
lean_dec(v_mv_1073_);
v___x_1180_ = 0;
v___x_1181_ = lean_box(v___x_1180_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
v___jp_1086_:
{
if (v___y_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref(v___y_1087_);
v___x_1089_ = lean_box(v___y_1088_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___y_1087_);
return v___x_1091_;
}
}
v___jp_1092_:
{
if (lean_obj_tag(v___y_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
v_a_1094_ = lean_ctor_get(v___y_1093_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___y_1093_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v___y_1093_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___y_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_a_1098_; lean_object* v___x_1100_; 
v_a_1098_ = lean_ctor_get(v_a_1094_, 0);
lean_inc(v_a_1098_);
lean_dec(v_a_1094_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v_a_1098_);
v___x_1100_ = v___x_1096_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_object* v_a_1103_; uint8_t v___x_1104_; 
v_a_1103_ = lean_ctor_get(v___y_1093_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___y_1093_, 1);
v___x_1104_ = l_Lean_Exception_isInterrupt(v_a_1103_);
if (v___x_1104_ == 0)
{
uint8_t v___x_1105_; 
lean_inc(v_a_1103_);
v___x_1105_ = l_Lean_Exception_isRuntime(v_a_1103_);
v___y_1087_ = v_a_1103_;
v___y_1088_ = v___x_1105_;
goto v___jp_1086_;
}
else
{
v___y_1087_ = v_a_1103_;
v___y_1088_ = v___x_1104_;
goto v___jp_1086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant___boxed(lean_object* v_n_1183_, lean_object* v_mv_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant(v_n_1183_, v_mv_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_n_1183_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0(lean_object* v_mvarId_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___redArg(v_mvarId_1198_, v___y_1207_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0___boxed(lean_object* v_mvarId_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0(v_mvarId_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v_mvarId_1212_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2(lean_object* v_mvarId_1226_, lean_object* v_val_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___redArg(v_mvarId_1226_, v_val_1227_, v___y_1236_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2___boxed(lean_object* v_mvarId_1241_, lean_object* v_val_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2(v_mvarId_1241_, v_val_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3(lean_object* v_00_u03b2_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___redArg(v_m_1257_, v_a_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3___boxed(lean_object* v_00_u03b2_1260_, lean_object* v_m_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3(v_00_u03b2_1260_, v_m_1261_, v_a_1262_);
lean_dec(v_a_1262_);
lean_dec_ref(v_m_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0(lean_object* v_00_u03b2_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
uint8_t v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___redArg(v_x_1265_, v_x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0(v_00_u03b2_1268_, v_x_1269_, v_x_1270_);
lean_dec(v_x_1270_);
lean_dec_ref(v_x_1269_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3(lean_object* v_00_u03b2_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3___redArg(v_x_1274_, v_x_1275_, v_x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5(lean_object* v_00_u03b2_1278_, lean_object* v_a_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___redArg(v_a_1279_, v_x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1282_, lean_object* v_a_1283_, lean_object* v_x_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__3_spec__5(v_00_u03b2_1282_, v_a_1283_, v_x_1284_);
lean_dec(v_x_1284_);
lean_dec(v_a_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, size_t v_x_1288_, lean_object* v_x_1289_){
_start:
{
uint8_t v___x_1290_; 
v___x_1290_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___redArg(v_x_1287_, v_x_1288_, v_x_1289_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
size_t v_x_49474__boxed_1295_; uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_x_49474__boxed_1295_ = lean_unbox_usize(v_x_1293_);
lean_dec(v_x_1293_);
v_res_1296_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2(v_00_u03b2_1291_, v_x_1292_, v_x_49474__boxed_1295_, v_x_1294_);
lean_dec(v_x_1294_);
lean_dec_ref(v_x_1292_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1298_, lean_object* v_x_1299_, size_t v_x_1300_, size_t v_x_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___redArg(v_x_1299_, v_x_1300_, v_x_1301_, v_x_1302_, v_x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1305_, lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_){
_start:
{
size_t v_x_49485__boxed_1311_; size_t v_x_49486__boxed_1312_; lean_object* v_res_1313_; 
v_x_49485__boxed_1311_ = lean_unbox_usize(v_x_1307_);
lean_dec(v_x_1307_);
v_x_49486__boxed_1312_ = lean_unbox_usize(v_x_1308_);
lean_dec(v_x_1308_);
v_res_1313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5(v_00_u03b2_1305_, v_x_1306_, v_x_49485__boxed_1311_, v_x_49486__boxed_1312_, v_x_1309_, v_x_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1314_, lean_object* v_keys_1315_, lean_object* v_vals_1316_, lean_object* v_heq_1317_, lean_object* v_i_1318_, lean_object* v_k_1319_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_1315_, v_i_1318_, v_k_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1321_, lean_object* v_keys_1322_, lean_object* v_vals_1323_, lean_object* v_heq_1324_, lean_object* v_i_1325_, lean_object* v_k_1326_){
_start:
{
uint8_t v_res_1327_; lean_object* v_r_1328_; 
v_res_1327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1321_, v_keys_1322_, v_vals_1323_, v_heq_1324_, v_i_1325_, v_k_1326_);
lean_dec(v_k_1326_);
lean_dec_ref(v_vals_1323_);
lean_dec_ref(v_keys_1322_);
v_r_1328_ = lean_box(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1329_, lean_object* v_n_1330_, lean_object* v_k_1331_, lean_object* v_v_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8___redArg(v_n_1330_, v_k_1331_, v_v_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03b2_1334_, size_t v_depth_1335_, lean_object* v_keys_1336_, lean_object* v_vals_1337_, lean_object* v_heq_1338_, lean_object* v_i_1339_, lean_object* v_entries_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___redArg(v_depth_1335_, v_keys_1336_, v_vals_1337_, v_i_1339_, v_entries_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1342_, lean_object* v_depth_1343_, lean_object* v_keys_1344_, lean_object* v_vals_1345_, lean_object* v_heq_1346_, lean_object* v_i_1347_, lean_object* v_entries_1348_){
_start:
{
size_t v_depth_boxed_1349_; lean_object* v_res_1350_; 
v_depth_boxed_1349_ = lean_unbox_usize(v_depth_1343_);
lean_dec(v_depth_1343_);
v_res_1350_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__9(v_00_u03b2_1342_, v_depth_boxed_1349_, v_keys_1344_, v_vals_1345_, v_heq_1346_, v_i_1347_, v_entries_1348_);
lean_dec_ref(v_vals_1345_);
lean_dec_ref(v_keys_1344_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8_spec__10(lean_object* v_00_u03b2_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__2_spec__3_spec__5_spec__8_spec__10___redArg(v_x_1352_, v_x_1353_, v_x_1354_, v_x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(lean_object* v_a_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
uint8_t v___x_1359_; 
v___x_1359_ = 0;
return v___x_1359_;
}
else
{
lean_object* v_key_1360_; lean_object* v_tail_1361_; uint8_t v___x_1362_; 
v_key_1360_ = lean_ctor_get(v_x_1358_, 0);
v_tail_1361_ = lean_ctor_get(v_x_1358_, 2);
v___x_1362_ = lean_nat_dec_eq(v_key_1360_, v_a_1357_);
if (v___x_1362_ == 0)
{
v_x_1358_ = v_tail_1361_;
goto _start;
}
else
{
return v___x_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg___boxed(lean_object* v_a_1364_, lean_object* v_x_1365_){
_start:
{
uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1364_, v_x_1365_);
lean_dec(v_x_1365_);
lean_dec(v_a_1364_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 0)
{
return v_x_1368_;
}
else
{
lean_object* v_key_1370_; lean_object* v_value_1371_; lean_object* v_tail_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1395_; 
v_key_1370_ = lean_ctor_get(v_x_1369_, 0);
v_value_1371_ = lean_ctor_get(v_x_1369_, 1);
v_tail_1372_ = lean_ctor_get(v_x_1369_, 2);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_x_1369_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1374_ = v_x_1369_;
v_isShared_1375_ = v_isSharedCheck_1395_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_tail_1372_);
lean_inc(v_value_1371_);
lean_inc(v_key_1370_);
lean_dec(v_x_1369_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1395_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; uint64_t v___x_1377_; uint64_t v___x_1378_; uint64_t v___x_1379_; uint64_t v_fold_1380_; uint64_t v___x_1381_; uint64_t v___x_1382_; uint64_t v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; size_t v___x_1386_; size_t v___x_1387_; size_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1376_ = lean_array_get_size(v_x_1368_);
v___x_1377_ = lean_uint64_of_nat(v_key_1370_);
v___x_1378_ = 32ULL;
v___x_1379_ = lean_uint64_shift_right(v___x_1377_, v___x_1378_);
v_fold_1380_ = lean_uint64_xor(v___x_1377_, v___x_1379_);
v___x_1381_ = 16ULL;
v___x_1382_ = lean_uint64_shift_right(v_fold_1380_, v___x_1381_);
v___x_1383_ = lean_uint64_xor(v_fold_1380_, v___x_1382_);
v___x_1384_ = lean_uint64_to_usize(v___x_1383_);
v___x_1385_ = lean_usize_of_nat(v___x_1376_);
v___x_1386_ = ((size_t)1ULL);
v___x_1387_ = lean_usize_sub(v___x_1385_, v___x_1386_);
v___x_1388_ = lean_usize_land(v___x_1384_, v___x_1387_);
v___x_1389_ = lean_array_uget_borrowed(v_x_1368_, v___x_1388_);
lean_inc(v___x_1389_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 2, v___x_1389_);
v___x_1391_ = v___x_1374_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_key_1370_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_value_1371_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_array_uset(v_x_1368_, v___x_1388_, v___x_1391_);
v_x_1368_ = v___x_1392_;
v_x_1369_ = v_tail_1372_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(lean_object* v_i_1396_, lean_object* v_source_1397_, lean_object* v_target_1398_){
_start:
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_array_get_size(v_source_1397_);
v___x_1400_ = lean_nat_dec_lt(v_i_1396_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_dec_ref(v_source_1397_);
lean_dec(v_i_1396_);
return v_target_1398_;
}
else
{
lean_object* v_es_1401_; lean_object* v___x_1402_; lean_object* v_source_1403_; lean_object* v_target_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_es_1401_ = lean_array_fget(v_source_1397_, v_i_1396_);
v___x_1402_ = lean_box(0);
v_source_1403_ = lean_array_fset(v_source_1397_, v_i_1396_, v___x_1402_);
v_target_1404_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_target_1398_, v_es_1401_);
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_nat_add(v_i_1396_, v___x_1405_);
lean_dec(v_i_1396_);
v_i_1396_ = v___x_1406_;
v_source_1397_ = v_source_1403_;
v_target_1398_ = v_target_1404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(lean_object* v_data_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_nbuckets_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1409_ = lean_array_get_size(v_data_1408_);
v___x_1410_ = lean_unsigned_to_nat(2u);
v_nbuckets_1411_ = lean_nat_mul(v___x_1409_, v___x_1410_);
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_mk_array(v_nbuckets_1411_, v___x_1413_);
v___x_1415_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v___x_1412_, v_data_1408_, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(lean_object* v_m_1416_, lean_object* v_a_1417_, lean_object* v_b_1418_){
_start:
{
lean_object* v_size_1419_; lean_object* v_buckets_1420_; lean_object* v___x_1421_; uint64_t v___x_1422_; uint64_t v___x_1423_; uint64_t v___x_1424_; uint64_t v_fold_1425_; uint64_t v___x_1426_; uint64_t v___x_1427_; uint64_t v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; size_t v___x_1431_; size_t v___x_1432_; size_t v___x_1433_; lean_object* v_bkt_1434_; uint8_t v___x_1435_; 
v_size_1419_ = lean_ctor_get(v_m_1416_, 0);
v_buckets_1420_ = lean_ctor_get(v_m_1416_, 1);
v___x_1421_ = lean_array_get_size(v_buckets_1420_);
v___x_1422_ = lean_uint64_of_nat(v_a_1417_);
v___x_1423_ = 32ULL;
v___x_1424_ = lean_uint64_shift_right(v___x_1422_, v___x_1423_);
v_fold_1425_ = lean_uint64_xor(v___x_1422_, v___x_1424_);
v___x_1426_ = 16ULL;
v___x_1427_ = lean_uint64_shift_right(v_fold_1425_, v___x_1426_);
v___x_1428_ = lean_uint64_xor(v_fold_1425_, v___x_1427_);
v___x_1429_ = lean_uint64_to_usize(v___x_1428_);
v___x_1430_ = lean_usize_of_nat(v___x_1421_);
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_sub(v___x_1430_, v___x_1431_);
v___x_1433_ = lean_usize_land(v___x_1429_, v___x_1432_);
v_bkt_1434_ = lean_array_uget_borrowed(v_buckets_1420_, v___x_1433_);
v___x_1435_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1417_, v_bkt_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1456_; 
lean_inc_ref(v_buckets_1420_);
lean_inc(v_size_1419_);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_m_1416_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1457_ = lean_ctor_get(v_m_1416_, 1);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_m_1416_, 0);
lean_dec(v_unused_1458_);
v___x_1437_ = v_m_1416_;
v_isShared_1438_ = v_isSharedCheck_1456_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v_m_1416_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1456_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v_size_x27_1440_; lean_object* v___x_1441_; lean_object* v_buckets_x27_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1439_ = lean_unsigned_to_nat(1u);
v_size_x27_1440_ = lean_nat_add(v_size_1419_, v___x_1439_);
lean_dec(v_size_1419_);
lean_inc(v_bkt_1434_);
v___x_1441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1441_, 0, v_a_1417_);
lean_ctor_set(v___x_1441_, 1, v_b_1418_);
lean_ctor_set(v___x_1441_, 2, v_bkt_1434_);
v_buckets_x27_1442_ = lean_array_uset(v_buckets_1420_, v___x_1433_, v___x_1441_);
v___x_1443_ = lean_unsigned_to_nat(4u);
v___x_1444_ = lean_nat_mul(v_size_x27_1440_, v___x_1443_);
v___x_1445_ = lean_unsigned_to_nat(3u);
v___x_1446_ = lean_nat_div(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_array_get_size(v_buckets_x27_1442_);
v___x_1448_ = lean_nat_dec_le(v___x_1446_, v___x_1447_);
lean_dec(v___x_1446_);
if (v___x_1448_ == 0)
{
lean_object* v_val_1449_; lean_object* v___x_1451_; 
v_val_1449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_buckets_x27_1442_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v_val_1449_);
lean_ctor_set(v___x_1437_, 0, v_size_x27_1440_);
v___x_1451_ = v___x_1437_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_size_x27_1440_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_val_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
lean_object* v___x_1454_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v_buckets_x27_1442_);
lean_ctor_set(v___x_1437_, 0, v_size_x27_1440_);
v___x_1454_ = v___x_1437_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_size_x27_1440_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_buckets_x27_1442_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_dec(v_b_1418_);
lean_dec(v_a_1417_);
return v_m_1416_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(lean_object* v___x_1459_, lean_object* v_as_x27_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
if (lean_obj_tag(v_as_x27_1460_) == 0)
{
lean_object* v___x_1474_; 
lean_dec_ref(v___x_1459_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_b_1461_);
return v___x_1474_;
}
else
{
lean_object* v_head_1475_; lean_object* v_tail_1476_; lean_object* v___x_1477_; 
v_head_1475_ = lean_ctor_get(v_as_x27_1460_, 0);
v_tail_1476_ = lean_ctor_get(v_as_x27_1460_, 1);
lean_inc(v_head_1475_);
v___x_1477_ = l_Lean_MVarId_getType(v_head_1475_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; uint8_t v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
lean_inc_ref(v___x_1459_);
v___x_1479_ = l_Lean_Elab_Tactic_Do_SpecAttr_isSpecInvariantType(v___x_1459_, v_a_1478_);
lean_dec(v_a_1478_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_inc(v_head_1475_);
v___x_1480_ = lean_array_push(v_b_1461_, v_head_1475_);
v_as_x27_1460_ = v_tail_1476_;
v_b_1461_ = v___x_1480_;
goto _start;
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_specBackwardRuleCache_1484_; lean_object* v_splitBackwardRuleCache_1485_; lean_object* v_invariants_1486_; lean_object* v_vcs_1487_; lean_object* v_simpState_1488_; lean_object* v_jps_1489_; lean_object* v_fuel_1490_; lean_object* v_inlineHandledInvariants_1491_; uint8_t v_preTacFailed_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1548_; 
v___x_1482_ = lean_st_ref_get(v___y_1463_);
v___x_1483_ = lean_st_ref_take(v___y_1463_);
v_specBackwardRuleCache_1484_ = lean_ctor_get(v___x_1483_, 0);
v_splitBackwardRuleCache_1485_ = lean_ctor_get(v___x_1483_, 1);
v_invariants_1486_ = lean_ctor_get(v___x_1483_, 2);
v_vcs_1487_ = lean_ctor_get(v___x_1483_, 3);
v_simpState_1488_ = lean_ctor_get(v___x_1483_, 4);
v_jps_1489_ = lean_ctor_get(v___x_1483_, 5);
v_fuel_1490_ = lean_ctor_get(v___x_1483_, 6);
v_inlineHandledInvariants_1491_ = lean_ctor_get(v___x_1483_, 7);
v_preTacFailed_1492_ = lean_ctor_get_uint8(v___x_1483_, sizeof(void*)*8);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1494_ = v___x_1483_;
v_isShared_1495_ = v_isSharedCheck_1548_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_inlineHandledInvariants_1491_);
lean_inc(v_fuel_1490_);
lean_inc(v_jps_1489_);
lean_inc(v_simpState_1488_);
lean_inc(v_vcs_1487_);
lean_inc(v_invariants_1486_);
lean_inc(v_splitBackwardRuleCache_1485_);
lean_inc(v_specBackwardRuleCache_1484_);
lean_dec(v___x_1483_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1548_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
lean_inc(v_head_1475_);
v___x_1496_ = lean_array_push(v_invariants_1486_, v_head_1475_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 2, v___x_1496_);
v___x_1498_ = v___x_1494_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_specBackwardRuleCache_1484_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_splitBackwardRuleCache_1485_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_vcs_1487_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_simpState_1488_);
lean_ctor_set(v_reuseFailAlloc_1547_, 5, v_jps_1489_);
lean_ctor_set(v_reuseFailAlloc_1547_, 6, v_fuel_1490_);
lean_ctor_set(v_reuseFailAlloc_1547_, 7, v_inlineHandledInvariants_1491_);
lean_ctor_set_uint8(v_reuseFailAlloc_1547_, sizeof(void*)*8, v_preTacFailed_1492_);
v___x_1498_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v_invariants_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1499_ = lean_st_ref_set(v___y_1463_, v___x_1498_);
v_invariants_1500_ = lean_ctor_get(v___x_1482_, 2);
lean_inc_ref(v_invariants_1500_);
lean_dec(v___x_1482_);
v___x_1501_ = lean_array_get_size(v_invariants_1500_);
lean_dec_ref(v_invariants_1500_);
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_add(v___x_1501_, v___x_1502_);
lean_inc(v_head_1475_);
v___x_1504_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant(v___x_1503_, v_head_1475_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; uint8_t v___x_1506_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = lean_unbox(v_a_1505_);
lean_dec(v_a_1505_);
if (v___x_1506_ == 0)
{
uint8_t v___x_1507_; lean_object* v___x_1508_; 
lean_dec(v___x_1503_);
v___x_1507_ = 2;
lean_inc(v_head_1475_);
v___x_1508_ = l_Lean_MVarId_setKind___redArg(v_head_1475_, v___x_1507_, v___y_1470_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_dec_ref_known(v___x_1508_, 1);
v_as_x27_1460_ = v_tail_1476_;
goto _start;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_b_1461_);
lean_dec_ref(v___x_1459_);
v_a_1510_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1508_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1508_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v_specBackwardRuleCache_1519_; lean_object* v_splitBackwardRuleCache_1520_; lean_object* v_invariants_1521_; lean_object* v_vcs_1522_; lean_object* v_simpState_1523_; lean_object* v_jps_1524_; lean_object* v_fuel_1525_; lean_object* v_inlineHandledInvariants_1526_; uint8_t v_preTacFailed_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1538_; 
v___x_1518_ = lean_st_ref_take(v___y_1463_);
v_specBackwardRuleCache_1519_ = lean_ctor_get(v___x_1518_, 0);
v_splitBackwardRuleCache_1520_ = lean_ctor_get(v___x_1518_, 1);
v_invariants_1521_ = lean_ctor_get(v___x_1518_, 2);
v_vcs_1522_ = lean_ctor_get(v___x_1518_, 3);
v_simpState_1523_ = lean_ctor_get(v___x_1518_, 4);
v_jps_1524_ = lean_ctor_get(v___x_1518_, 5);
v_fuel_1525_ = lean_ctor_get(v___x_1518_, 6);
v_inlineHandledInvariants_1526_ = lean_ctor_get(v___x_1518_, 7);
v_preTacFailed_1527_ = lean_ctor_get_uint8(v___x_1518_, sizeof(void*)*8);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1529_ = v___x_1518_;
v_isShared_1530_ = v_isSharedCheck_1538_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_inlineHandledInvariants_1526_);
lean_inc(v_fuel_1525_);
lean_inc(v_jps_1524_);
lean_inc(v_simpState_1523_);
lean_inc(v_vcs_1522_);
lean_inc(v_invariants_1521_);
lean_inc(v_splitBackwardRuleCache_1520_);
lean_inc(v_specBackwardRuleCache_1519_);
lean_dec(v___x_1518_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1538_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1531_ = lean_box(0);
v___x_1532_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_inlineHandledInvariants_1526_, v___x_1503_, v___x_1531_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 7, v___x_1532_);
v___x_1534_ = v___x_1529_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_specBackwardRuleCache_1519_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_splitBackwardRuleCache_1520_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_invariants_1521_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_vcs_1522_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_simpState_1523_);
lean_ctor_set(v_reuseFailAlloc_1537_, 5, v_jps_1524_);
lean_ctor_set(v_reuseFailAlloc_1537_, 6, v_fuel_1525_);
lean_ctor_set(v_reuseFailAlloc_1537_, 7, v___x_1532_);
lean_ctor_set_uint8(v_reuseFailAlloc_1537_, sizeof(void*)*8, v_preTacFailed_1527_);
v___x_1534_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_st_ref_set(v___y_1463_, v___x_1534_);
v_as_x27_1460_ = v_tail_1476_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v___x_1503_);
lean_dec_ref(v_b_1461_);
lean_dec_ref(v___x_1459_);
v_a_1539_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1504_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1504_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v_b_1461_);
lean_dec_ref(v___x_1459_);
v_a_1549_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1477_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1477_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg___boxed(lean_object* v___x_1557_, lean_object* v_as_x27_1558_, lean_object* v_b_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1557_, v_as_x27_1558_, v_b_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_as_x27_1558_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(lean_object* v_subgoals_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
lean_object* v___x_1588_; lean_object* v_env_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1588_ = lean_st_ref_get(v_a_1586_);
v_env_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc_ref(v_env_1589_);
lean_dec(v___x_1588_);
v___x_1590_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_1591_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v_env_1589_, v_subgoals_1575_, v___x_1590_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___boxed(lean_object* v_subgoals_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec_ref(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
lean_dec(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_subgoals_1592_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0(lean_object* v_00_u03b2_1606_, lean_object* v_m_1607_, lean_object* v_a_1608_, lean_object* v_b_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0___redArg(v_m_1607_, v_a_1608_, v_b_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(lean_object* v___x_1611_, lean_object* v_as_1612_, lean_object* v_as_x27_1613_, lean_object* v_b_1614_, lean_object* v_a_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___redArg(v___x_1611_, v_as_x27_1613_, v_b_1614_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1___boxed(lean_object** _args){
lean_object* v___x_1629_ = _args[0];
lean_object* v_as_1630_ = _args[1];
lean_object* v_as_x27_1631_ = _args[2];
lean_object* v_b_1632_ = _args[3];
lean_object* v_a_1633_ = _args[4];
lean_object* v___y_1634_ = _args[5];
lean_object* v___y_1635_ = _args[6];
lean_object* v___y_1636_ = _args[7];
lean_object* v___y_1637_ = _args[8];
lean_object* v___y_1638_ = _args[9];
lean_object* v___y_1639_ = _args[10];
lean_object* v___y_1640_ = _args[11];
lean_object* v___y_1641_ = _args[12];
lean_object* v___y_1642_ = _args[13];
lean_object* v___y_1643_ = _args[14];
lean_object* v___y_1644_ = _args[15];
lean_object* v___y_1645_ = _args[16];
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__1(v___x_1629_, v_as_1630_, v_as_x27_1631_, v_b_1632_, v_a_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_as_x27_1631_);
lean_dec(v_as_1630_);
return v_res_1646_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(lean_object* v_00_u03b2_1647_, lean_object* v_a_1648_, lean_object* v_x_1649_){
_start:
{
uint8_t v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___redArg(v_a_1648_, v_x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_a_1652_, lean_object* v_x_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__0(v_00_u03b2_1651_, v_a_1652_, v_x_1653_);
lean_dec(v_x_1653_);
lean_dec(v_a_1652_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1(lean_object* v_00_u03b2_1656_, lean_object* v_data_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1___redArg(v_data_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1659_, lean_object* v_i_1660_, lean_object* v_source_1661_, lean_object* v_target_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2___redArg(v_i_1660_, v_source_1661_, v_target_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1664_, lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals_spec__0_spec__1_spec__2_spec__4___redArg(v_x_1665_, v_x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(lean_object* v_as_x27_1668_, lean_object* v_b_1669_, lean_object* v___y_1670_){
_start:
{
if (lean_obj_tag(v_as_x27_1668_) == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v_b_1669_);
return v___x_1672_;
}
else
{
lean_object* v_head_1673_; lean_object* v_tail_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; 
v_head_1673_ = lean_ctor_get(v_as_x27_1668_, 0);
v_tail_1674_ = lean_ctor_get(v_as_x27_1668_, 1);
v___x_1675_ = 2;
lean_inc(v_head_1673_);
v___x_1676_ = l_Lean_MVarId_setKind___redArg(v_head_1673_, v___x_1675_, v___y_1670_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1677_; 
lean_dec_ref_known(v___x_1676_, 1);
lean_inc(v_head_1673_);
v___x_1677_ = lean_array_push(v_b_1669_, v_head_1673_);
v_as_x27_1668_ = v_tail_1674_;
v_b_1669_ = v___x_1677_;
goto _start;
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v_b_1669_);
v_a_1679_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1676_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1676_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg___boxed(lean_object* v_as_x27_1687_, lean_object* v_b_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(v_as_x27_1687_, v_b_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec(v_as_x27_1687_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(lean_object* v_goal_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_preTac_1705_; uint8_t v_trivial_1706_; lean_object* v___x_1707_; 
v_preTac_1705_ = lean_ctor_get(v_a_1693_, 18);
v_trivial_1706_ = lean_ctor_get_uint8(v_a_1693_, sizeof(void*)*20);
v___x_1707_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(v_preTac_1705_, v_goal_1692_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; lean_object* v_mvarId_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
if (v_trivial_1706_ == 0)
{
lean_object* v_mvarId_1780_; 
v_mvarId_1780_ = lean_ctor_get(v_a_1708_, 1);
lean_inc(v_mvarId_1780_);
v_mvarId_1711_ = v_mvarId_1780_;
v___y_1712_ = v_a_1693_;
v___y_1713_ = v_a_1694_;
v___y_1714_ = v_a_1695_;
v___y_1715_ = v_a_1696_;
v___y_1716_ = v_a_1697_;
v___y_1717_ = v_a_1698_;
v___y_1718_ = v_a_1699_;
v___y_1719_ = v_a_1700_;
v___y_1720_ = v_a_1701_;
v___y_1721_ = v_a_1702_;
v___y_1722_ = v_a_1703_;
goto v___jp_1710_;
}
else
{
lean_object* v_mvarId_1781_; lean_object* v___x_1782_; 
v_mvarId_1781_ = lean_ctor_get(v_a_1708_, 1);
lean_inc(v_mvarId_1781_);
v___x_1782_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(v_mvarId_1781_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1792_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1792_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1792_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
if (lean_obj_tag(v_a_1783_) == 1)
{
lean_object* v_val_1787_; 
lean_del_object(v___x_1785_);
v_val_1787_ = lean_ctor_get(v_a_1783_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v_a_1783_, 1);
v_mvarId_1711_ = v_val_1787_;
v___y_1712_ = v_a_1693_;
v___y_1713_ = v_a_1694_;
v___y_1714_ = v_a_1695_;
v___y_1715_ = v_a_1696_;
v___y_1716_ = v_a_1697_;
v___y_1717_ = v_a_1698_;
v___y_1718_ = v_a_1699_;
v___y_1719_ = v_a_1700_;
v___y_1720_ = v_a_1701_;
v___y_1721_ = v_a_1702_;
v___y_1722_ = v_a_1703_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
lean_dec(v_a_1783_);
lean_dec(v_a_1708_);
v___x_1788_ = lean_box(0);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1788_);
v___x_1790_ = v___x_1785_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1708_);
v_a_1793_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1782_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1782_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
v___jp_1710_:
{
lean_object* v_toGoalState_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1778_; 
v_toGoalState_1723_ = lean_ctor_get(v_a_1708_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_a_1708_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v_a_1708_, 1);
lean_dec(v_unused_1779_);
v___x_1725_ = v_a_1708_;
v_isShared_1726_ = v_isSharedCheck_1778_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_toGoalState_1723_);
lean_dec(v_a_1708_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1778_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_preTac_1727_; lean_object* v___x_1729_; 
v_preTac_1727_ = lean_ctor_get(v___y_1712_, 18);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 1, v_mvarId_1711_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_toGoalState_1723_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_mvarId_1711_);
v___x_1729_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; 
lean_inc(v_preTac_1727_);
v___x_1730_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run(v_preTac_1727_, v___x_1729_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1732_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(v_a_1731_, v___x_1709_, v___y_1720_);
lean_dec(v_a_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1760_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1760_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1760_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v_specBackwardRuleCache_1738_; lean_object* v_splitBackwardRuleCache_1739_; lean_object* v_invariants_1740_; lean_object* v_vcs_1741_; lean_object* v_simpState_1742_; lean_object* v_jps_1743_; lean_object* v_fuel_1744_; lean_object* v_inlineHandledInvariants_1745_; uint8_t v_preTacFailed_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1759_; 
v___x_1737_ = lean_st_ref_take(v___y_1713_);
v_specBackwardRuleCache_1738_ = lean_ctor_get(v___x_1737_, 0);
v_splitBackwardRuleCache_1739_ = lean_ctor_get(v___x_1737_, 1);
v_invariants_1740_ = lean_ctor_get(v___x_1737_, 2);
v_vcs_1741_ = lean_ctor_get(v___x_1737_, 3);
v_simpState_1742_ = lean_ctor_get(v___x_1737_, 4);
v_jps_1743_ = lean_ctor_get(v___x_1737_, 5);
v_fuel_1744_ = lean_ctor_get(v___x_1737_, 6);
v_inlineHandledInvariants_1745_ = lean_ctor_get(v___x_1737_, 7);
v_preTacFailed_1746_ = lean_ctor_get_uint8(v___x_1737_, sizeof(void*)*8);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1748_ = v___x_1737_;
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_inlineHandledInvariants_1745_);
lean_inc(v_fuel_1744_);
lean_inc(v_jps_1743_);
lean_inc(v_simpState_1742_);
lean_inc(v_vcs_1741_);
lean_inc(v_invariants_1740_);
lean_inc(v_splitBackwardRuleCache_1739_);
lean_inc(v_specBackwardRuleCache_1738_);
lean_dec(v___x_1737_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = l_Array_append___redArg(v_vcs_1741_, v_a_1733_);
lean_dec(v_a_1733_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 3, v___x_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_specBackwardRuleCache_1738_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_splitBackwardRuleCache_1739_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_invariants_1740_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_simpState_1742_);
lean_ctor_set(v_reuseFailAlloc_1758_, 5, v_jps_1743_);
lean_ctor_set(v_reuseFailAlloc_1758_, 6, v_fuel_1744_);
lean_ctor_set(v_reuseFailAlloc_1758_, 7, v_inlineHandledInvariants_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1758_, sizeof(void*)*8, v_preTacFailed_1746_);
v___x_1752_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1753_ = lean_st_ref_set(v___y_1713_, v___x_1752_);
v___x_1754_ = lean_box(0);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1754_);
v___x_1756_ = v___x_1735_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1732_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1732_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
v_a_1769_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1730_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1730_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1707_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1707_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC___boxed(lean_object* v_goal_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v_goal_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec_ref(v_a_1810_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0(lean_object* v_as_1823_, lean_object* v_as_x27_1824_, lean_object* v_b_1825_, lean_object* v_a_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___redArg(v_as_x27_1824_, v_b_1825_, v___y_1835_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0___boxed(lean_object* v_as_1840_, lean_object* v_as_x27_1841_, lean_object* v_b_1842_, lean_object* v_a_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_emitVC_spec__0(v_as_1840_, v_as_x27_1841_, v_b_1842_, v_a_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_as_x27_1841_);
lean_dec(v_as_1840_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(lean_object* v_msg_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_ref_1863_; lean_object* v___x_1864_; lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1873_; 
v_ref_1863_ = lean_ctor_get(v___y_1860_, 5);
v___x_1864_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__0_spec__0_spec__2_spec__3(v_msg_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1873_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_inc(v_ref_1863_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_ref_1863_);
lean_ctor_set(v___x_1869_, 1, v_a_1865_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 1);
lean_ctor_set(v___x_1867_, 0, v___x_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg___boxed(lean_object* v_msg_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(v_msg_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(lean_object* v_00_u03b1_1881_, lean_object* v_msg_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(v_msg_1882_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_msg_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0(v_00_u03b1_1896_, v_msg_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(lean_object* v_goal_1911_, size_t v_sz_1912_, size_t v_i_1913_, lean_object* v_bs_1914_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_lt(v_i_1913_, v_sz_1912_);
if (v___x_1915_ == 0)
{
return v_bs_1914_;
}
else
{
lean_object* v_toGoalState_1916_; lean_object* v_v_1917_; lean_object* v___x_1918_; lean_object* v_bs_x27_1919_; lean_object* v___x_1920_; size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v_toGoalState_1916_ = lean_ctor_get(v_goal_1911_, 0);
v_v_1917_ = lean_array_uget(v_bs_1914_, v_i_1913_);
v___x_1918_ = lean_unsigned_to_nat(0u);
v_bs_x27_1919_ = lean_array_uset(v_bs_1914_, v_i_1913_, v___x_1918_);
lean_inc_ref(v_toGoalState_1916_);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_toGoalState_1916_);
lean_ctor_set(v___x_1920_, 1, v_v_1917_);
v___x_1921_ = ((size_t)1ULL);
v___x_1922_ = lean_usize_add(v_i_1913_, v___x_1921_);
v___x_1923_ = lean_array_uset(v_bs_x27_1919_, v_i_1913_, v___x_1920_);
v_i_1913_ = v___x_1922_;
v_bs_1914_ = v___x_1923_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3___boxed(lean_object* v_goal_1925_, lean_object* v_sz_1926_, lean_object* v_i_1927_, lean_object* v_bs_1928_){
_start:
{
size_t v_sz_boxed_1929_; size_t v_i_boxed_1930_; lean_object* v_res_1931_; 
v_sz_boxed_1929_ = lean_unbox_usize(v_sz_1926_);
lean_dec(v_sz_1926_);
v_i_boxed_1930_ = lean_unbox_usize(v_i_1927_);
lean_dec(v_i_1927_);
v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(v_goal_1925_, v_sz_boxed_1929_, v_i_boxed_1930_, v_bs_1928_);
lean_dec_ref(v_goal_1925_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(lean_object* v_a_1932_, lean_object* v___x_1933_, lean_object* v_goal_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; size_t v_sz_1948_; size_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1947_ = l_Array_reverse___redArg(v_a_1932_);
v_sz_1948_ = lean_array_size(v___x_1947_);
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__3(v_goal_1934_, v_sz_1948_, v___x_1949_, v___x_1947_);
v___x_1951_ = l_Array_append___redArg(v___x_1933_, v___x_1950_);
lean_dec_ref(v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2___boxed(lean_object* v_a_1954_, lean_object* v___x_1955_, lean_object* v_goal_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_1954_, v___x_1955_, v_goal_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
lean_dec_ref(v_goal_1956_);
return v_res_1969_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__0));
v___x_1972_ = l_Lean_stringToMessageData(v___x_1971_);
return v___x_1972_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__2));
v___x_1975_ = l_Lean_stringToMessageData(v___x_1974_);
return v___x_1975_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__4));
v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__6));
v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2(lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
if (lean_obj_tag(v_a_1982_) == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = l_List_reverse___redArg(v_a_1983_);
return v___x_1984_;
}
else
{
lean_object* v_head_1985_; lean_object* v_tail_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2014_; 
v_head_1985_ = lean_ctor_get(v_a_1982_, 0);
v_tail_1986_ = lean_ctor_get(v_a_1982_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_a_1982_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1988_ = v_a_1982_;
v_isShared_1989_ = v_isSharedCheck_2014_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_tail_1986_);
lean_inc(v_head_1985_);
lean_dec(v_a_1982_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2014_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___y_1991_; 
switch(lean_obj_tag(v_head_1985_))
{
case 0:
{
lean_object* v_declName_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v_declName_1996_ = lean_ctor_get(v_head_1985_, 0);
lean_inc(v_declName_1996_);
lean_dec_ref_known(v_head_1985_, 1);
v___x_1997_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__1);
v___x_1998_ = l_Lean_MessageData_ofName(v_declName_1996_);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1997_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___y_1991_ = v___x_1999_;
goto v___jp_1990_;
}
case 1:
{
lean_object* v_fvarId_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_fvarId_2000_ = lean_ctor_get(v_head_1985_, 0);
lean_inc(v_fvarId_2000_);
lean_dec_ref_known(v_head_1985_, 1);
v___x_2001_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__3);
v___x_2002_ = l_Lean_mkFVar(v_fvarId_2000_);
v___x_2003_ = l_Lean_MessageData_ofExpr(v___x_2002_);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2001_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___y_1991_ = v___x_2004_;
goto v___jp_1990_;
}
default: 
{
lean_object* v_ref_2005_; lean_object* v_proof_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_ref_2005_ = lean_ctor_get(v_head_1985_, 1);
lean_inc(v_ref_2005_);
v_proof_2006_ = lean_ctor_get(v_head_1985_, 2);
lean_inc_ref(v_proof_2006_);
lean_dec_ref_known(v_head_1985_, 3);
v___x_2007_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__5);
v___x_2008_ = l_Lean_MessageData_ofSyntax(v_ref_2005_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7, &l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7_once, _init_l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2___closed__7);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = l_Lean_MessageData_ofExpr(v_proof_2006_);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___y_1991_ = v___x_2013_;
goto v___jp_1990_;
}
}
v___jp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v_a_1983_);
lean_ctor_set(v___x_1988_, 0, v___y_1991_);
v___x_1993_ = v___x_1988_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___y_1991_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_a_1983_);
v___x_1993_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
v_a_1982_ = v_tail_1986_;
v_a_1983_ = v___x_1993_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(size_t v_sz_2015_, size_t v_i_2016_, lean_object* v_bs_2017_){
_start:
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_usize_dec_lt(v_i_2016_, v_sz_2015_);
if (v___x_2018_ == 0)
{
return v_bs_2017_;
}
else
{
lean_object* v_v_2019_; lean_object* v_proof_2020_; lean_object* v___x_2021_; lean_object* v_bs_x27_2022_; size_t v___x_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v_v_2019_ = lean_array_uget_borrowed(v_bs_2017_, v_i_2016_);
v_proof_2020_ = lean_ctor_get(v_v_2019_, 1);
lean_inc_ref(v_proof_2020_);
v___x_2021_ = lean_unsigned_to_nat(0u);
v_bs_x27_2022_ = lean_array_uset(v_bs_2017_, v_i_2016_, v___x_2021_);
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_2016_, v___x_2023_);
v___x_2025_ = lean_array_uset(v_bs_x27_2022_, v_i_2016_, v_proof_2020_);
v_i_2016_ = v___x_2024_;
v_bs_2017_ = v___x_2025_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1___boxed(lean_object* v_sz_2027_, lean_object* v_i_2028_, lean_object* v_bs_2029_){
_start:
{
size_t v_sz_boxed_2030_; size_t v_i_boxed_2031_; lean_object* v_res_2032_; 
v_sz_boxed_2030_ = lean_unbox_usize(v_sz_2027_);
lean_dec(v_sz_2027_);
v_i_boxed_2031_ = lean_unbox_usize(v_i_2028_);
lean_dec(v_i_2028_);
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_sz_boxed_2030_, v_i_boxed_2031_, v_bs_2029_);
return v_res_2032_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__0));
v___x_2035_ = l_Lean_stringToMessageData(v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__2));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__4));
v___x_2041_ = l_Lean_stringToMessageData(v___x_2040_);
return v___x_2041_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__6));
v___x_2044_ = l_Lean_stringToMessageData(v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__8));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1(uint8_t v___x_2048_, lean_object* v_monad_2049_, lean_object* v_e_2050_, lean_object* v_thms_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
if (v___x_2048_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; size_t v_sz_2073_; size_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2064_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__1);
v___x_2065_ = l_Lean_MessageData_ofExpr(v_monad_2049_);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__3);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2066_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = l_Lean_MessageData_ofExpr(v_e_2050_);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__5);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v_sz_2073_ = lean_array_size(v_thms_2051_);
v___x_2074_ = ((size_t)0ULL);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__1(v_sz_2073_, v___x_2074_, v_thms_2051_);
v___x_2076_ = lean_array_to_list(v___x_2075_);
v___x_2077_ = lean_box(0);
v___x_2078_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__2(v___x_2076_, v___x_2077_);
v___x_2079_ = l_Lean_MessageData_ofList(v___x_2078_);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2072_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(v___x_2082_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref(v_thms_2051_);
lean_dec_ref(v_monad_2049_);
v___x_2084_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__9);
v___x_2085_ = l_Lean_MessageData_ofExpr(v_e_2050_);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___closed__7);
v___x_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___redArg(v___x_2088_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___boxed(lean_object* v___x_2090_, lean_object* v_monad_2091_, lean_object* v_e_2092_, lean_object* v_thms_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v___x_78618__boxed_2106_; lean_object* v_res_2107_; 
v___x_78618__boxed_2106_ = lean_unbox(v___x_2090_);
v_res_2107_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1(v___x_78618__boxed_2106_, v_monad_2091_, v_e_2092_, v_thms_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(lean_object* v___x_2108_, lean_object* v___x_2109_, lean_object* v_target_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v___x_2108_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2123_, 0);
lean_dec(v_unused_2132_);
v___x_2125_ = v___x_2123_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_dec(v___x_2123_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2109_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v___x_2109_);
v_a_2133_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2123_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2123_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0___boxed(lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v_target_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(v___x_2141_, v___x_2142_, v_target_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec_ref(v_target_2143_);
return v_res_2156_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__0));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(lean_object* v_a_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___y_2174_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2194_ = lean_array_get_size(v_a_2160_);
v___x_2195_ = lean_unsigned_to_nat(1u);
v___x_2196_ = lean_nat_sub(v___x_2194_, v___x_2195_);
v___x_2197_ = lean_nat_dec_lt(v___x_2196_, v___x_2194_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2198_, 0, v_a_2160_);
return v___x_2198_;
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_2162_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2201_ = lean_array_fget(v_a_2160_, v___x_2196_);
lean_dec(v___x_2196_);
v___x_2202_ = lean_array_pop(v_a_2160_);
v___x_2203_ = lean_unbox(v_a_2200_);
lean_dec(v_a_2200_);
if (v___x_2203_ == 0)
{
lean_object* v_mvarId_2204_; lean_object* v___x_2205_; 
v_mvarId_2204_ = lean_ctor_get(v___x_2201_, 1);
lean_inc(v_mvarId_2204_);
v___x_2205_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_mvarId_2204_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
switch(lean_obj_tag(v_a_2206_))
{
case 2:
{
lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2227_; 
lean_inc(v_mvarId_2204_);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2228_ = lean_ctor_get(v___x_2201_, 1);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v___x_2201_, 0);
lean_dec(v_unused_2229_);
v___x_2208_ = v___x_2201_;
v_isShared_2209_ = v_isSharedCheck_2227_;
goto v_resetjp_2207_;
}
else
{
lean_dec(v___x_2201_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2227_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_e_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v_e_2210_ = lean_ctor_get(v_a_2206_, 0);
lean_inc_ref(v_e_2210_);
lean_dec_ref_known(v_a_2206_, 1);
v___x_2211_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1, &l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1_once, _init_l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___closed__1);
v___x_2212_ = l_Lean_MessageData_ofExpr(v_e_2210_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set_tag(v___x_2208_, 7);
lean_ctor_set(v___x_2208_, 1, v___x_2212_);
lean_ctor_set(v___x_2208_, 0, v___x_2211_);
v___x_2214_ = v___x_2208_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_alloc_closure((void*)(l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__0___boxed), 14, 2);
lean_closure_set(v___x_2215_, 0, lean_box(0));
lean_closure_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_2204_, v___x_2215_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_dec_ref_known(v___x_2216_, 1);
v_a_2160_ = v___x_2202_;
goto _start;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v___x_2202_);
v_a_2218_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2216_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2216_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
case 3:
{
uint8_t v_errorOnMissingSpec_2230_; 
v_errorOnMissingSpec_2230_ = lean_ctor_get_uint8(v___y_2161_, sizeof(void*)*20 + 2);
if (v_errorOnMissingSpec_2230_ == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref_known(v_a_2206_, 3);
v___x_2231_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v___x_2201_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_dec_ref_known(v___x_2231_, 1);
v_a_2160_ = v___x_2202_;
goto _start;
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v___x_2202_);
v_a_2233_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2231_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2231_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
else
{
lean_object* v_e_2241_; lean_object* v_monad_2242_; lean_object* v_thms_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___y_2248_; lean_object* v___x_2249_; 
lean_inc(v_mvarId_2204_);
lean_dec(v___x_2201_);
v_e_2241_ = lean_ctor_get(v_a_2206_, 0);
lean_inc_ref(v_e_2241_);
v_monad_2242_ = lean_ctor_get(v_a_2206_, 1);
lean_inc_ref(v_monad_2242_);
v_thms_2243_ = lean_ctor_get(v_a_2206_, 2);
lean_inc_ref(v_thms_2243_);
lean_dec_ref_known(v_a_2206_, 3);
v___x_2244_ = lean_array_get_size(v_thms_2243_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_nat_dec_eq(v___x_2244_, v___x_2245_);
v___x_2247_ = lean_box(v___x_2246_);
v___y_2248_ = lean_alloc_closure((void*)(l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__1___boxed), 16, 4);
lean_closure_set(v___y_2248_, 0, v___x_2247_);
lean_closure_set(v___y_2248_, 1, v_monad_2242_);
lean_closure_set(v___y_2248_, 2, v_e_2241_);
lean_closure_set(v___y_2248_, 3, v_thms_2243_);
v___x_2249_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_run_spec__1___redArg(v_mvarId_2204_, v___y_2248_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_dec_ref_known(v___x_2249_, 1);
v_a_2160_ = v___x_2202_;
goto _start;
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref(v___x_2202_);
v_a_2251_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2249_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2249_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
case 4:
{
lean_object* v_subgoals_2259_; lean_object* v___x_2260_; 
v_subgoals_2259_ = lean_ctor_get(v_a_2206_, 0);
lean_inc(v_subgoals_2259_);
lean_dec_ref_known(v_a_2206_, 1);
v___x_2260_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals(v_subgoals_2259_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v_subgoals_2259_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
v___x_2262_ = lean_array_get_size(v_a_2261_);
v___x_2263_ = lean_nat_dec_lt(v___x_2195_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
v___x_2264_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_2261_, v___x_2202_, v___x_2201_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___x_2201_);
v___y_2174_ = v___x_2264_;
goto v___jp_2173_;
}
else
{
lean_object* v_preTac_2265_; lean_object* v___x_2266_; 
v_preTac_2265_ = lean_ctor_get(v___y_2161_, 18);
v___x_2266_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(v_preTac_2265_, v___x_2201_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__2(v_a_2261_, v___x_2202_, v_a_2267_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v_a_2267_);
v___y_2174_ = v___x_2268_;
goto v___jp_2173_;
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_a_2261_);
lean_dec_ref(v___x_2202_);
v_a_2269_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2266_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2266_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v___x_2202_);
lean_dec(v___x_2201_);
v_a_2277_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2260_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2260_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
default: 
{
lean_object* v_target_2285_; lean_object* v___x_2286_; 
v_target_2285_ = lean_ctor_get(v_a_2206_, 0);
lean_inc_ref(v_target_2285_);
lean_dec(v_a_2206_);
v___x_2286_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___lam__0(v___x_2201_, v___x_2202_, v_target_2285_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec_ref(v_target_2285_);
v___y_2174_ = v___x_2286_;
goto v___jp_2173_;
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v___x_2202_);
lean_dec(v___x_2201_);
v_a_2287_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2205_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2205_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
else
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_emitVC(v___x_2201_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_dec_ref_known(v___x_2295_, 1);
v_a_2160_ = v___x_2202_;
goto _start;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec_ref(v___x_2202_);
v_a_2297_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2295_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v___x_2196_);
lean_dec_ref(v_a_2160_);
v_a_2305_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2199_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2199_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
v___jp_2173_:
{
if (lean_obj_tag(v___y_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2185_; 
v_a_2175_ = lean_ctor_get(v___y_2174_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___y_2174_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2177_ = v___y_2174_;
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___y_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2185_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
if (lean_obj_tag(v_a_2175_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; 
v_a_2179_ = lean_ctor_get(v_a_2175_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v_a_2175_, 1);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v_a_2179_);
v___x_2181_ = v___x_2177_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
else
{
lean_object* v_a_2183_; 
lean_del_object(v___x_2177_);
v_a_2183_ = lean_ctor_get(v_a_2175_, 0);
lean_inc(v_a_2183_);
lean_dec_ref_known(v_a_2175_, 1);
v_a_2160_ = v_a_2183_;
goto _start;
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_a_2186_ = lean_ctor_get(v___y_2174_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___y_2174_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___y_2174_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___y_2174_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg___boxed(lean_object* v_a_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v_a_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work(lean_object* v_goal_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_toGoalState_2340_; lean_object* v_mvarId_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2379_; 
v_toGoalState_2340_ = lean_ctor_get(v_goal_2327_, 0);
v_mvarId_2341_ = lean_ctor_get(v_goal_2327_, 1);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_goal_2327_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2343_ = v_goal_2327_;
v_isShared_2344_ = v_isSharedCheck_2379_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_mvarId_2341_);
lean_inc(v_toGoalState_2340_);
lean_dec(v_goal_2327_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2379_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_2341_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 1, v_a_2346_);
v___x_2348_ = v___x_2343_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_toGoalState_2340_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_a_2346_);
v___x_2348_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_mk_empty_array_with_capacity(v___x_2349_);
v___x_2351_ = lean_array_push(v___x_2350_, v___x_2348_);
v___x_2352_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v___x_2351_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2360_; 
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v___x_2352_, 0);
lean_dec(v_unused_2361_);
v___x_2354_ = v___x_2352_;
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v___x_2352_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_box(0);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2356_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2352_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2352_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_del_object(v___x_2343_);
lean_dec_ref(v_toGoalState_2340_);
v_a_2371_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2345_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2345_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_work___boxed(lean_object* v_goal_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_goal_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4(lean_object* v_inst_2394_, lean_object* v_a_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___redArg(v_a_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4___boxed(lean_object* v_inst_2409_, lean_object* v_a_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_Internal_VCGen_work_spec__4(v_inst_2409_, v_a_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg(lean_object* v_as_2425_, lean_object* v_i_2426_, lean_object* v_j_2427_, lean_object* v_bs_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_zero_2434_; uint8_t v_isZero_2435_; 
v_zero_2434_ = lean_unsigned_to_nat(0u);
v_isZero_2435_ = lean_nat_dec_eq(v_i_2426_, v_zero_2434_);
if (v_isZero_2435_ == 1)
{
lean_object* v___x_2436_; 
lean_dec(v_j_2427_);
lean_dec(v_i_2426_);
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_bs_2428_);
return v___x_2436_;
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_array_fget_borrowed(v_as_2425_, v_j_2427_);
lean_inc(v___x_2437_);
v___x_2438_ = l_Lean_MVarId_getTag(v___x_2437_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v___x_2438_, 1);
v___x_2440_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg___closed__0));
v___x_2441_ = lean_unsigned_to_nat(1u);
v___x_2442_ = lean_nat_add(v_j_2427_, v___x_2441_);
lean_dec(v_j_2427_);
lean_inc(v___x_2442_);
v___x_2443_ = l_Nat_reprFast(v___x_2442_);
v___x_2444_ = lean_string_append(v___x_2440_, v___x_2443_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = lean_box(0);
v___x_2446_ = l_Lean_Name_str___override(v___x_2445_, v___x_2444_);
v___x_2447_ = lean_erase_macro_scopes(v_a_2439_);
v___x_2448_ = l_Lean_Name_append(v___x_2446_, v___x_2447_);
lean_inc(v___x_2437_);
v___x_2449_ = l_Lean_MVarId_setTag___redArg(v___x_2437_, v___x_2448_, v___y_2430_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v_n_2451_; lean_object* v___x_2452_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v_n_2451_ = lean_nat_sub(v_i_2426_, v___x_2441_);
lean_dec(v_i_2426_);
v___x_2452_ = lean_array_push(v_bs_2428_, v_a_2450_);
v_i_2426_ = v_n_2451_;
v_j_2427_ = v___x_2442_;
v_bs_2428_ = v___x_2452_;
goto _start;
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v___x_2442_);
lean_dec_ref(v_bs_2428_);
lean_dec(v_i_2426_);
v_a_2454_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2449_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2449_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v_bs_2428_);
lean_dec(v_j_2427_);
lean_dec(v_i_2426_);
v_a_2462_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2438_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2438_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg___boxed(lean_object* v_as_2470_, lean_object* v_i_2471_, lean_object* v_j_2472_, lean_object* v_bs_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg(v_as_2470_, v_i_2471_, v_j_2472_, v_bs_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v_as_2470_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___redArg(lean_object* v_mvarId_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; lean_object* v_mctx_2484_; lean_object* v_eAssignment_2485_; uint8_t v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2483_ = lean_st_ref_get(v___y_2481_);
v_mctx_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc_ref(v_mctx_2484_);
lean_dec(v___x_2483_);
v_eAssignment_2485_ = lean_ctor_get(v_mctx_2484_, 8);
lean_inc_ref(v_eAssignment_2485_);
lean_dec_ref(v_mctx_2484_);
v___x_2486_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_tryInlineInvariant_spec__0_spec__0___redArg(v_eAssignment_2485_, v_mvarId_2480_);
lean_dec_ref(v_eAssignment_2485_);
v___x_2487_ = lean_box(v___x_2486_);
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___redArg___boxed(lean_object* v_mvarId_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___redArg(v_mvarId_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec(v_mvarId_2489_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__3(lean_object* v_as_2493_, size_t v_i_2494_, size_t v_stop_2495_, lean_object* v_b_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_a_2508_; uint8_t v___x_2512_; 
v___x_2512_ = lean_usize_dec_eq(v_i_2494_, v_stop_2495_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2516_; 
v___x_2513_ = lean_array_uget_borrowed(v_as_2493_, v_i_2494_);
v___x_2516_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___redArg(v___x_2513_, v___y_2503_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; uint8_t v___x_2518_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = lean_unbox(v_a_2517_);
lean_dec(v_a_2517_);
if (v___x_2518_ == 0)
{
goto v___jp_2514_;
}
else
{
v_a_2508_ = v_b_2496_;
goto v___jp_2507_;
}
}
else
{
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2519_; uint8_t v___x_2520_; 
v_a_2519_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2519_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2520_ = lean_unbox(v_a_2519_);
lean_dec(v_a_2519_);
if (v___x_2520_ == 0)
{
v_a_2508_ = v_b_2496_;
goto v___jp_2507_;
}
else
{
goto v___jp_2514_;
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v_b_2496_);
v_a_2521_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2516_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2516_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
v___jp_2514_:
{
lean_object* v___x_2515_; 
lean_inc(v___x_2513_);
v___x_2515_ = lean_array_push(v_b_2496_, v___x_2513_);
v_a_2508_ = v___x_2515_;
goto v___jp_2507_;
}
}
else
{
lean_object* v___x_2529_; 
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_b_2496_);
return v___x_2529_;
}
v___jp_2507_:
{
size_t v___x_2509_; size_t v___x_2510_; 
v___x_2509_ = ((size_t)1ULL);
v___x_2510_ = lean_usize_add(v_i_2494_, v___x_2509_);
v_i_2494_ = v___x_2510_;
v_b_2496_ = v_a_2508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__3___boxed(lean_object* v_as_2530_, lean_object* v_i_2531_, lean_object* v_stop_2532_, lean_object* v_b_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
size_t v_i_boxed_2544_; size_t v_stop_boxed_2545_; lean_object* v_res_2546_; 
v_i_boxed_2544_ = lean_unbox_usize(v_i_2531_);
lean_dec(v_i_2531_);
v_stop_boxed_2545_ = lean_unbox_usize(v_stop_2532_);
lean_dec(v_stop_2532_);
v_res_2546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__3(v_as_2530_, v_i_boxed_2544_, v_stop_boxed_2545_, v_b_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v_as_2530_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg(lean_object* v_as_2548_, lean_object* v_i_2549_, lean_object* v_j_2550_, lean_object* v_bs_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_zero_2554_; uint8_t v_isZero_2555_; 
v_zero_2554_ = lean_unsigned_to_nat(0u);
v_isZero_2555_ = lean_nat_dec_eq(v_i_2549_, v_zero_2554_);
if (v_isZero_2555_ == 1)
{
lean_object* v___x_2556_; 
lean_dec(v_j_2550_);
lean_dec(v_i_2549_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_bs_2551_);
return v___x_2556_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2557_ = lean_array_fget_borrowed(v_as_2548_, v_j_2550_);
v___x_2558_ = ((lean_object*)(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg___closed__0));
v___x_2559_ = lean_unsigned_to_nat(1u);
v___x_2560_ = lean_nat_add(v_j_2550_, v___x_2559_);
lean_dec(v_j_2550_);
lean_inc(v___x_2560_);
v___x_2561_ = l_Nat_reprFast(v___x_2560_);
v___x_2562_ = lean_string_append(v___x_2558_, v___x_2561_);
lean_dec_ref(v___x_2561_);
v___x_2563_ = lean_box(0);
v___x_2564_ = l_Lean_Name_str___override(v___x_2563_, v___x_2562_);
lean_inc(v___x_2557_);
v___x_2565_ = l_Lean_MVarId_setTag___redArg(v___x_2557_, v___x_2564_, v___y_2552_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v_n_2567_; lean_object* v___x_2568_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v_n_2567_ = lean_nat_sub(v_i_2549_, v___x_2559_);
lean_dec(v_i_2549_);
v___x_2568_ = lean_array_push(v_bs_2551_, v_a_2566_);
v_i_2549_ = v_n_2567_;
v_j_2550_ = v___x_2560_;
v_bs_2551_ = v___x_2568_;
goto _start;
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec(v___x_2560_);
lean_dec_ref(v_bs_2551_);
lean_dec(v_i_2549_);
v_a_2570_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2565_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2565_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg___boxed(lean_object* v_as_2578_, lean_object* v_i_2579_, lean_object* v_j_2580_, lean_object* v_bs_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg(v_as_2578_, v_i_2579_, v_j_2580_, v_bs_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v_as_2578_);
return v_res_2584_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__0(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_box(0);
v___x_2586_ = lean_unsigned_to_nat(16u);
v___x_2587_ = lean_mk_array(v___x_2586_, v___x_2585_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__1(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__0);
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___x_2588_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__2(void){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__3(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__2);
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__4(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__3);
v___x_2595_ = lean_unsigned_to_nat(0u);
v___x_2596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2594_);
lean_ctor_set(v___x_2596_, 2, v___x_2594_);
lean_ctor_set(v___x_2596_, 3, v___x_2594_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main(lean_object* v_goal_2597_, lean_object* v_ctx_2598_, lean_object* v_stepLimit_x3f_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___y_2611_; uint8_t v___y_2612_; lean_object* v___y_2613_; lean_object* v_a_2614_; lean_object* v___y_2618_; uint8_t v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Meta_Grind_mkGoalCore(v_goal_2597_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___y_2639_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__1);
v___x_2635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Driver_0__Lean_Elab_Tactic_Do_Internal_VCGen_handleInvariantSubgoals___closed__0));
v___x_2636_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__4, &l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__4_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_main___closed__4);
v___x_2637_ = lean_box(1);
if (lean_obj_tag(v_stepLimit_x3f_2599_) == 0)
{
lean_object* v___x_2687_; 
v___x_2687_ = lean_box(1);
v___y_2639_ = v___x_2687_;
goto v___jp_2638_;
}
else
{
lean_object* v_val_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_val_2688_ = lean_ctor_get(v_stepLimit_x3f_2599_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_stepLimit_x3f_2599_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v_stepLimit_x3f_2599_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_val_2688_);
lean_dec(v_stepLimit_x3f_2599_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set_tag(v___x_2690_, 0);
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_val_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
v___y_2639_ = v___x_2693_;
goto v___jp_2638_;
}
}
}
v___jp_2638_:
{
uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2640_ = 0;
v___x_2641_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_2641_, 0, v___x_2634_);
lean_ctor_set(v___x_2641_, 1, v___x_2634_);
lean_ctor_set(v___x_2641_, 2, v___x_2635_);
lean_ctor_set(v___x_2641_, 3, v___x_2635_);
lean_ctor_set(v___x_2641_, 4, v___x_2636_);
lean_ctor_set(v___x_2641_, 5, v___x_2637_);
lean_ctor_set(v___x_2641_, 6, v___y_2639_);
lean_ctor_set(v___x_2641_, 7, v___x_2634_);
lean_ctor_set_uint8(v___x_2641_, sizeof(void*)*8, v___x_2640_);
v___x_2642_ = lean_st_mk_ref(v___x_2641_);
v___x_2643_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_work(v_a_2632_, v_ctx_2598_, v___x_2642_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v___x_2644_; lean_object* v_invariants_2645_; lean_object* v_vcs_2646_; lean_object* v_inlineHandledInvariants_2647_; uint8_t v_preTacFailed_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec_ref_known(v___x_2643_, 1);
v___x_2644_ = lean_st_ref_get(v___x_2642_);
lean_dec(v___x_2642_);
v_invariants_2645_ = lean_ctor_get(v___x_2644_, 2);
lean_inc_ref(v_invariants_2645_);
v_vcs_2646_ = lean_ctor_get(v___x_2644_, 3);
lean_inc_ref(v_vcs_2646_);
v_inlineHandledInvariants_2647_ = lean_ctor_get(v___x_2644_, 7);
lean_inc_ref(v_inlineHandledInvariants_2647_);
v_preTacFailed_2648_ = lean_ctor_get_uint8(v___x_2644_, sizeof(void*)*8);
lean_dec(v___x_2644_);
v___x_2649_ = lean_array_get_size(v_invariants_2645_);
v___x_2650_ = lean_mk_empty_array_with_capacity(v___x_2649_);
v___x_2651_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg(v_invariants_2645_, v___x_2649_, v___x_2633_, v___x_2650_, v_a_2606_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec_ref_known(v___x_2651_, 1);
v___x_2652_ = lean_array_get_size(v_vcs_2646_);
v___x_2653_ = lean_mk_empty_array_with_capacity(v___x_2652_);
v___x_2654_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg(v_vcs_2646_, v___x_2652_, v___x_2633_, v___x_2653_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2654_) == 0)
{
uint8_t v___x_2655_; 
lean_dec_ref_known(v___x_2654_, 1);
v___x_2655_ = lean_nat_dec_lt(v___x_2633_, v___x_2652_);
if (v___x_2655_ == 0)
{
lean_dec_ref(v_vcs_2646_);
v___y_2611_ = v_invariants_2645_;
v___y_2612_ = v_preTacFailed_2648_;
v___y_2613_ = v_inlineHandledInvariants_2647_;
v_a_2614_ = v___x_2635_;
goto v___jp_2610_;
}
else
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_nat_dec_le(v___x_2652_, v___x_2652_);
if (v___x_2656_ == 0)
{
if (v___x_2655_ == 0)
{
lean_dec_ref(v_vcs_2646_);
v___y_2611_ = v_invariants_2645_;
v___y_2612_ = v_preTacFailed_2648_;
v___y_2613_ = v_inlineHandledInvariants_2647_;
v_a_2614_ = v___x_2635_;
goto v___jp_2610_;
}
else
{
size_t v___x_2657_; size_t v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = ((size_t)0ULL);
v___x_2658_ = lean_usize_of_nat(v___x_2652_);
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__3(v_vcs_2646_, v___x_2657_, v___x_2658_, v___x_2635_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec_ref(v_vcs_2646_);
v___y_2618_ = v_invariants_2645_;
v___y_2619_ = v_preTacFailed_2648_;
v___y_2620_ = v_inlineHandledInvariants_2647_;
v___y_2621_ = v___x_2659_;
goto v___jp_2617_;
}
}
else
{
size_t v___x_2660_; size_t v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = ((size_t)0ULL);
v___x_2661_ = lean_usize_of_nat(v___x_2652_);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__3(v_vcs_2646_, v___x_2660_, v___x_2661_, v___x_2635_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec_ref(v_vcs_2646_);
v___y_2618_ = v_invariants_2645_;
v___y_2619_ = v_preTacFailed_2648_;
v___y_2620_ = v_inlineHandledInvariants_2647_;
v___y_2621_ = v___x_2662_;
goto v___jp_2617_;
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v_inlineHandledInvariants_2647_);
lean_dec_ref(v_vcs_2646_);
lean_dec_ref(v_invariants_2645_);
v_a_2663_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2654_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2654_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v_inlineHandledInvariants_2647_);
lean_dec_ref(v_vcs_2646_);
lean_dec_ref(v_invariants_2645_);
v_a_2671_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2651_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2651_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v___x_2642_);
v_a_2679_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2643_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2643_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_stepLimit_x3f_2599_);
v_a_2696_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2631_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2631_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
v___jp_2610_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2615_, 0, v___y_2611_);
lean_ctor_set(v___x_2615_, 1, v_a_2614_);
lean_ctor_set(v___x_2615_, 2, v___y_2613_);
lean_ctor_set_uint8(v___x_2615_, sizeof(void*)*3, v___y_2612_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
return v___x_2616_;
}
v___jp_2617_:
{
if (lean_obj_tag(v___y_2621_) == 0)
{
lean_object* v_a_2622_; 
v_a_2622_ = lean_ctor_get(v___y_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___y_2621_, 1);
v___y_2611_ = v___y_2618_;
v___y_2612_ = v___y_2619_;
v___y_2613_ = v___y_2620_;
v_a_2614_ = v_a_2622_;
goto v___jp_2610_;
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec_ref(v___y_2620_);
lean_dec_ref(v___y_2618_);
v_a_2623_ = lean_ctor_get(v___y_2621_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___y_2621_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___y_2621_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___y_2621_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_main___boxed(lean_object* v_goal_2704_, lean_object* v_ctx_2705_, lean_object* v_stepLimit_x3f_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_main(v_goal_2704_, v_ctx_2705_, v_stepLimit_x3f_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
lean_dec(v_a_2715_);
lean_dec_ref(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
lean_dec(v_a_2707_);
lean_dec_ref(v_ctx_2705_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0(lean_object* v_mvarId_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___redArg(v_mvarId_2718_, v___y_2725_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0___boxed(lean_object* v_mvarId_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__0(v_mvarId_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v_mvarId_2730_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1(lean_object* v_as_2742_, lean_object* v_i_2743_, lean_object* v_j_2744_, lean_object* v_inv_2745_, lean_object* v_bs_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___redArg(v_as_2742_, v_i_2743_, v_j_2744_, v_bs_2746_, v___y_2753_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1___boxed(lean_object* v_as_2758_, lean_object* v_i_2759_, lean_object* v_j_2760_, lean_object* v_inv_2761_, lean_object* v_bs_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__1(v_as_2758_, v_i_2759_, v_j_2760_, v_inv_2761_, v_bs_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v_as_2758_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2(lean_object* v_as_2774_, lean_object* v_i_2775_, lean_object* v_j_2776_, lean_object* v_inv_2777_, lean_object* v_bs_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___redArg(v_as_2774_, v_i_2775_, v_j_2776_, v_bs_2778_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2___boxed(lean_object* v_as_2790_, lean_object* v_i_2791_, lean_object* v_j_2792_, lean_object* v_inv_2793_, lean_object* v_bs_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_main_spec__2(v_as_2790_, v_i_2791_, v_j_2792_, v_inv_2793_, v_bs_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v_as_2790_);
return v_res_2805_;
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
