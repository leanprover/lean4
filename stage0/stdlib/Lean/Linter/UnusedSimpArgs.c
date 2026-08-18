// Lean compiler output
// Module: Lean.Linter.UnusedSimpArgs
// Imports: public import Lean.Elab.Command public import Lean.Elab.Tactic.Simp public import Lean.Linter.Util
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_linter_unusedSimpArgs;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_getSimpParams(lean_object*);
lean_object* l_Lean_Elab_Tactic_setSimpParams(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1_value;
static const lean_array_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2_value;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Omit it from the simp argument list."};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value;
static const lean_ctor_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_value)}};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4_value;
static lean_once_cell_t l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "This simp argument is unused:"};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6_value;
static lean_once_cell_t l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value;
static const lean_ctor_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__10_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11_value;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 260, .m_capacity = 260, .m_length = 255, .m_data = "Simp arguments with `←` have the additional effect of removing the other direction from the simp set, even if the simp argument itself is unused. If the hint above does not work, try replacing `←` with `-` to only get that effect and silence this warning."};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12_value;
static lean_once_cell_t l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13;
static lean_once_cell_t l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Index "};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15_value;
static lean_once_cell_t l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = " out of bounds for simp arguments of "};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17_value;
static lean_once_cell_t l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Simp argument mask size mismatch: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " vs. "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(5, 49, 55, 92, 153, 191, 153, 249)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___closed__0;
static lean_once_cell_t l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___closed__1;
static lean_once_cell_t l_Lean_Linter_unusedSimpArgs___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_unusedSimpArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_unusedSimpArgs___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_unusedSimpArgs___closed__0 = (const lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__0_value;
static const lean_string_object l_Lean_Linter_unusedSimpArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_unusedSimpArgs___closed__1 = (const lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__1_value;
static const lean_string_object l_Lean_Linter_unusedSimpArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "unusedSimpArgs"};
static const lean_object* l_Lean_Linter_unusedSimpArgs___closed__2 = (const lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__2_value;
static const lean_ctor_object l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_0),((lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_unusedSimpArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__3_value_aux_1),((lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__2_value),LEAN_SCALAR_PTR_LITERAL(106, 83, 85, 18, 196, 98, 191, 198)}};
static const lean_object* l_Lean_Linter_unusedSimpArgs___closed__3 = (const lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__3_value;
static const lean_ctor_object l_Lean_Linter_unusedSimpArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__0_value),((lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__3_value)}};
static const lean_object* l_Lean_Linter_unusedSimpArgs___closed__4 = (const lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_unusedSimpArgs = (const lean_object*)&l_Lean_Linter_unusedSimpArgs___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(lean_object* v_upperBound_1_, lean_object* v_i_2_, lean_object* v_simpArgs_3_, lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
lean_object* v_a_8_; uint8_t v___x_12_; 
v___x_12_ = lean_nat_dec_lt(v_a_4_, v_upperBound_1_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec(v_a_4_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v_b_5_);
return v___x_13_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_eq(v_a_4_, v_i_2_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_array_fget_borrowed(v_simpArgs_3_, v_a_4_);
lean_inc(v___x_15_);
v___x_16_ = lean_array_push(v_b_5_, v___x_15_);
v_a_8_ = v___x_16_;
goto v___jp_7_;
}
else
{
v_a_8_ = v_b_5_;
goto v___jp_7_;
}
}
v___jp_7_:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_add(v_a_4_, v___x_9_);
lean_dec(v_a_4_);
v_a_4_ = v___x_10_;
v_b_5_ = v_a_8_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg___boxed(lean_object* v_upperBound_17_, lean_object* v_i_18_, lean_object* v_simpArgs_19_, lean_object* v_a_20_, lean_object* v_b_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_17_, v_i_18_, v_simpArgs_19_, v_a_20_, v_b_21_);
lean_dec_ref(v_simpArgs_19_);
lean_dec(v_i_18_);
lean_dec(v_upperBound_17_);
return v_res_23_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_24_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_28_);
lean_ctor_set(v___x_29_, 2, v___x_28_);
lean_ctor_set(v___x_29_, 3, v___x_28_);
lean_ctor_set(v___x_29_, 4, v___x_27_);
lean_ctor_set(v___x_29_, 5, v___x_27_);
lean_ctor_set(v___x_29_, 6, v___x_27_);
lean_ctor_set(v___x_29_, 7, v___x_27_);
lean_ctor_set(v___x_29_, 8, v___x_27_);
lean_ctor_set(v___x_29_, 9, v___x_27_);
lean_ctor_set(v___x_29_, 10, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_unsigned_to_nat(32u);
v___x_31_ = lean_mk_empty_array_with_capacity(v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4(void){
_start:
{
size_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_33_ = ((size_t)5ULL);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_unsigned_to_nat(32u);
v___x_36_ = lean_mk_empty_array_with_capacity(v___x_35_);
v___x_37_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3);
v___x_38_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_34_);
lean_ctor_set(v___x_38_, 3, v___x_34_);
lean_ctor_set_usize(v___x_38_, 4, v___x_33_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_box(1);
v___x_40_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4);
v___x_41_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
v___x_42_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
lean_ctor_set(v___x_42_, 2, v___x_39_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(lean_object* v_msgData_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; lean_object* v_env_48_; lean_object* v_options_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_47_ = lean_st_ref_get(v___y_45_);
v_env_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_env_48_);
lean_dec(v___x_47_);
v_options_49_ = lean_ctor_get(v___y_44_, 2);
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_49_);
v___x_52_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_52_, 0, v_env_48_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v_options_49_);
v___x_53_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v_msgData_43_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___boxed(lean_object* v_msgData_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msgData_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(lean_object* v_msg_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_ref_64_; lean_object* v___x_65_; lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_74_; 
v_ref_64_ = lean_ctor_get(v___y_61_, 5);
v___x_65_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msg_60_, v___y_61_, v___y_62_);
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_74_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_74_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_72_; 
lean_inc(v_ref_64_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_ref_64_);
lean_ctor_set(v___x_70_, 1, v_a_66_);
if (v_isShared_69_ == 0)
{
lean_ctor_set_tag(v___x_68_, 1);
lean_ctor_set(v___x_68_, 0, v___x_70_);
v___x_72_ = v___x_68_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg___boxed(lean_object* v_msg_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_88_, uint8_t v_suppressElabErrors_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_90_) == 1)
{
lean_object* v_pre_91_; 
v_pre_91_ = lean_ctor_get(v_x_90_, 0);
switch(lean_obj_tag(v_pre_91_))
{
case 1:
{
lean_object* v_pre_92_; 
v_pre_92_ = lean_ctor_get(v_pre_91_, 0);
switch(lean_obj_tag(v_pre_92_))
{
case 0:
{
lean_object* v_str_93_; lean_object* v_str_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v_str_93_ = lean_ctor_get(v_x_90_, 1);
v_str_94_ = lean_ctor_get(v_pre_91_, 1);
v___x_95_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_96_ = lean_string_dec_eq(v_str_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_98_ = lean_string_dec_eq(v_str_94_, v___x_97_);
if (v___x_98_ == 0)
{
return v___y_88_;
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_100_ = lean_string_dec_eq(v_str_93_, v___x_99_);
if (v___x_100_ == 0)
{
return v___y_88_;
}
else
{
return v_suppressElabErrors_89_;
}
}
}
else
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_102_ = lean_string_dec_eq(v_str_93_, v___x_101_);
if (v___x_102_ == 0)
{
return v___y_88_;
}
else
{
return v_suppressElabErrors_89_;
}
}
}
case 1:
{
lean_object* v_pre_103_; 
v_pre_103_ = lean_ctor_get(v_pre_92_, 0);
if (lean_obj_tag(v_pre_103_) == 0)
{
lean_object* v_str_104_; lean_object* v_str_105_; lean_object* v_str_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_str_104_ = lean_ctor_get(v_x_90_, 1);
v_str_105_ = lean_ctor_get(v_pre_91_, 1);
v_str_106_ = lean_ctor_get(v_pre_92_, 1);
v___x_107_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_108_ = lean_string_dec_eq(v_str_106_, v___x_107_);
if (v___x_108_ == 0)
{
return v___y_88_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_110_ = lean_string_dec_eq(v_str_105_, v___x_109_);
if (v___x_110_ == 0)
{
return v___y_88_;
}
else
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_112_ = lean_string_dec_eq(v_str_104_, v___x_111_);
if (v___x_112_ == 0)
{
return v___y_88_;
}
else
{
return v_suppressElabErrors_89_;
}
}
}
}
else
{
return v___y_88_;
}
}
default: 
{
return v___y_88_;
}
}
}
case 0:
{
lean_object* v_str_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_str_113_ = lean_ctor_get(v_x_90_, 1);
v___x_114_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_115_ = lean_string_dec_eq(v_str_113_, v___x_114_);
if (v___x_115_ == 0)
{
return v___y_88_;
}
else
{
return v_suppressElabErrors_89_;
}
}
default: 
{
return v___y_88_;
}
}
}
else
{
return v___y_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_116_, lean_object* v_suppressElabErrors_117_, lean_object* v_x_118_){
_start:
{
uint8_t v___y_4626__boxed_119_; uint8_t v_suppressElabErrors_boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v___y_4626__boxed_119_ = lean_unbox(v___y_116_);
v_suppressElabErrors_boxed_120_ = lean_unbox(v_suppressElabErrors_117_);
v_res_121_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v___y_4626__boxed_119_, v_suppressElabErrors_boxed_120_, v_x_118_);
lean_dec(v_x_118_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_123_, lean_object* v_opt_124_){
_start:
{
lean_object* v_name_125_; lean_object* v_defValue_126_; lean_object* v_map_127_; lean_object* v___x_128_; 
v_name_125_ = lean_ctor_get(v_opt_124_, 0);
v_defValue_126_ = lean_ctor_get(v_opt_124_, 1);
v_map_127_ = lean_ctor_get(v_opts_123_, 0);
v___x_128_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_127_, v_name_125_);
if (lean_obj_tag(v___x_128_) == 0)
{
uint8_t v___x_129_; 
v___x_129_ = lean_unbox(v_defValue_126_);
return v___x_129_;
}
else
{
lean_object* v_val_130_; 
v_val_130_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_val_130_);
lean_dec_ref_known(v___x_128_, 1);
if (lean_obj_tag(v_val_130_) == 1)
{
uint8_t v_v_131_; 
v_v_131_ = lean_ctor_get_uint8(v_val_130_, 0);
lean_dec_ref_known(v_val_130_, 0);
return v_v_131_;
}
else
{
uint8_t v___x_132_; 
lean_dec(v_val_130_);
v___x_132_ = lean_unbox(v_defValue_126_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_133_, lean_object* v_opt_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_133_, v_opt_134_);
lean_dec_ref(v_opt_134_);
lean_dec_ref(v_opts_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(lean_object* v_ref_138_, lean_object* v_msgData_139_, uint8_t v_severity_140_, uint8_t v_isSilent_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___y_146_; lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; uint8_t v___y_151_; uint8_t v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_182_; uint8_t v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; uint8_t v___y_187_; uint8_t v___y_188_; lean_object* v___y_189_; lean_object* v___y_207_; uint8_t v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; uint8_t v___y_211_; lean_object* v___y_212_; uint8_t v___y_213_; lean_object* v___y_214_; lean_object* v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; uint8_t v___y_223_; uint8_t v___y_224_; uint8_t v___x_229_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; uint8_t v___y_235_; uint8_t v___y_236_; uint8_t v___y_237_; uint8_t v___y_239_; uint8_t v___x_254_; 
v___x_229_ = 2;
v___x_254_ = l_Lean_instBEqMessageSeverity_beq(v_severity_140_, v___x_229_);
if (v___x_254_ == 0)
{
v___y_239_ = v___x_254_;
goto v___jp_238_;
}
else
{
uint8_t v___x_255_; 
lean_inc_ref(v_msgData_139_);
v___x_255_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_139_);
v___y_239_ = v___x_255_;
goto v___jp_238_;
}
v___jp_145_:
{
lean_object* v___x_155_; lean_object* v_currNamespace_156_; lean_object* v_openDecls_157_; lean_object* v_env_158_; lean_object* v_nextMacroScope_159_; lean_object* v_ngen_160_; lean_object* v_auxDeclNGen_161_; lean_object* v_traceState_162_; lean_object* v_cache_163_; lean_object* v_messages_164_; lean_object* v_infoState_165_; lean_object* v_snapshotTasks_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_180_; 
v___x_155_ = lean_st_ref_take(v___y_154_);
v_currNamespace_156_ = lean_ctor_get(v___y_153_, 6);
v_openDecls_157_ = lean_ctor_get(v___y_153_, 7);
v_env_158_ = lean_ctor_get(v___x_155_, 0);
v_nextMacroScope_159_ = lean_ctor_get(v___x_155_, 1);
v_ngen_160_ = lean_ctor_get(v___x_155_, 2);
v_auxDeclNGen_161_ = lean_ctor_get(v___x_155_, 3);
v_traceState_162_ = lean_ctor_get(v___x_155_, 4);
v_cache_163_ = lean_ctor_get(v___x_155_, 5);
v_messages_164_ = lean_ctor_get(v___x_155_, 6);
v_infoState_165_ = lean_ctor_get(v___x_155_, 7);
v_snapshotTasks_166_ = lean_ctor_get(v___x_155_, 8);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_180_ == 0)
{
v___x_168_ = v___x_155_;
v_isShared_169_ = v_isSharedCheck_180_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_snapshotTasks_166_);
lean_inc(v_infoState_165_);
lean_inc(v_messages_164_);
lean_inc(v_cache_163_);
lean_inc(v_traceState_162_);
lean_inc(v_auxDeclNGen_161_);
lean_inc(v_ngen_160_);
lean_inc(v_nextMacroScope_159_);
lean_inc(v_env_158_);
lean_dec(v___x_155_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_180_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
lean_inc(v_openDecls_157_);
lean_inc(v_currNamespace_156_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v_currNamespace_156_);
lean_ctor_set(v___x_170_, 1, v_openDecls_157_);
v___x_171_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___y_150_);
lean_inc_ref(v___y_148_);
lean_inc_ref(v___y_146_);
v___x_172_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_172_, 0, v___y_146_);
lean_ctor_set(v___x_172_, 1, v___y_147_);
lean_ctor_set(v___x_172_, 2, v___y_149_);
lean_ctor_set(v___x_172_, 3, v___y_148_);
lean_ctor_set(v___x_172_, 4, v___x_171_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*5, v___y_152_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*5 + 1, v___y_151_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*5 + 2, v_isSilent_141_);
v___x_173_ = l_Lean_MessageLog_add(v___x_172_, v_messages_164_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 6, v___x_173_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_env_158_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_nextMacroScope_159_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_ngen_160_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_auxDeclNGen_161_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v_traceState_162_);
lean_ctor_set(v_reuseFailAlloc_179_, 5, v_cache_163_);
lean_ctor_set(v_reuseFailAlloc_179_, 6, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_179_, 7, v_infoState_165_);
lean_ctor_set(v_reuseFailAlloc_179_, 8, v_snapshotTasks_166_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_st_ref_put(v___y_154_, v___x_175_);
v___x_177_ = lean_box(0);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
}
v___jp_181_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_205_; 
v___x_190_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_139_);
v___x_191_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v___x_190_, v___y_142_, v___y_143_);
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_205_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_205_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_205_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_inc_ref_n(v___y_185_, 2);
v___x_196_ = l_Lean_FileMap_toPosition(v___y_185_, v___y_186_);
lean_dec(v___y_186_);
v___x_197_ = l_Lean_FileMap_toPosition(v___y_185_, v___y_189_);
lean_dec(v___y_189_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
v___x_199_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0));
if (v___y_183_ == 0)
{
lean_del_object(v___x_194_);
lean_dec_ref(v___y_182_);
v___y_146_ = v___y_184_;
v___y_147_ = v___x_196_;
v___y_148_ = v___x_199_;
v___y_149_ = v___x_198_;
v___y_150_ = v_a_192_;
v___y_151_ = v___y_187_;
v___y_152_ = v___y_188_;
v___y_153_ = v___y_142_;
v___y_154_ = v___y_143_;
goto v___jp_145_;
}
else
{
uint8_t v___x_200_; 
lean_inc(v_a_192_);
v___x_200_ = l_Lean_MessageData_hasTag(v___y_182_, v_a_192_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_203_; 
lean_dec_ref_known(v___x_198_, 1);
lean_dec_ref(v___x_196_);
lean_dec(v_a_192_);
v___x_201_ = lean_box(0);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_201_);
v___x_203_ = v___x_194_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
else
{
lean_del_object(v___x_194_);
v___y_146_ = v___y_184_;
v___y_147_ = v___x_196_;
v___y_148_ = v___x_199_;
v___y_149_ = v___x_198_;
v___y_150_ = v_a_192_;
v___y_151_ = v___y_187_;
v___y_152_ = v___y_188_;
v___y_153_ = v___y_142_;
v___y_154_ = v___y_143_;
goto v___jp_145_;
}
}
}
}
v___jp_206_:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Syntax_getTailPos_x3f(v___y_212_, v___y_208_);
lean_dec(v___y_212_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_inc(v___y_214_);
v___y_182_ = v___y_207_;
v___y_183_ = v___y_213_;
v___y_184_ = v___y_209_;
v___y_185_ = v___y_210_;
v___y_186_ = v___y_214_;
v___y_187_ = v___y_211_;
v___y_188_ = v___y_208_;
v___y_189_ = v___y_214_;
goto v___jp_181_;
}
else
{
lean_object* v_val_216_; 
v_val_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_215_, 1);
v___y_182_ = v___y_207_;
v___y_183_ = v___y_213_;
v___y_184_ = v___y_209_;
v___y_185_ = v___y_210_;
v___y_186_ = v___y_214_;
v___y_187_ = v___y_211_;
v___y_188_ = v___y_208_;
v___y_189_ = v_val_216_;
goto v___jp_181_;
}
}
v___jp_217_:
{
lean_object* v_ref_225_; lean_object* v___x_226_; 
v_ref_225_ = l_Lean_replaceRef(v_ref_138_, v___y_222_);
v___x_226_ = l_Lean_Syntax_getPos_x3f(v_ref_225_, v___y_223_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___y_207_ = v___y_218_;
v___y_208_ = v___y_223_;
v___y_209_ = v___y_220_;
v___y_210_ = v___y_221_;
v___y_211_ = v___y_224_;
v___y_212_ = v_ref_225_;
v___y_213_ = v___y_219_;
v___y_214_ = v___x_227_;
goto v___jp_206_;
}
else
{
lean_object* v_val_228_; 
v_val_228_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_226_, 1);
v___y_207_ = v___y_218_;
v___y_208_ = v___y_223_;
v___y_209_ = v___y_220_;
v___y_210_ = v___y_221_;
v___y_211_ = v___y_224_;
v___y_212_ = v_ref_225_;
v___y_213_ = v___y_219_;
v___y_214_ = v_val_228_;
goto v___jp_206_;
}
}
v___jp_230_:
{
if (v___y_237_ == 0)
{
v___y_218_ = v___y_233_;
v___y_219_ = v___y_235_;
v___y_220_ = v___y_231_;
v___y_221_ = v___y_232_;
v___y_222_ = v___y_234_;
v___y_223_ = v___y_236_;
v___y_224_ = v_severity_140_;
goto v___jp_217_;
}
else
{
v___y_218_ = v___y_233_;
v___y_219_ = v___y_235_;
v___y_220_ = v___y_231_;
v___y_221_ = v___y_232_;
v___y_222_ = v___y_234_;
v___y_223_ = v___y_236_;
v___y_224_ = v___x_229_;
goto v___jp_217_;
}
}
v___jp_238_:
{
if (v___y_239_ == 0)
{
lean_object* v_fileName_240_; lean_object* v_fileMap_241_; lean_object* v_options_242_; lean_object* v_ref_243_; uint8_t v_suppressElabErrors_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___f_247_; uint8_t v___x_248_; uint8_t v___x_249_; 
v_fileName_240_ = lean_ctor_get(v___y_142_, 0);
v_fileMap_241_ = lean_ctor_get(v___y_142_, 1);
v_options_242_ = lean_ctor_get(v___y_142_, 2);
v_ref_243_ = lean_ctor_get(v___y_142_, 5);
v_suppressElabErrors_244_ = lean_ctor_get_uint8(v___y_142_, sizeof(void*)*14 + 1);
v___x_245_ = lean_box(v___y_239_);
v___x_246_ = lean_box(v_suppressElabErrors_244_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_247_, 0, v___x_245_);
lean_closure_set(v___f_247_, 1, v___x_246_);
v___x_248_ = 1;
v___x_249_ = l_Lean_instBEqMessageSeverity_beq(v_severity_140_, v___x_248_);
if (v___x_249_ == 0)
{
v___y_231_ = v_fileName_240_;
v___y_232_ = v_fileMap_241_;
v___y_233_ = v___f_247_;
v___y_234_ = v_ref_243_;
v___y_235_ = v_suppressElabErrors_244_;
v___y_236_ = v___y_239_;
v___y_237_ = v___x_249_;
goto v___jp_230_;
}
else
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = l_Lean_warningAsError;
v___x_251_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_options_242_, v___x_250_);
v___y_231_ = v_fileName_240_;
v___y_232_ = v_fileMap_241_;
v___y_233_ = v___f_247_;
v___y_234_ = v_ref_243_;
v___y_235_ = v_suppressElabErrors_244_;
v___y_236_ = v___y_239_;
v___y_237_ = v___x_251_;
goto v___jp_230_;
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec_ref(v_msgData_139_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_256_, lean_object* v_msgData_257_, lean_object* v_severity_258_, lean_object* v_isSilent_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
uint8_t v_severity_boxed_263_; uint8_t v_isSilent_boxed_264_; lean_object* v_res_265_; 
v_severity_boxed_263_ = lean_unbox(v_severity_258_);
v_isSilent_boxed_264_ = lean_unbox(v_isSilent_259_);
v_res_265_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_256_, v_msgData_257_, v_severity_boxed_263_, v_isSilent_boxed_264_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v_ref_256_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(lean_object* v_ref_266_, lean_object* v_msgData_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
uint8_t v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; 
v___x_271_ = 1;
v___x_272_ = 0;
v___x_273_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_266_, v_msgData_267_, v___x_271_, v___x_272_, v___y_268_, v___y_269_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(lean_object* v_ref_274_, lean_object* v_msgData_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_274_, v_msgData_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v_ref_274_);
return v_res_279_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0));
v___x_282_ = l_Lean_stringToMessageData(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2));
v___x_285_ = l_Lean_stringToMessageData(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(lean_object* v_linterOption_286_, lean_object* v_stx_287_, lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_name_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_310_; 
v_name_292_ = lean_ctor_get(v_linterOption_286_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_linterOption_286_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v_linterOption_286_, 1);
lean_dec(v_unused_311_);
v___x_294_ = v_linterOption_286_;
v_isShared_295_ = v_isSharedCheck_310_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_name_292_);
lean_dec(v_linterOption_286_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_310_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_296_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1);
lean_inc(v_name_292_);
v___x_297_ = l_Lean_MessageData_ofName(v_name_292_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 7);
lean_ctor_set(v___x_294_, 1, v___x_297_);
lean_ctor_set(v___x_294_, 0, v___x_296_);
v___x_299_ = v___x_294_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v___x_297_);
v___x_299_ = v_reuseFailAlloc_309_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_disable_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_300_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3);
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v_disable_302_ = l_Lean_MessageData_note(v___x_301_);
v___x_303_ = l_Lean_Linter_linterMessageTag;
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v_msg_288_);
lean_ctor_set(v___x_304_, 1, v_disable_302_);
v___x_305_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_306_, 0, v_name_292_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
lean_inc(v_stx_287_);
v___x_307_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_307_, 0, v_stx_287_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_stx_287_, v___x_307_, v___y_289_, v___y_290_);
lean_dec(v_stx_287_);
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(lean_object* v_linterOption_312_, lean_object* v_stx_313_, lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_312_, v_stx_313_, v_msg_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_318_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4));
v___x_328_ = l_Lean_MessageData_ofFormat(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13);
v___x_344_ = l_Lean_MessageData_note(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17));
v___x_350_ = l_Lean_stringToMessageData(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(lean_object* v_stx_351_, lean_object* v_i_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v_hint_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_simpArgs_367_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_365_ = lean_box(0);
v___x_366_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1));
v_simpArgs_367_ = l_Lean_Elab_Tactic_getSimpParams(v_stx_351_);
v___x_418_ = lean_array_get_size(v_simpArgs_367_);
v___x_419_ = lean_nat_dec_lt(v_i_352_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref(v_simpArgs_367_);
v___x_420_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16);
v___x_421_ = l_Nat_reprFast(v_i_352_);
v___x_422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
v___x_423_ = l_Lean_MessageData_ofFormat(v___x_422_);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_420_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = l_Lean_MessageData_ofSyntax(v_stx_351_);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v___x_428_, v_a_353_, v_a_354_);
return v___x_429_;
}
else
{
v___y_369_ = v_a_353_;
v___y_370_ = v_a_354_;
goto v___jp_368_;
}
v___jp_356_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___y_357_);
lean_ctor_set(v___x_363_, 1, v_hint_359_);
v___x_364_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_362_, v___y_358_, v___x_363_, v___y_360_, v___y_361_);
return v___x_364_;
}
v___jp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_argStx_373_; lean_object* v_otherArgs_374_; lean_object* v___x_375_; 
v___x_371_ = lean_array_get_size(v_simpArgs_367_);
v___x_372_ = lean_unsigned_to_nat(0u);
v_argStx_373_ = lean_array_get(v___x_365_, v_simpArgs_367_, v_i_352_);
v_otherArgs_374_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2));
v___x_375_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v___x_371_, v_i_352_, v_simpArgs_367_, v___x_372_, v_otherArgs_374_);
lean_dec_ref(v_simpArgs_367_);
lean_dec(v_i_352_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_a_376_);
lean_dec_ref_known(v___x_375_, 1);
lean_inc(v_stx_351_);
v___x_377_ = l_Lean_Elab_Tactic_setSimpParams(v_stx_351_, v_a_376_);
lean_dec(v_a_376_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_366_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
lean_ctor_set(v___x_380_, 2, v___x_379_);
lean_ctor_set(v___x_380_, 3, v___x_379_);
lean_ctor_set(v___x_380_, 4, v___x_379_);
lean_ctor_set(v___x_380_, 5, v___x_379_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v_stx_351_);
v___x_382_ = 4;
v___x_383_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_383_, 0, v___x_380_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_379_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*3, v___x_382_);
v___x_384_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5);
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_mk_empty_array_with_capacity(v___x_385_);
v___x_387_ = lean_array_push(v___x_386_, v___x_383_);
v___x_388_ = 0;
v___x_389_ = l_Lean_MessageData_hint(v___x_384_, v___x_387_, v___x_379_, v___x_379_, v___x_388_, v___y_369_, v___y_370_);
lean_dec_ref(v___x_387_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_msg_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v___x_391_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7);
lean_inc_n(v_argStx_373_, 2);
v___x_392_ = l_Lean_MessageData_ofSyntax(v_argStx_373_);
v___x_393_ = l_Lean_indentD(v___x_392_);
v_msg_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_394_, 0, v___x_391_);
lean_ctor_set(v_msg_394_, 1, v___x_393_);
v___x_395_ = l_Lean_Syntax_getKind(v_argStx_373_);
v___x_396_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11));
v___x_397_ = lean_name_eq(v___x_395_, v___x_396_);
lean_dec(v___x_395_);
if (v___x_397_ == 0)
{
v___y_357_ = v_msg_394_;
v___y_358_ = v_argStx_373_;
v_hint_359_ = v_a_390_;
v___y_360_ = v___y_369_;
v___y_361_ = v___y_370_;
goto v___jp_356_;
}
else
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = l_Lean_Syntax_getArg(v_argStx_373_, v___x_385_);
v___x_399_ = l_Lean_Syntax_isNone(v___x_398_);
lean_dec(v___x_398_);
if (v___x_399_ == 0)
{
if (v___x_397_ == 0)
{
v___y_357_ = v_msg_394_;
v___y_358_ = v_argStx_373_;
v_hint_359_ = v_a_390_;
v___y_360_ = v___y_369_;
v___y_361_ = v___y_370_;
goto v___jp_356_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v_a_390_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___y_357_ = v_msg_394_;
v___y_358_ = v_argStx_373_;
v_hint_359_ = v___x_401_;
v___y_360_ = v___y_369_;
v___y_361_ = v___y_370_;
goto v___jp_356_;
}
}
else
{
v___y_357_ = v_msg_394_;
v___y_358_ = v_argStx_373_;
v_hint_359_ = v_a_390_;
v___y_360_ = v___y_369_;
v___y_361_ = v___y_370_;
goto v___jp_356_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_argStx_373_);
v_a_402_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_389_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_389_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_argStx_373_);
lean_dec(v_stx_351_);
v_a_410_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_375_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_375_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed(lean_object* v_stx_430_, lean_object* v_i_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(v_stx_430_, v_i_431_, v_a_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(lean_object* v_upperBound_436_, lean_object* v_i_437_, lean_object* v_simpArgs_438_, lean_object* v_inst_439_, lean_object* v_R_440_, lean_object* v_a_441_, lean_object* v_b_442_, lean_object* v_c_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_436_, v_i_437_, v_simpArgs_438_, v_a_441_, v_b_442_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(lean_object* v_upperBound_448_, lean_object* v_i_449_, lean_object* v_simpArgs_450_, lean_object* v_inst_451_, lean_object* v_R_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v_c_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_448_, v_i_449_, v_simpArgs_450_, v_inst_451_, v_R_452_, v_a_453_, v_b_454_, v_c_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec_ref(v_simpArgs_450_);
lean_dec(v_i_449_);
lean_dec(v_upperBound_448_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(lean_object* v_00_u03b1_460_, lean_object* v_msg_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_461_, v___y_462_, v___y_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(lean_object* v_00_u03b1_466_, lean_object* v_msg_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(v_00_u03b1_466_, v_msg_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object* v_m_472_, lean_object* v_query_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v_zero_477_; uint8_t v_isZero_478_; 
v_zero_477_ = lean_unsigned_to_nat(0u);
v_isZero_478_ = lean_nat_dec_eq(v_x_475_, v_zero_477_);
if (v_isZero_478_ == 1)
{
lean_dec(v_x_476_);
lean_dec(v_x_475_);
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v___x_479_; 
v___x_479_ = lean_box(2);
return v___x_479_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_val_480_ = lean_ctor_get(v_x_474_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v_x_474_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v_x_474_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_val_480_);
lean_dec(v_x_474_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_val_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_keyArray_488_; lean_object* v_valueArray_489_; lean_object* v___x_490_; uint8_t v_isSome_491_; 
v_keyArray_488_ = lean_ctor_get(v_m_472_, 1);
v_valueArray_489_ = lean_ctor_get(v_m_472_, 2);
v___x_490_ = lean_array_fget_borrowed(v_keyArray_488_, v_x_476_);
v_isSome_491_ = lean_noption_is_some(v___x_490_);
if (v_isSome_491_ == 0)
{
lean_dec(v_x_475_);
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_492_, 0, v_x_476_);
return v___x_492_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_x_476_);
v_val_493_ = lean_ctor_get(v_x_474_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_x_474_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v_x_474_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_val_493_);
lean_dec(v_x_474_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_val_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v_one_501_; lean_object* v_n_502_; lean_object* v___y_504_; 
v_one_501_ = lean_unsigned_to_nat(1u);
v_n_502_ = lean_nat_sub(v_x_475_, v_one_501_);
lean_dec(v_x_475_);
if (v_isSome_491_ == 0)
{
goto v___jp_510_;
}
else
{
lean_object* v___x_512_; uint8_t v_isSome_513_; 
v___x_512_ = lean_array_fget_borrowed(v_valueArray_489_, v_x_476_);
v_isSome_513_ = lean_noption_is_some(v___x_512_);
if (v_isSome_513_ == 0)
{
goto v___jp_510_;
}
else
{
lean_object* v_val_514_; uint8_t v___x_515_; 
lean_inc(v___x_490_);
v_val_514_ = lean_noption_get(v___x_490_);
v___x_515_ = l_Lean_Syntax_instBEqRange_beq(v_val_514_, v_query_473_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
lean_dec(v_val_514_);
v___x_516_ = lean_array_get_size(v_keyArray_488_);
v___x_517_ = lean_nat_add(v_x_476_, v_one_501_);
lean_dec(v_x_476_);
v___x_518_ = lean_nat_dec_lt(v___x_517_, v___x_516_);
if (v___x_518_ == 0)
{
lean_dec(v___x_517_);
v_x_475_ = v_n_502_;
v_x_476_ = v_zero_477_;
goto _start;
}
else
{
v_x_475_ = v_n_502_;
v_x_476_ = v___x_517_;
goto _start;
}
}
else
{
lean_object* v_val_521_; lean_object* v___x_522_; 
lean_dec(v_n_502_);
lean_dec(v_x_474_);
lean_inc(v___x_512_);
v_val_521_ = lean_noption_get(v___x_512_);
v___x_522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_522_, 0, v_x_476_);
lean_ctor_set(v___x_522_, 1, v_val_514_);
lean_ctor_set(v___x_522_, 2, v_val_521_);
return v___x_522_;
}
}
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_505_ = lean_array_get_size(v_keyArray_488_);
v___x_506_ = lean_nat_add(v_x_476_, v_one_501_);
lean_dec(v_x_476_);
v___x_507_ = lean_nat_dec_lt(v___x_506_, v___x_505_);
if (v___x_507_ == 0)
{
lean_dec(v___x_506_);
v_x_474_ = v___y_504_;
v_x_475_ = v_n_502_;
v_x_476_ = v_zero_477_;
goto _start;
}
else
{
v_x_474_ = v___y_504_;
v_x_475_ = v_n_502_;
v_x_476_ = v___x_506_;
goto _start;
}
}
v___jp_510_:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v___x_511_; 
lean_inc(v_x_476_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_x_476_);
v___y_504_ = v___x_511_;
goto v___jp_503_;
}
else
{
v___y_504_ = v_x_474_;
goto v___jp_503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object* v_m_523_, lean_object* v_query_524_, lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_m_523_, v_query_524_, v_x_525_, v_x_526_, v_x_527_);
lean_dec_ref(v_query_524_);
lean_dec_ref(v_m_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object* v_m_529_, lean_object* v_query_530_){
_start:
{
lean_object* v_keyArray_531_; lean_object* v___x_532_; uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; uint64_t v_fold_536_; uint64_t v___x_537_; uint64_t v___x_538_; uint64_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_keyArray_531_ = lean_ctor_get(v_m_529_, 1);
v___x_532_ = lean_array_get_size(v_keyArray_531_);
v___x_533_ = l_Lean_Syntax_instHashableRange_hash(v_query_530_);
v___x_534_ = 32ULL;
v___x_535_ = lean_uint64_shift_right(v___x_533_, v___x_534_);
v_fold_536_ = lean_uint64_xor(v___x_533_, v___x_535_);
v___x_537_ = 16ULL;
v___x_538_ = lean_uint64_shift_right(v_fold_536_, v___x_537_);
v___x_539_ = lean_uint64_xor(v_fold_536_, v___x_538_);
v___x_540_ = lean_uint64_to_usize(v___x_539_);
v___x_541_ = lean_usize_of_nat(v___x_532_);
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_sub(v___x_541_, v___x_542_);
v___x_544_ = lean_usize_land(v___x_540_, v___x_543_);
v___x_545_ = lean_usize_to_nat(v___x_544_);
v___x_546_ = lean_box(0);
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_m_529_, v_query_530_, v___x_546_, v___x_532_, v___x_545_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg___boxed(lean_object* v_m_548_, lean_object* v_query_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_548_, v_query_549_);
lean_dec_ref(v_query_549_);
lean_dec_ref(v_m_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___redArg(lean_object* v_m_551_, lean_object* v_query_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_551_, v_query_552_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_index_554_; lean_object* v_key_555_; lean_object* v_value_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_index_554_ = lean_ctor_get(v___x_553_, 0);
v_key_555_ = lean_ctor_get(v___x_553_, 1);
v_value_556_ = lean_ctor_get(v___x_553_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_553_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_value_556_);
lean_inc(v_key_555_);
lean_inc(v_index_554_);
lean_dec(v___x_553_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_index_554_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_key_555_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_value_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
else
{
lean_object* v___x_564_; 
lean_dec(v___x_553_);
v___x_564_ = lean_box(1);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___redArg___boxed(lean_object* v_m_565_, lean_object* v_query_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___redArg(v_m_565_, v_query_566_);
lean_dec_ref(v_query_566_);
lean_dec_ref(v_m_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___redArg(lean_object* v_m_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___redArg(v_m_568_, v_a_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_value_571_; lean_object* v___x_572_; 
v_value_571_ = lean_ctor_get(v___x_570_, 2);
lean_inc(v_value_571_);
lean_dec_ref_known(v___x_570_, 3);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_value_571_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; 
v___x_573_ = lean_box(0);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___redArg___boxed(lean_object* v_m_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___redArg(v_m_574_, v_a_575_);
lean_dec_ref(v_a_575_);
lean_dec_ref(v_m_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___redArg(lean_object* v_b_577_, lean_object* v_acc_578_, lean_object* v_i_579_){
_start:
{
lean_object* v___y_581_; lean_object* v_keyArray_589_; lean_object* v_valueArray_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_keyArray_589_ = lean_ctor_get(v_b_577_, 1);
v_valueArray_590_ = lean_ctor_get(v_b_577_, 2);
v___x_591_ = lean_array_get_size(v_keyArray_589_);
v___x_592_ = lean_nat_dec_lt(v_i_579_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v_i_579_);
return v_acc_578_;
}
else
{
lean_object* v___x_593_; uint8_t v_isSome_594_; 
v___x_593_ = lean_array_fget_borrowed(v_keyArray_589_, v_i_579_);
v_isSome_594_ = lean_noption_is_some(v___x_593_);
if (v_isSome_594_ == 0)
{
goto v___jp_585_;
}
else
{
lean_object* v___x_595_; uint8_t v_isSome_596_; 
v___x_595_ = lean_array_fget_borrowed(v_valueArray_590_, v_i_579_);
v_isSome_596_ = lean_noption_is_some(v___x_595_);
if (v_isSome_596_ == 0)
{
goto v___jp_585_;
}
else
{
lean_object* v_val_597_; lean_object* v_val_598_; lean_object* v_i_600_; lean_object* v___x_605_; 
lean_inc(v___x_593_);
v_val_597_ = lean_noption_get(v___x_593_);
lean_inc(v___x_595_);
v_val_598_ = lean_noption_get(v___x_595_);
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_acc_578_, v_val_597_);
switch(lean_obj_tag(v___x_605_))
{
case 0:
{
lean_object* v_index_606_; lean_object* v_size_607_; lean_object* v___x_608_; 
v_index_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_index_606_);
lean_dec_ref_known(v___x_605_, 3);
v_size_607_ = lean_ctor_get(v_acc_578_, 0);
lean_inc(v_size_607_);
v___x_608_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_578_, v_size_607_, v_index_606_, v_val_597_, v_val_598_);
lean_dec(v_index_606_);
v___y_581_ = v___x_608_;
goto v___jp_580_;
}
case 1:
{
lean_object* v_index_609_; 
v_index_609_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_index_609_);
lean_dec_ref_known(v___x_605_, 1);
v_i_600_ = v_index_609_;
goto v___jp_599_;
}
default: 
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_578_, v___x_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_index_612_; 
v_index_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_index_612_);
lean_dec_ref_known(v___x_611_, 1);
v_i_600_ = v_index_612_;
goto v___jp_599_;
}
else
{
lean_dec(v_val_598_);
lean_dec(v_val_597_);
v___y_581_ = v_acc_578_;
goto v___jp_580_;
}
}
}
v___jp_599_:
{
lean_object* v_size_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_size_601_ = lean_ctor_get(v_acc_578_, 0);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_size_601_, v___x_602_);
v___x_604_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_578_, v___x_603_, v_i_600_, v_val_597_, v_val_598_);
lean_dec(v_i_600_);
v___y_581_ = v___x_604_;
goto v___jp_580_;
}
}
}
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_i_579_, v___x_582_);
lean_dec(v_i_579_);
v_acc_578_ = v___y_581_;
v_i_579_ = v___x_583_;
goto _start;
}
v___jp_585_:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_i_579_, v___x_586_);
lean_dec(v_i_579_);
v_i_579_ = v___x_587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_613_, lean_object* v_acc_614_, lean_object* v_i_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___redArg(v_b_613_, v_acc_614_, v_i_615_);
lean_dec_ref(v_b_613_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___redArg(lean_object* v_init_617_, lean_object* v_b_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___redArg(v_b_618_, v_init_617_, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___redArg___boxed(lean_object* v_init_621_, lean_object* v_b_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___redArg(v_init_621_, v_b_622_);
lean_dec_ref(v_b_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object* v_m_624_){
_start:
{
lean_object* v_keyArray_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_cellCount_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_target_632_; lean_object* v___x_633_; 
v_keyArray_625_ = lean_ctor_get(v_m_624_, 1);
v___x_626_ = lean_array_get_size(v_keyArray_625_);
v___x_627_ = lean_unsigned_to_nat(2u);
v_cellCount_628_ = lean_nat_mul(v___x_626_, v___x_627_);
v___x_629_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_628_);
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_628_);
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_628_);
v_target_632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_632_, 0, v___x_629_);
lean_ctor_set(v_target_632_, 1, v___x_630_);
lean_ctor_set(v_target_632_, 2, v___x_631_);
v___x_633_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___redArg(v_target_632_, v_m_624_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object* v_m_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_634_);
lean_dec_ref(v_m_634_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___redArg(lean_object* v_msgData_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v_env_640_; lean_object* v___x_641_; lean_object* v_scopes_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v_opts_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_639_ = lean_st_ref_get(v___y_637_);
v_env_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc_ref(v_env_640_);
lean_dec(v___x_639_);
v___x_641_ = lean_st_ref_get(v___y_637_);
v_scopes_642_ = lean_ctor_get(v___x_641_, 2);
lean_inc(v_scopes_642_);
lean_dec(v___x_641_);
v___x_643_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_644_ = l_List_head_x21___redArg(v___x_643_, v_scopes_642_);
lean_dec(v_scopes_642_);
v_opts_645_ = lean_ctor_get(v___x_644_, 1);
lean_inc_ref(v_opts_645_);
lean_dec(v___x_644_);
v___x_646_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_647_ = lean_unsigned_to_nat(32u);
v___x_648_ = lean_mk_empty_array_with_capacity(v___x_647_);
lean_dec_ref(v___x_648_);
v___x_649_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
v___x_650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_650_, 0, v_env_640_);
lean_ctor_set(v___x_650_, 1, v___x_646_);
lean_ctor_set(v___x_650_, 2, v___x_649_);
lean_ctor_set(v___x_650_, 3, v_opts_645_);
v___x_651_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v_msgData_636_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___redArg(v_msgData_653_, v___y_654_);
lean_dec(v___y_654_);
return v_res_656_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_box(1);
v___x_658_ = l_Lean_MessageData_ofFormat(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__3(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__2));
v___x_663_ = l_Lean_MessageData_ofFormat(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19(lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
if (lean_obj_tag(v_x_665_) == 0)
{
return v_x_664_;
}
else
{
lean_object* v_head_666_; lean_object* v_tail_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_689_; 
v_head_666_ = lean_ctor_get(v_x_665_, 0);
v_tail_667_ = lean_ctor_get(v_x_665_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_689_ == 0)
{
v___x_669_ = v_x_665_;
v_isShared_670_ = v_isSharedCheck_689_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_tail_667_);
lean_inc(v_head_666_);
lean_dec(v_x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_689_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_before_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_687_; 
v_before_671_ = lean_ctor_get(v_head_666_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_head_666_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_head_666_, 1);
lean_dec(v_unused_688_);
v___x_673_ = v_head_666_;
v_isShared_674_ = v_isSharedCheck_687_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_before_671_);
lean_dec(v_head_666_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_687_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0);
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 7);
lean_ctor_set(v___x_673_, 1, v___x_675_);
lean_ctor_set(v___x_673_, 0, v_x_664_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_x_664_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_686_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__3);
if (v_isShared_670_ == 0)
{
lean_ctor_set_tag(v___x_669_, 7);
lean_ctor_set(v___x_669_, 1, v___x_678_);
lean_ctor_set(v___x_669_, 0, v___x_677_);
v___x_680_ = v___x_669_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_685_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = l_Lean_MessageData_ofSyntax(v_before_671_);
v___x_682_ = l_Lean_indentD(v___x_681_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_680_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v_x_664_ = v___x_683_;
v_x_665_ = v_tail_667_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__1));
v___x_694_ = l_Lean_MessageData_ofFormat(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg(lean_object* v_msgData_695_, lean_object* v_macroStack_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; lean_object* v_scopes_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_opts_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_699_ = lean_st_ref_get(v___y_697_);
v_scopes_700_ = lean_ctor_get(v___x_699_, 2);
lean_inc(v_scopes_700_);
lean_dec(v___x_699_);
v___x_701_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_702_ = l_List_head_x21___redArg(v___x_701_, v_scopes_700_);
lean_dec(v_scopes_700_);
v_opts_703_ = lean_ctor_get(v___x_702_, 1);
lean_inc_ref(v_opts_703_);
lean_dec(v___x_702_);
v___x_704_ = l_Lean_Elab_pp_macroStack;
v___x_705_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_703_, v___x_704_);
lean_dec_ref(v_opts_703_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; 
lean_dec(v_macroStack_696_);
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v_msgData_695_);
return v___x_706_;
}
else
{
if (lean_obj_tag(v_macroStack_696_) == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_msgData_695_);
return v___x_707_;
}
else
{
lean_object* v_head_708_; lean_object* v_after_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_724_; 
v_head_708_ = lean_ctor_get(v_macroStack_696_, 0);
lean_inc(v_head_708_);
v_after_709_ = lean_ctor_get(v_head_708_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_head_708_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_head_708_, 0);
lean_dec(v_unused_725_);
v___x_711_ = v_head_708_;
v_isShared_712_ = v_isSharedCheck_724_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_after_709_);
lean_dec(v_head_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_724_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19___closed__0);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 7);
lean_ctor_set(v___x_711_, 1, v___x_713_);
lean_ctor_set(v___x_711_, 0, v_msgData_695_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_msgData_695_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_713_);
v___x_715_ = v_reuseFailAlloc_723_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_msgData_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_716_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___closed__2);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_MessageData_ofSyntax(v_after_709_);
v___x_719_ = l_Lean_indentD(v___x_718_);
v_msgData_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_720_, 0, v___x_717_);
lean_ctor_set(v_msgData_720_, 1, v___x_719_);
v___x_721_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12_spec__19(v_msgData_720_, v_macroStack_696_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_msgData_726_, lean_object* v_macroStack_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg(v_msgData_726_, v_macroStack_727_, v___y_728_);
lean_dec(v___y_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___redArg(lean_object* v_msg_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Elab_Command_getRef___redArg(v___y_732_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v_macroStack_737_; lean_object* v___x_738_; lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v_macroStack_737_ = lean_ctor_get(v___y_732_, 4);
v___x_738_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___redArg(v_msg_731_, v___y_733_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Lean_Elab_getBetterRef(v_a_736_, v_macroStack_737_);
lean_dec(v_a_736_);
lean_inc(v_macroStack_737_);
v___x_741_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg(v_a_739_, v_macroStack_737_, v___y_733_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_750_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_740_);
lean_ctor_set(v___x_746_, 1, v_a_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 1);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_msg_731_);
v_a_751_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_735_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_735_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___redArg___boxed(lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___redArg(v_msg_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___redArg(lean_object* v_ref_764_, lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Elab_Command_getRef___redArg(v___y_766_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v_fileName_771_; lean_object* v_fileMap_772_; lean_object* v_currRecDepth_773_; lean_object* v_cmdPos_774_; lean_object* v_macroStack_775_; lean_object* v_quotContext_x3f_776_; lean_object* v_currMacroScope_777_; lean_object* v_snap_x3f_778_; lean_object* v_cancelTk_x3f_779_; uint8_t v_suppressElabErrors_780_; lean_object* v_ref_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v_fileName_771_ = lean_ctor_get(v___y_766_, 0);
v_fileMap_772_ = lean_ctor_get(v___y_766_, 1);
v_currRecDepth_773_ = lean_ctor_get(v___y_766_, 2);
v_cmdPos_774_ = lean_ctor_get(v___y_766_, 3);
v_macroStack_775_ = lean_ctor_get(v___y_766_, 4);
v_quotContext_x3f_776_ = lean_ctor_get(v___y_766_, 5);
v_currMacroScope_777_ = lean_ctor_get(v___y_766_, 6);
v_snap_x3f_778_ = lean_ctor_get(v___y_766_, 8);
v_cancelTk_x3f_779_ = lean_ctor_get(v___y_766_, 9);
v_suppressElabErrors_780_ = lean_ctor_get_uint8(v___y_766_, sizeof(void*)*10);
v_ref_781_ = l_Lean_replaceRef(v_ref_764_, v_a_770_);
lean_dec(v_a_770_);
lean_inc(v_cancelTk_x3f_779_);
lean_inc(v_snap_x3f_778_);
lean_inc(v_currMacroScope_777_);
lean_inc(v_quotContext_x3f_776_);
lean_inc(v_macroStack_775_);
lean_inc(v_cmdPos_774_);
lean_inc(v_currRecDepth_773_);
lean_inc_ref(v_fileMap_772_);
lean_inc_ref(v_fileName_771_);
v___x_782_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_782_, 0, v_fileName_771_);
lean_ctor_set(v___x_782_, 1, v_fileMap_772_);
lean_ctor_set(v___x_782_, 2, v_currRecDepth_773_);
lean_ctor_set(v___x_782_, 3, v_cmdPos_774_);
lean_ctor_set(v___x_782_, 4, v_macroStack_775_);
lean_ctor_set(v___x_782_, 5, v_quotContext_x3f_776_);
lean_ctor_set(v___x_782_, 6, v_currMacroScope_777_);
lean_ctor_set(v___x_782_, 7, v_ref_781_);
lean_ctor_set(v___x_782_, 8, v_snap_x3f_778_);
lean_ctor_set(v___x_782_, 9, v_cancelTk_x3f_779_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*10, v_suppressElabErrors_780_);
v___x_783_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___redArg(v_msg_765_, v___x_782_, v___y_767_);
lean_dec_ref_known(v___x_782_, 10);
return v___x_783_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_msg_765_);
v_a_784_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_769_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_769_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___redArg___boxed(lean_object* v_ref_792_, lean_object* v_msg_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___redArg(v_ref_792_, v_msg_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v_ref_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__4(uint8_t v___x_798_, lean_object* v_as_799_, lean_object* v_bs_800_, lean_object* v_i_801_, lean_object* v_cs_802_){
_start:
{
uint8_t v___y_804_; lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = lean_array_get_size(v_as_799_);
v___x_811_ = lean_nat_dec_lt(v_i_801_, v___x_810_);
if (v___x_811_ == 0)
{
lean_dec(v_i_801_);
return v_cs_802_;
}
else
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_array_get_size(v_bs_800_);
v___x_813_ = lean_nat_dec_lt(v_i_801_, v___x_812_);
if (v___x_813_ == 0)
{
lean_dec(v_i_801_);
return v_cs_802_;
}
else
{
lean_object* v_a_814_; uint8_t v___x_815_; 
v_a_814_ = lean_array_fget_borrowed(v_as_799_, v_i_801_);
v___x_815_ = lean_unbox(v_a_814_);
if (v___x_815_ == 0)
{
lean_object* v_b_816_; uint8_t v___x_817_; 
v_b_816_ = lean_array_fget_borrowed(v_bs_800_, v_i_801_);
v___x_817_ = lean_unbox(v_b_816_);
v___y_804_ = v___x_817_;
goto v___jp_803_;
}
else
{
v___y_804_ = v___x_798_;
goto v___jp_803_;
}
}
}
v___jp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_add(v_i_801_, v___x_805_);
lean_dec(v_i_801_);
v___x_807_ = lean_box(v___y_804_);
v___x_808_ = lean_array_push(v_cs_802_, v___x_807_);
v_i_801_ = v___x_806_;
v_cs_802_ = v___x_808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object* v___x_818_, lean_object* v_as_819_, lean_object* v_bs_820_, lean_object* v_i_821_, lean_object* v_cs_822_){
_start:
{
uint8_t v___x_16419__boxed_823_; lean_object* v_res_824_; 
v___x_16419__boxed_823_ = lean_unbox(v___x_818_);
v_res_824_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__4(v___x_16419__boxed_823_, v_as_819_, v_bs_820_, v_i_821_, v_cs_822_);
lean_dec_ref(v_bs_820_);
lean_dec_ref(v_as_819_);
return v_res_824_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__2(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__1));
v___x_829_ = l_Lean_stringToMessageData(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__4(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__3));
v___x_832_ = l_Lean_stringToMessageData(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1(lean_object* v_val_845_, uint8_t v___x_846_, lean_object* v_ci_847_, lean_object* v_info_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___y_854_; 
if (lean_obj_tag(v_info_848_) == 10)
{
lean_object* v_i_857_; lean_object* v_stx_858_; lean_object* v_value_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_1013_; 
v_i_857_ = lean_ctor_get(v_info_848_, 0);
lean_inc_ref(v_i_857_);
v_stx_858_ = lean_ctor_get(v_i_857_, 0);
v_value_859_ = lean_ctor_get(v_i_857_, 1);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_i_857_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_861_ = v_i_857_;
v_isShared_862_ = v_isSharedCheck_1013_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_value_859_);
lean_inc(v_stx_858_);
lean_dec(v_i_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_1013_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
v___x_864_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_859_, v___x_863_);
lean_dec(v_value_859_);
if (lean_obj_tag(v___x_864_) == 1)
{
lean_object* v_val_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_1003_; 
v_val_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_1003_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_val_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_1003_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Elab_Info_range_x3f(v_info_848_);
if (lean_obj_tag(v___x_869_) == 1)
{
lean_object* v_val_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_998_; 
v_val_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_998_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_998_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_val_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_998_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v_i_877_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v_i_896_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v_maskAcc_914_; lean_object* v___y_950_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__6));
lean_inc(v_stx_858_);
v___x_991_ = l_Lean_Syntax_isOfKind(v_stx_858_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__8));
lean_inc(v_stx_858_);
v___x_993_ = l_Lean_Syntax_isOfKind(v_stx_858_, v___x_992_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_996_; 
lean_del_object(v___x_872_);
lean_dec(v_val_870_);
lean_dec(v_val_865_);
lean_del_object(v___x_861_);
lean_dec(v_stx_858_);
lean_dec_ref_known(v_info_848_, 1);
v___x_994_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 0);
lean_ctor_set(v___x_867_, 0, v___x_994_);
v___x_996_ = v___x_867_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
lean_del_object(v___x_867_);
goto v___jp_954_;
}
}
else
{
lean_del_object(v___x_867_);
goto v___jp_954_;
}
v___jp_874_:
{
lean_object* v_size_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_size_878_ = lean_ctor_get(v___y_875_, 0);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_add(v_size_878_, v___x_879_);
v___x_881_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_875_, v___x_880_, v_i_877_, v_val_870_, v___y_876_);
lean_dec(v_i_877_);
v___y_854_ = v___x_881_;
goto v___jp_853_;
}
v___jp_882_:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___y_884_, v_val_870_);
switch(lean_obj_tag(v___x_885_))
{
case 0:
{
lean_object* v_index_886_; lean_object* v_size_887_; lean_object* v___x_888_; 
v_index_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_index_886_);
lean_dec_ref_known(v___x_885_, 3);
v_size_887_ = lean_ctor_get(v___y_884_, 0);
lean_inc(v_size_887_);
v___x_888_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_884_, v_size_887_, v_index_886_, v_val_870_, v___y_883_);
lean_dec(v_index_886_);
v___y_854_ = v___x_888_;
goto v___jp_853_;
}
case 1:
{
lean_object* v_index_889_; 
v_index_889_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_index_889_);
lean_dec_ref_known(v___x_885_, 1);
v___y_875_ = v___y_884_;
v___y_876_ = v___y_883_;
v_i_877_ = v_index_889_;
goto v___jp_874_;
}
default: 
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_884_, v___x_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_index_892_; 
v_index_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_index_892_);
lean_dec_ref_known(v___x_891_, 1);
v___y_875_ = v___y_884_;
v___y_876_ = v___y_883_;
v_i_877_ = v_index_892_;
goto v___jp_874_;
}
else
{
lean_dec_ref(v___y_883_);
lean_dec(v_val_870_);
v___y_854_ = v___y_884_;
goto v___jp_853_;
}
}
}
}
v___jp_893_:
{
lean_object* v_size_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_size_897_ = lean_ctor_get(v___y_894_, 0);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_size_897_, v___x_898_);
v___x_900_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_894_, v___x_899_, v_i_896_, v_val_870_, v___y_895_);
lean_dec(v_i_896_);
v___y_854_ = v___x_900_;
goto v___jp_853_;
}
v___jp_901_:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___y_902_);
lean_dec_ref(v___y_902_);
v___x_905_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_904_, v_val_870_);
switch(lean_obj_tag(v___x_905_))
{
case 0:
{
lean_object* v_index_906_; lean_object* v_size_907_; lean_object* v___x_908_; 
v_index_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_index_906_);
lean_dec_ref_known(v___x_905_, 3);
v_size_907_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_size_907_);
v___x_908_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_904_, v_size_907_, v_index_906_, v_val_870_, v___y_903_);
lean_dec(v_index_906_);
v___y_854_ = v___x_908_;
goto v___jp_853_;
}
case 1:
{
lean_object* v_index_909_; 
v_index_909_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_index_909_);
lean_dec_ref_known(v___x_905_, 1);
v___y_894_ = v___x_904_;
v___y_895_ = v___y_903_;
v_i_896_ = v_index_909_;
goto v___jp_893_;
}
default: 
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_904_, v___x_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_index_912_; 
v_index_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_index_912_);
lean_dec_ref_known(v___x_911_, 1);
v___y_894_ = v___x_904_;
v___y_895_ = v___y_903_;
v_i_896_ = v_index_912_;
goto v___jp_893_;
}
else
{
lean_dec_ref(v___y_903_);
lean_dec(v_val_870_);
v___y_854_ = v___x_904_;
goto v___jp_853_;
}
}
}
}
v___jp_913_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_915_ = lean_st_ref_take(v_val_845_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v_maskAcc_914_);
v___x_917_ = v___x_861_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_stx_858_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_maskAcc_914_);
v___x_917_ = v_reuseFailAlloc_948_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; 
v___x_918_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_915_, v_val_870_);
switch(lean_obj_tag(v___x_918_))
{
case 0:
{
lean_object* v_index_919_; lean_object* v_size_920_; lean_object* v___x_921_; 
v_index_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_index_919_);
lean_dec_ref_known(v___x_918_, 3);
v_size_920_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_size_920_);
v___x_921_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_915_, v_size_920_, v_index_919_, v_val_870_, v___x_917_);
lean_dec(v_index_919_);
v___y_854_ = v___x_921_;
goto v___jp_853_;
}
case 1:
{
lean_object* v_index_922_; lean_object* v_size_923_; lean_object* v_keyArray_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_index_922_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_index_922_);
lean_dec_ref_known(v___x_918_, 1);
v_size_923_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_size_923_);
v_keyArray_924_ = lean_ctor_get(v___x_915_, 1);
lean_inc_ref(v_keyArray_924_);
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_nat_add(v_size_923_, v___x_925_);
lean_dec(v_size_923_);
v___x_927_ = lean_array_get_size(v_keyArray_924_);
lean_dec_ref(v_keyArray_924_);
v___x_928_ = lean_nat_dec_lt(v___x_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec(v___x_926_);
lean_dec(v_index_922_);
v___y_902_ = v___x_915_;
v___y_903_ = v___x_917_;
goto v___jp_901_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_929_ = lean_unsigned_to_nat(4u);
v___x_930_ = lean_nat_mul(v___x_926_, v___x_929_);
v___x_931_ = lean_unsigned_to_nat(3u);
v___x_932_ = lean_nat_mul(v___x_927_, v___x_931_);
v___x_933_ = lean_nat_dec_le(v___x_930_, v___x_932_);
lean_dec(v___x_932_);
lean_dec(v___x_930_);
if (v___x_933_ == 0)
{
lean_dec(v___x_926_);
lean_dec(v_index_922_);
v___y_902_ = v___x_915_;
v___y_903_ = v___x_917_;
goto v___jp_901_;
}
else
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_915_, v___x_926_, v_index_922_, v_val_870_, v___x_917_);
lean_dec(v_index_922_);
v___y_854_ = v___x_934_;
goto v___jp_853_;
}
}
}
default: 
{
lean_object* v_size_935_; lean_object* v_keyArray_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_size_935_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_size_935_);
v_keyArray_936_ = lean_ctor_get(v___x_915_, 1);
lean_inc_ref(v_keyArray_936_);
v___x_937_ = lean_unsigned_to_nat(1u);
v___x_938_ = lean_nat_add(v_size_935_, v___x_937_);
lean_dec(v_size_935_);
v___x_939_ = lean_array_get_size(v_keyArray_936_);
lean_dec_ref(v_keyArray_936_);
v___x_940_ = lean_nat_dec_lt(v___x_938_, v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
lean_dec(v___x_938_);
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_915_);
lean_dec(v___x_915_);
v___y_883_ = v___x_917_;
v___y_884_ = v___x_941_;
goto v___jp_882_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_942_ = lean_unsigned_to_nat(4u);
v___x_943_ = lean_nat_mul(v___x_938_, v___x_942_);
lean_dec(v___x_938_);
v___x_944_ = lean_unsigned_to_nat(3u);
v___x_945_ = lean_nat_mul(v___x_939_, v___x_944_);
v___x_946_ = lean_nat_dec_le(v___x_943_, v___x_945_);
lean_dec(v___x_945_);
lean_dec(v___x_943_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_915_);
lean_dec(v___x_915_);
v___y_883_ = v___x_917_;
v___y_884_ = v___x_947_;
goto v___jp_882_;
}
else
{
v___y_883_ = v___x_917_;
v___y_884_ = v___x_915_;
goto v___jp_882_;
}
}
}
}
}
}
v___jp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__0));
v___x_953_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__4(v___x_846_, v_val_865_, v___y_950_, v___x_951_, v___x_952_);
lean_dec_ref(v___y_950_);
lean_dec(v_val_865_);
v_maskAcc_914_ = v___x_953_;
goto v___jp_913_;
}
v___jp_954_:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_st_ref_get(v_val_845_);
v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___redArg(v___x_955_, v_val_870_);
lean_dec(v___x_955_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_989_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_989_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_989_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_989_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v_snd_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_987_; 
v_snd_961_ = lean_ctor_get(v_val_957_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_val_957_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; 
v_unused_988_ = lean_ctor_get(v_val_957_, 0);
lean_dec(v_unused_988_);
v___x_963_ = v_val_957_;
v_isShared_964_ = v_isSharedCheck_987_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_snd_961_);
lean_dec(v_val_957_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_987_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_965_ = lean_array_get_size(v_val_865_);
v___x_966_ = lean_array_get_size(v_snd_961_);
v___x_967_ = lean_nat_dec_eq(v___x_965_, v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_968_ = l_Lean_Elab_Info_stx(v_info_848_);
lean_dec_ref_known(v_info_848_, 1);
v___x_969_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__2);
v___x_970_ = l_Nat_reprFast(v___x_966_);
if (v_isShared_960_ == 0)
{
lean_ctor_set_tag(v___x_959_, 3);
lean_ctor_set(v___x_959_, 0, v___x_970_);
v___x_972_ = v___x_959_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_986_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_973_ = l_Lean_MessageData_ofFormat(v___x_972_);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 7);
lean_ctor_set(v___x_963_, 1, v___x_973_);
lean_ctor_set(v___x_963_, 0, v___x_969_);
v___x_975_ = v___x_963_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_985_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_976_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___closed__4);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = l_Nat_reprFast(v___x_965_);
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 3);
lean_ctor_set(v___x_872_, 0, v___x_978_);
v___x_980_ = v___x_872_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = l_Lean_MessageData_ofFormat(v___x_980_);
v___x_982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_977_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___redArg(v___x_968_, v___x_982_, v___y_850_, v___y_851_);
lean_dec(v___x_968_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_dec_ref_known(v___x_983_, 1);
v___y_950_ = v_snd_961_;
goto v___jp_949_;
}
else
{
lean_dec(v_snd_961_);
lean_dec(v_val_870_);
lean_dec(v_val_865_);
lean_del_object(v___x_861_);
lean_dec(v_stx_858_);
return v___x_983_;
}
}
}
}
}
else
{
lean_del_object(v___x_963_);
lean_del_object(v___x_959_);
lean_del_object(v___x_872_);
lean_dec_ref_known(v_info_848_, 1);
v___y_950_ = v_snd_961_;
goto v___jp_949_;
}
}
}
}
else
{
lean_dec(v___x_956_);
lean_del_object(v___x_872_);
lean_dec_ref_known(v_info_848_, 1);
v_maskAcc_914_ = v_val_865_;
goto v___jp_913_;
}
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec(v___x_869_);
lean_dec(v_val_865_);
lean_del_object(v___x_861_);
lean_dec(v_stx_858_);
lean_dec_ref_known(v_info_848_, 1);
v___x_999_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 0);
lean_ctor_set(v___x_867_, 0, v___x_999_);
v___x_1001_ = v___x_867_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v___x_864_);
lean_del_object(v___x_861_);
lean_dec(v_stx_858_);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_info_848_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_info_848_, 0);
lean_dec(v_unused_1012_);
v___x_1005_ = v_info_848_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_info_848_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = lean_box(0);
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref(v_info_848_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
v___jp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_st_ref_put(v_val_845_, v___y_854_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___boxed(lean_object* v_val_1016_, lean_object* v___x_1017_, lean_object* v_ci_1018_, lean_object* v_info_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v___x_16492__boxed_1024_; lean_object* v_res_1025_; 
v___x_16492__boxed_1024_ = lean_unbox(v___x_1017_);
v_res_1025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1(v_val_1016_, v___x_16492__boxed_1024_, v_ci_1018_, v_info_1019_, v_x_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v_x_1020_);
lean_dec_ref(v_ci_1018_);
lean_dec(v_val_1016_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(lean_object* v_postNode_1026_, lean_object* v_ci_1027_, lean_object* v_i_1028_, lean_object* v_cs_1029_, lean_object* v_x_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
v___x_1034_ = lean_apply_6(v_postNode_1026_, v_ci_1027_, v_i_1028_, v_cs_1029_, v___y_1031_, v___y_1032_, lean_box(0));
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object* v_postNode_1035_, lean_object* v_ci_1036_, lean_object* v_i_1037_, lean_object* v_cs_1038_, lean_object* v_x_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v_postNode_1035_, v_ci_1036_, v_i_1037_, v_cs_1038_, v_x_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v_x_1039_);
return v_res_1043_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__0(void){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_instMonadEIO(lean_box(0));
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg(lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v_toApplicative_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1084_; 
v___x_1051_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__0);
v___x_1052_ = l_StateRefT_x27_instMonad___redArg(v___x_1051_);
v_toApplicative_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v___x_1052_, 1);
lean_dec(v_unused_1085_);
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1084_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_toApplicative_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1084_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_toFunctor_1057_; lean_object* v_toSeq_1058_; lean_object* v_toSeqLeft_1059_; lean_object* v_toSeqRight_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1082_; 
v_toFunctor_1057_ = lean_ctor_get(v_toApplicative_1053_, 0);
v_toSeq_1058_ = lean_ctor_get(v_toApplicative_1053_, 2);
v_toSeqLeft_1059_ = lean_ctor_get(v_toApplicative_1053_, 3);
v_toSeqRight_1060_ = lean_ctor_get(v_toApplicative_1053_, 4);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_toApplicative_1053_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_toApplicative_1053_, 1);
lean_dec(v_unused_1083_);
v___x_1062_ = v_toApplicative_1053_;
v_isShared_1063_ = v_isSharedCheck_1082_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_toSeqRight_1060_);
lean_inc(v_toSeqLeft_1059_);
lean_inc(v_toSeq_1058_);
lean_inc(v_toFunctor_1057_);
lean_dec(v_toApplicative_1053_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1082_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___f_1064_; lean_object* v___f_1065_; lean_object* v___f_1066_; lean_object* v___f_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___f_1071_; lean_object* v___x_1073_; 
v___f_1064_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__1));
v___f_1065_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___closed__2));
lean_inc_ref(v_toFunctor_1057_);
v___f_1066_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1066_, 0, v_toFunctor_1057_);
v___f_1067_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1067_, 0, v_toFunctor_1057_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___f_1066_);
lean_ctor_set(v___x_1068_, 1, v___f_1067_);
v___f_1069_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1069_, 0, v_toSeqRight_1060_);
v___f_1070_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1070_, 0, v_toSeqLeft_1059_);
v___f_1071_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1071_, 0, v_toSeq_1058_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 4, v___f_1069_);
lean_ctor_set(v___x_1062_, 3, v___f_1070_);
lean_ctor_set(v___x_1062_, 2, v___f_1071_);
lean_ctor_set(v___x_1062_, 1, v___f_1064_);
lean_ctor_set(v___x_1062_, 0, v___x_1068_);
v___x_1073_ = v___x_1062_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___f_1064_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v___f_1071_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v___f_1070_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___f_1069_);
v___x_1073_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___f_1065_);
lean_ctor_set(v___x_1055_, 0, v___x_1073_);
v___x_1075_ = v___x_1055_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v___f_1065_);
v___x_1075_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_15329__overap_1078_; lean_object* v___x_1079_; 
v___x_1076_ = lean_box(0);
v___x_1077_ = l_instInhabitedOfMonad___redArg(v___x_1075_, v___x_1076_);
v___x_15329__overap_1078_ = lean_panic_fn_borrowed(v___x_1077_, v_msg_1047_);
lean_dec(v___x_1077_);
lean_inc(v___y_1049_);
lean_inc_ref(v___y_1048_);
v___x_1079_ = lean_apply_3(v___x_15329__overap_1078_, v___y_1048_, v___y_1049_, lean_box(0));
return v___x_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg___boxed(lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg(v_msg_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1090_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__2));
v___x_1095_ = lean_unsigned_to_nat(21u);
v___x_1096_ = lean_unsigned_to_nat(65u);
v___x_1097_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__1));
v___x_1098_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__0));
v___x_1099_ = l_mkPanicMessageWithDecl(v___x_1098_, v___x_1097_, v___x_1096_, v___x_1095_, v___x_1094_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg(lean_object* v_preNode_1100_, lean_object* v_postNode_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
switch(lean_obj_tag(v_x_1103_))
{
case 0:
{
lean_object* v_i_1107_; lean_object* v_t_1108_; lean_object* v___x_1109_; 
v_i_1107_ = lean_ctor_get(v_x_1103_, 0);
lean_inc_ref(v_i_1107_);
v_t_1108_ = lean_ctor_get(v_x_1103_, 1);
lean_inc_ref(v_t_1108_);
lean_dec_ref_known(v_x_1103_, 2);
v___x_1109_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1107_, v_x_1102_);
v_x_1102_ = v___x_1109_;
v_x_1103_ = v_t_1108_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref_known(v_x_1103_, 2);
lean_dec_ref(v_postNode_1101_);
lean_dec_ref(v_preNode_1100_);
v___x_1111_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___closed__3);
v___x_1112_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg(v___x_1111_, v___y_1104_, v___y_1105_);
return v___x_1112_;
}
else
{
lean_object* v_i_1113_; lean_object* v_children_1114_; lean_object* v_val_1115_; lean_object* v___x_1116_; 
v_i_1113_ = lean_ctor_get(v_x_1103_, 0);
lean_inc_ref_n(v_i_1113_, 2);
v_children_1114_ = lean_ctor_get(v_x_1103_, 1);
lean_inc_ref_n(v_children_1114_, 2);
lean_dec_ref_known(v_x_1103_, 2);
v_val_1115_ = lean_ctor_get(v_x_1102_, 0);
lean_inc_n(v_val_1115_, 2);
lean_inc_ref(v_preNode_1100_);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
v___x_1116_ = lean_apply_6(v_preNode_1100_, v_val_1115_, v_i_1113_, v_children_1114_, v___y_1104_, v___y_1105_, lean_box(0));
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; uint8_t v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = lean_unbox(v_a_1117_);
lean_dec(v_a_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v_preNode_1100_);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1102_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v_x_1102_, 0);
lean_dec(v_unused_1144_);
v___x_1120_ = v_x_1102_;
v_isShared_1121_ = v_isSharedCheck_1143_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v_x_1102_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1143_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_box(0);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
v___x_1123_ = lean_apply_7(v_postNode_1101_, v_val_1115_, v_i_1113_, v_children_1114_, v___x_1122_, v___y_1104_, v___y_1105_, lean_box(0));
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1134_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1134_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1134_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v_a_1124_);
v___x_1129_ = v___x_1120_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_del_object(v___x_1120_);
v_a_1135_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1123_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1123_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1102_, v_i_1113_);
v___x_1146_ = l_Lean_PersistentArray_toList___redArg(v_children_1114_);
v___x_1147_ = lean_box(0);
lean_inc_ref(v_postNode_1101_);
v___x_1148_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___redArg(v_preNode_1100_, v_postNode_1101_, v___x_1145_, v___x_1146_, v___x_1147_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1148_, 1);
lean_inc(v___y_1105_);
lean_inc_ref(v___y_1104_);
v___x_1150_ = lean_apply_7(v_postNode_1101_, v_val_1115_, v_i_1113_, v_children_1114_, v_a_1149_, v___y_1104_, v___y_1105_, lean_box(0));
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1155_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1150_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1150_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_val_1115_);
lean_dec_ref(v_children_1114_);
lean_dec_ref(v_i_1113_);
lean_dec_ref(v_postNode_1101_);
v_a_1168_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1148_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1148_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_val_1115_);
lean_dec_ref(v_children_1114_);
lean_dec_ref(v_i_1113_);
lean_dec_ref_known(v_x_1102_, 1);
lean_dec_ref(v_postNode_1101_);
lean_dec_ref(v_preNode_1100_);
v_a_1176_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1116_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1116_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
default: 
{
lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_x_1102_);
lean_dec_ref(v_postNode_1101_);
lean_dec_ref(v_preNode_1100_);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x_1103_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_x_1103_, 0);
lean_dec(v_unused_1192_);
v___x_1185_ = v_x_1103_;
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
else
{
lean_dec(v_x_1103_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1191_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_box(0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set_tag(v___x_1185_, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___redArg(lean_object* v_preNode_1193_, lean_object* v_postNode_1194_, lean_object* v___x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
if (lean_obj_tag(v_x_1196_) == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v___x_1195_);
lean_dec_ref(v_postNode_1194_);
lean_dec_ref(v_preNode_1193_);
v___x_1201_ = l_List_reverse___redArg(v_x_1197_);
v___x_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
return v___x_1202_;
}
else
{
lean_object* v_head_1203_; lean_object* v_tail_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1222_; 
v_head_1203_ = lean_ctor_get(v_x_1196_, 0);
v_tail_1204_ = lean_ctor_get(v_x_1196_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_x_1196_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1206_ = v_x_1196_;
v_isShared_1207_ = v_isSharedCheck_1222_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_tail_1204_);
lean_inc(v_head_1203_);
lean_dec(v_x_1196_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1222_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; 
lean_inc(v___x_1195_);
lean_inc_ref(v_postNode_1194_);
lean_inc_ref(v_preNode_1193_);
v___x_1208_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg(v_preNode_1193_, v_postNode_1194_, v___x_1195_, v_head_1203_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v_x_1197_);
lean_ctor_set(v___x_1206_, 0, v_a_1209_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1209_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_x_1197_);
v___x_1211_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
v_x_1196_ = v_tail_1204_;
v_x_1197_ = v___x_1211_;
goto _start;
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_del_object(v___x_1206_);
lean_dec(v_tail_1204_);
lean_dec(v_x_1197_);
lean_dec(v___x_1195_);
lean_dec_ref(v_postNode_1194_);
lean_dec_ref(v_preNode_1193_);
v_a_1214_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1208_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1208_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___redArg___boxed(lean_object* v_preNode_1223_, lean_object* v_postNode_1224_, lean_object* v___x_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___redArg(v_preNode_1223_, v_postNode_1224_, v___x_1225_, v_x_1226_, v_x_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg___boxed(lean_object* v_preNode_1232_, lean_object* v_postNode_1233_, lean_object* v_x_1234_, lean_object* v_x_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg(v_preNode_1232_, v_postNode_1233_, v_x_1234_, v_x_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7(lean_object* v_preNode_1240_, lean_object* v_postNode_1241_, lean_object* v_ctx_x3f_1242_, lean_object* v_t_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___f_1247_; lean_object* v___x_1248_; 
v___f_1247_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1247_, 0, v_postNode_1241_);
v___x_1248_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg(v_preNode_1240_, v___f_1247_, v_ctx_x3f_1242_, v_t_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1256_; 
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1248_, 0);
lean_dec(v_unused_1257_);
v___x_1250_ = v___x_1248_;
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
else
{
lean_dec(v___x_1248_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_box(0);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v_a_1258_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1248_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1248_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object* v_preNode_1266_, lean_object* v_postNode_1267_, lean_object* v_ctx_x3f_1268_, lean_object* v_t_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7(v_preNode_1266_, v_postNode_1267_, v_ctx_x3f_1268_, v_t_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__0(uint8_t v___x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_box(v___x_1274_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__0___boxed(lean_object* v___x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v___x_17245__boxed_1290_; lean_object* v_res_1291_; 
v___x_17245__boxed_1290_ = lean_unbox(v___x_1283_);
v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__0(v___x_17245__boxed_1290_, v_x_1284_, v_x_1285_, v_x_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec_ref(v_x_1286_);
lean_dec_ref(v_x_1285_);
lean_dec_ref(v_x_1284_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(uint8_t v___x_1292_, lean_object* v_val_1293_, lean_object* v_as_1294_, size_t v_sz_1295_, size_t v_i_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_lt(v_i_1296_, v_sz_1295_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_dec(v_val_1293_);
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_b_1297_);
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; lean_object* v___f_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1303_ = lean_box(v___x_1292_);
v___f_1304_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1304_, 0, v___x_1303_);
v___x_1305_ = lean_box(v___x_1292_);
lean_inc(v_val_1293_);
v___f_1306_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1306_, 0, v_val_1293_);
lean_closure_set(v___f_1306_, 1, v___x_1305_);
v_a_1307_ = lean_array_uget_borrowed(v_as_1294_, v_i_1296_);
v___x_1308_ = lean_box(0);
lean_inc(v_a_1307_);
v___x_1309_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7(v___f_1304_, v___f_1306_, v___x_1308_, v_a_1307_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; 
lean_dec_ref_known(v___x_1309_, 1);
v___x_1310_ = lean_box(0);
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1296_, v___x_1311_);
v_i_1296_ = v___x_1312_;
v_b_1297_ = v___x_1310_;
goto _start;
}
else
{
lean_dec(v_val_1293_);
return v___x_1309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object* v___x_1314_, lean_object* v_val_1315_, lean_object* v_as_1316_, lean_object* v_sz_1317_, lean_object* v_i_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
uint8_t v___x_17270__boxed_1323_; size_t v_sz_boxed_1324_; size_t v_i_boxed_1325_; lean_object* v_res_1326_; 
v___x_17270__boxed_1323_ = lean_unbox(v___x_1314_);
v_sz_boxed_1324_ = lean_unbox_usize(v_sz_1317_);
lean_dec(v_sz_1317_);
v_i_boxed_1325_ = lean_unbox_usize(v_i_1318_);
lean_dec(v_i_1318_);
v_res_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___x_17270__boxed_1323_, v_val_1315_, v_as_1316_, v_sz_boxed_1324_, v_i_boxed_1325_, v_b_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec_ref(v_as_1316_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10_spec__16(lean_object* v_b_1327_, lean_object* v_acc_1328_, lean_object* v_i_1329_){
_start:
{
lean_object* v_keyArray_1334_; lean_object* v_valueArray_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_keyArray_1334_ = lean_ctor_get(v_b_1327_, 1);
v_valueArray_1335_ = lean_ctor_get(v_b_1327_, 2);
v___x_1336_ = lean_array_get_size(v_keyArray_1334_);
v___x_1337_ = lean_nat_dec_lt(v_i_1329_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec(v_i_1329_);
return v_acc_1328_;
}
else
{
lean_object* v___x_1338_; uint8_t v_isSome_1339_; 
v___x_1338_ = lean_array_fget_borrowed(v_keyArray_1334_, v_i_1329_);
v_isSome_1339_ = lean_noption_is_some(v___x_1338_);
if (v_isSome_1339_ == 0)
{
goto v___jp_1330_;
}
else
{
lean_object* v___x_1340_; uint8_t v_isSome_1341_; 
v___x_1340_ = lean_array_fget_borrowed(v_valueArray_1335_, v_i_1329_);
v_isSome_1341_ = lean_noption_is_some(v___x_1340_);
if (v_isSome_1341_ == 0)
{
goto v___jp_1330_;
}
else
{
lean_object* v_val_1342_; lean_object* v_val_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_inc(v___x_1338_);
v_val_1342_ = lean_noption_get(v___x_1338_);
lean_inc(v___x_1340_);
v_val_1343_ = lean_noption_get(v___x_1340_);
v___x_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_val_1342_);
lean_ctor_set(v___x_1344_, 1, v_val_1343_);
v___x_1345_ = lean_array_push(v_acc_1328_, v___x_1344_);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = lean_nat_add(v_i_1329_, v___x_1346_);
lean_dec(v_i_1329_);
v_acc_1328_ = v___x_1345_;
v_i_1329_ = v___x_1347_;
goto _start;
}
}
}
v___jp_1330_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_nat_add(v_i_1329_, v___x_1331_);
lean_dec(v_i_1329_);
v_i_1329_ = v___x_1332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10_spec__16___boxed(lean_object* v_b_1349_, lean_object* v_acc_1350_, lean_object* v_i_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10_spec__16(v_b_1349_, v_acc_1350_, v_i_1351_);
lean_dec_ref(v_b_1349_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10(lean_object* v_init_1353_, lean_object* v_b_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10_spec__16(v_b_1354_, v_init_1353_, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10___boxed(lean_object* v_init_1357_, lean_object* v_b_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_init_1357_, v_b_1358_);
lean_dec_ref(v_b_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___redArg(lean_object* v_hi_1360_, lean_object* v_pivot_1361_, lean_object* v_as_1362_, lean_object* v_i_1363_, lean_object* v_k_1364_){
_start:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_lt(v_k_1364_, v_hi_1360_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_k_1364_);
v___x_1366_ = lean_array_fswap(v_as_1362_, v_i_1363_, v_hi_1360_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_i_1363_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; lean_object* v_fst_1369_; lean_object* v_fst_1370_; lean_object* v_start_1371_; lean_object* v_start_1372_; uint8_t v___x_1373_; 
v___x_1368_ = lean_array_fget_borrowed(v_as_1362_, v_k_1364_);
v_fst_1369_ = lean_ctor_get(v___x_1368_, 0);
v_fst_1370_ = lean_ctor_get(v_pivot_1361_, 0);
v_start_1371_ = lean_ctor_get(v_fst_1369_, 0);
v_start_1372_ = lean_ctor_get(v_fst_1370_, 0);
v___x_1373_ = lean_nat_dec_lt(v_start_1371_, v_start_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_nat_add(v_k_1364_, v___x_1374_);
lean_dec(v_k_1364_);
v_k_1364_ = v___x_1375_;
goto _start;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1377_ = lean_array_fswap(v_as_1362_, v_i_1363_, v_k_1364_);
v___x_1378_ = lean_unsigned_to_nat(1u);
v___x_1379_ = lean_nat_add(v_i_1363_, v___x_1378_);
lean_dec(v_i_1363_);
v___x_1380_ = lean_nat_add(v_k_1364_, v___x_1378_);
lean_dec(v_k_1364_);
v_as_1362_ = v___x_1377_;
v_i_1363_ = v___x_1379_;
v_k_1364_ = v___x_1380_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___redArg___boxed(lean_object* v_hi_1382_, lean_object* v_pivot_1383_, lean_object* v_as_1384_, lean_object* v_i_1385_, lean_object* v_k_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___redArg(v_hi_1382_, v_pivot_1383_, v_as_1384_, v_i_1385_, v_k_1386_);
lean_dec_ref(v_pivot_1383_);
lean_dec(v_hi_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___lam__0(lean_object* v_x1_1388_, lean_object* v_x2_1389_){
_start:
{
lean_object* v_fst_1390_; lean_object* v_fst_1391_; lean_object* v_start_1392_; lean_object* v_start_1393_; uint8_t v___x_1394_; 
v_fst_1390_ = lean_ctor_get(v_x1_1388_, 0);
v_fst_1391_ = lean_ctor_get(v_x2_1389_, 0);
v_start_1392_ = lean_ctor_get(v_fst_1390_, 0);
v_start_1393_ = lean_ctor_get(v_fst_1391_, 0);
v___x_1394_ = lean_nat_dec_lt(v_start_1392_, v_start_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1395_, lean_object* v_x2_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___lam__0(v_x1_1395_, v_x2_1396_);
lean_dec_ref(v_x2_1396_);
lean_dec_ref(v_x1_1395_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg(lean_object* v_n_1399_, lean_object* v_as_1400_, lean_object* v_lo_1401_, lean_object* v_hi_1402_){
_start:
{
lean_object* v___y_1404_; uint8_t v___x_1414_; 
v___x_1414_ = lean_nat_dec_lt(v_lo_1401_, v_hi_1402_);
if (v___x_1414_ == 0)
{
lean_dec(v_lo_1401_);
return v_as_1400_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_mid_1417_; lean_object* v___y_1419_; lean_object* v___y_1425_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1415_ = lean_nat_add(v_lo_1401_, v_hi_1402_);
v___x_1416_ = lean_unsigned_to_nat(1u);
v_mid_1417_ = lean_nat_shiftr(v___x_1415_, v___x_1416_);
lean_dec(v___x_1415_);
v___x_1430_ = lean_array_fget_borrowed(v_as_1400_, v_mid_1417_);
v___x_1431_ = lean_array_fget_borrowed(v_as_1400_, v_lo_1401_);
v___x_1432_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___lam__0(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
v___y_1425_ = v_as_1400_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_array_fswap(v_as_1400_, v_lo_1401_, v_mid_1417_);
v___y_1425_ = v___x_1433_;
goto v___jp_1424_;
}
v___jp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_array_fget_borrowed(v___y_1419_, v_mid_1417_);
v___x_1421_ = lean_array_fget_borrowed(v___y_1419_, v_hi_1402_);
v___x_1422_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___lam__0(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_dec(v_mid_1417_);
v___y_1404_ = v___y_1419_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_array_fswap(v___y_1419_, v_mid_1417_, v_hi_1402_);
lean_dec(v_mid_1417_);
v___y_1404_ = v___x_1423_;
goto v___jp_1403_;
}
}
v___jp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1426_ = lean_array_fget_borrowed(v___y_1425_, v_hi_1402_);
v___x_1427_ = lean_array_fget_borrowed(v___y_1425_, v_lo_1401_);
v___x_1428_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___lam__0(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
v___y_1419_ = v___y_1425_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_array_fswap(v___y_1425_, v_lo_1401_, v_hi_1402_);
v___y_1419_ = v___x_1429_;
goto v___jp_1418_;
}
}
}
v___jp_1403_:
{
lean_object* v_pivot_1405_; lean_object* v___x_1406_; lean_object* v_fst_1407_; lean_object* v_snd_1408_; uint8_t v___x_1409_; 
v_pivot_1405_ = lean_array_fget(v___y_1404_, v_hi_1402_);
lean_inc_n(v_lo_1401_, 2);
v___x_1406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___redArg(v_hi_1402_, v_pivot_1405_, v___y_1404_, v_lo_1401_, v_lo_1401_);
lean_dec(v_pivot_1405_);
v_fst_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_fst_1407_);
v_snd_1408_ = lean_ctor_get(v___x_1406_, 1);
lean_inc(v_snd_1408_);
lean_dec_ref(v___x_1406_);
v___x_1409_ = lean_nat_dec_le(v_hi_1402_, v_fst_1407_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg(v_n_1399_, v_snd_1408_, v_lo_1401_, v_fst_1407_);
v___x_1411_ = lean_unsigned_to_nat(1u);
v___x_1412_ = lean_nat_add(v_fst_1407_, v___x_1411_);
lean_dec(v_fst_1407_);
v_as_1400_ = v___x_1410_;
v_lo_1401_ = v___x_1412_;
goto _start;
}
else
{
lean_dec(v_fst_1407_);
lean_dec(v_lo_1401_);
return v_snd_1408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg___boxed(lean_object* v_n_1434_, lean_object* v_as_1435_, lean_object* v_lo_1436_, lean_object* v_hi_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg(v_n_1434_, v_as_1435_, v_lo_1436_, v_hi_1437_);
lean_dec(v_hi_1437_);
lean_dec(v_n_1434_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(lean_object* v_o_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v_env_1443_; lean_object* v___x_1444_; lean_object* v_toEnvExtension_1445_; lean_object* v_asyncMode_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_merged_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v___x_1442_ = lean_st_ref_get(v___y_1440_);
v_env_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc_ref(v_env_1443_);
lean_dec(v___x_1442_);
v___x_1444_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_1445_ = lean_ctor_get(v___x_1444_, 0);
v_asyncMode_1446_ = lean_ctor_get(v_toEnvExtension_1445_, 2);
v___x_1447_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1447_, v___x_1444_, v_env_1443_, v_asyncMode_1446_, v___x_1448_);
v_merged_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1449_, 1);
lean_dec(v_unused_1459_);
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_merged_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v_merged_1450_);
lean_ctor_set(v___x_1452_, 0, v_o_1439_);
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_o_1439_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_merged_1450_);
v___x_1455_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(lean_object* v_o_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_1460_, v___y_1461_);
lean_dec(v___y_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; lean_object* v_scopes_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v_opts_1471_; lean_object* v___x_1472_; 
v___x_1467_ = lean_st_ref_get(v___y_1465_);
v_scopes_1468_ = lean_ctor_get(v___x_1467_, 2);
lean_inc(v_scopes_1468_);
lean_dec(v___x_1467_);
v___x_1469_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1470_ = l_List_head_x21___redArg(v___x_1469_, v_scopes_1468_);
lean_dec(v_scopes_1468_);
v_opts_1471_ = lean_ctor_get(v___x_1470_, 1);
lean_inc_ref(v_opts_1471_);
lean_dec(v___x_1470_);
v___x_1472_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_opts_1471_, v___y_1465_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object* v_upperBound_1477_, lean_object* v_snd_1478_, lean_object* v_fst_1479_, lean_object* v_a_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_a_1486_; uint8_t v___x_1490_; 
v___x_1490_ = lean_nat_dec_lt(v_a_1480_, v_upperBound_1477_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_dec(v_a_1480_);
lean_dec(v_fst_1479_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1481_);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; uint8_t v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = 0;
v___x_1494_ = lean_box(v___x_1493_);
v___x_1495_ = lean_array_get(v___x_1494_, v_snd_1478_, v_a_1480_);
lean_dec(v___x_1494_);
v___x_1496_ = lean_unbox(v___x_1495_);
lean_dec(v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_inc(v_a_1480_);
lean_inc(v_fst_1479_);
v___x_1497_ = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed), 5, 2);
lean_closure_set(v___x_1497_, 0, v_fst_1479_);
lean_closure_set(v___x_1497_, 1, v_a_1480_);
v___x_1498_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1497_, v___y_1482_, v___y_1483_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_dec_ref_known(v___x_1498_, 1);
v_a_1486_ = v___x_1492_;
goto v___jp_1485_;
}
else
{
lean_dec(v_a_1480_);
lean_dec(v_fst_1479_);
return v___x_1498_;
}
}
else
{
v_a_1486_ = v___x_1492_;
goto v___jp_1485_;
}
}
v___jp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_add(v_a_1480_, v___x_1487_);
lean_dec(v_a_1480_);
v_a_1480_ = v___x_1488_;
v_b_1481_ = v_a_1486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object* v_upperBound_1499_, lean_object* v_snd_1500_, lean_object* v_fst_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_1499_, v_snd_1500_, v_fst_1501_, v_a_1502_, v_b_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v_snd_1500_);
lean_dec(v_upperBound_1499_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object* v_as_1508_, size_t v_sz_1509_, size_t v_i_1510_, lean_object* v_b_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_lt(v_i_1510_, v_sz_1509_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_b_1511_);
return v___x_1516_;
}
else
{
lean_object* v_a_1517_; lean_object* v_snd_1518_; lean_object* v_fst_1519_; lean_object* v_snd_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1517_ = lean_array_uget_borrowed(v_as_1508_, v_i_1510_);
v_snd_1518_ = lean_ctor_get(v_a_1517_, 1);
v_fst_1519_ = lean_ctor_get(v_snd_1518_, 0);
v_snd_1520_ = lean_ctor_get(v_snd_1518_, 1);
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_array_get_size(v_snd_1520_);
v___x_1523_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_1519_);
v___x_1524_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_1522_, v_snd_1520_, v_fst_1519_, v___x_1523_, v___x_1521_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1524_) == 0)
{
size_t v___x_1525_; size_t v___x_1526_; 
lean_dec_ref_known(v___x_1524_, 1);
v___x_1525_ = ((size_t)1ULL);
v___x_1526_ = lean_usize_add(v_i_1510_, v___x_1525_);
v_i_1510_ = v___x_1526_;
v_b_1511_ = v___x_1521_;
goto _start;
}
else
{
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object* v_as_1528_, lean_object* v_sz_1529_, lean_object* v_i_1530_, lean_object* v_b_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
size_t v_sz_boxed_1535_; size_t v_i_boxed_1536_; lean_object* v_res_1537_; 
v_sz_boxed_1535_ = lean_unbox_usize(v_sz_1529_);
lean_dec(v_sz_1529_);
v_i_boxed_1536_ = lean_unbox_usize(v_i_1530_);
lean_dec(v_i_1530_);
v_res_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__9(v_as_1528_, v_sz_boxed_1535_, v_i_boxed_1536_, v_b_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_as_1528_);
return v_res_1537_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0(void){
_start:
{
lean_object* v_cellCount_1538_; lean_object* v___x_1539_; 
v_cellCount_1538_ = lean_unsigned_to_nat(16u);
v___x_1539_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1(void){
_start:
{
lean_object* v_cellCount_1540_; lean_object* v___x_1541_; 
v_cellCount_1540_ = lean_unsigned_to_nat(16u);
v___x_1541_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1540_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1542_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__1, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1);
v___x_1543_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__0, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___x_1543_);
lean_ctor_set(v___x_1545_, 2, v___x_1542_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0(lean_object* v_cmdStx_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1606_; 
v___x_1550_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_1547_, v___y_1548_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1606_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1606_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_1556_ = l_Lean_Linter_getLinterValue(v___x_1555_, v_a_1551_);
lean_dec(v_a_1551_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(0);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1557_);
v___x_1559_ = v___x_1553_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
uint8_t v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = 0;
v___x_1562_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1546_, v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 1)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_infoState_1567_; lean_object* v_trees_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; size_t v_sz_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1562_, 1);
lean_del_object(v___x_1553_);
v___x_1563_ = lean_st_ref_get(v___y_1548_);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__2, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__2_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__2);
v___x_1566_ = lean_st_mk_ref(v___x_1565_);
v_infoState_1567_ = lean_ctor_get(v___x_1563_, 8);
lean_inc_ref(v_infoState_1567_);
lean_dec(v___x_1563_);
v_trees_1568_ = lean_ctor_get(v_infoState_1567_, 2);
lean_inc_ref(v_trees_1568_);
lean_dec_ref(v_infoState_1567_);
v___x_1569_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1568_);
lean_dec_ref(v_trees_1568_);
v___x_1570_ = lean_box(0);
v_sz_1571_ = lean_array_size(v___x_1569_);
v___x_1572_ = ((size_t)0ULL);
lean_inc(v___x_1566_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___x_1556_, v___x_1566_, v___x_1569_, v_sz_1571_, v___x_1572_, v___x_1570_, v___y_1547_, v___y_1548_);
lean_dec_ref(v___x_1569_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; lean_object* v___y_1576_; lean_object* v_size_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___x_1595_; 
lean_dec_ref_known(v___x_1573_, 1);
v___x_1574_ = lean_st_ref_get(v___x_1566_);
lean_dec(v___x_1566_);
v_size_1587_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_size_1587_);
v___x_1588_ = lean_mk_empty_array_with_capacity(v_size_1587_);
lean_dec(v_size_1587_);
v___x_1589_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Linter_unusedSimpArgs_spec__10(v___x_1588_, v___x_1574_);
lean_dec(v___x_1574_);
v___x_1590_ = lean_array_get_size(v___x_1589_);
v___x_1595_ = lean_nat_dec_eq(v___x_1590_, v___x_1564_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___y_1599_; uint8_t v___x_1601_; 
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_nat_sub(v___x_1590_, v___x_1596_);
v___x_1601_ = lean_nat_dec_le(v___x_1564_, v___x_1597_);
if (v___x_1601_ == 0)
{
lean_inc(v___x_1597_);
v___y_1599_ = v___x_1597_;
goto v___jp_1598_;
}
else
{
v___y_1599_ = v___x_1564_;
goto v___jp_1598_;
}
v___jp_1598_:
{
uint8_t v___x_1600_; 
v___x_1600_ = lean_nat_dec_le(v___y_1599_, v___x_1597_);
if (v___x_1600_ == 0)
{
lean_dec(v___x_1597_);
lean_inc(v___y_1599_);
v___y_1592_ = v___y_1599_;
v___y_1593_ = v___y_1599_;
goto v___jp_1591_;
}
else
{
v___y_1592_ = v___y_1599_;
v___y_1593_ = v___x_1597_;
goto v___jp_1591_;
}
}
}
else
{
v___y_1576_ = v___x_1589_;
goto v___jp_1575_;
}
v___jp_1575_:
{
size_t v_sz_1577_; lean_object* v___x_1578_; 
v_sz_1577_ = lean_array_size(v___y_1576_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__9(v___y_1576_, v_sz_1577_, v___x_1572_, v___x_1570_, v___y_1547_, v___y_1548_);
lean_dec_ref(v___y_1576_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v___x_1578_, 0);
lean_dec(v_unused_1586_);
v___x_1580_ = v___x_1578_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v___x_1578_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1570_);
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1570_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
return v___x_1578_;
}
}
v___jp_1591_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg(v___x_1590_, v___x_1589_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
v___y_1576_ = v___x_1594_;
goto v___jp_1575_;
}
}
else
{
lean_dec(v___x_1566_);
return v___x_1573_;
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
lean_dec(v___x_1562_);
v___x_1602_ = lean_box(0);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1602_);
v___x_1604_ = v___x_1553_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___boxed(lean_object* v_cmdStx_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v_cmdStx_1607_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(lean_object* v_o_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_1623_, v___y_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(lean_object* v_o_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object* v_00_u03b2_1633_, lean_object* v_m_1634_, lean_object* v_query_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_1634_, v_query_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_m_1638_, lean_object* v_query_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1(v_00_u03b2_1637_, v_m_1638_, v_query_1639_);
lean_dec_ref(v_query_1639_);
lean_dec_ref(v_m_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object* v_00_u03b2_1641_, lean_object* v_m_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object* v_00_u03b2_1644_, lean_object* v_m_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2(v_00_u03b2_1644_, v_m_1645_);
lean_dec_ref(v_m_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3(lean_object* v_00_u03b2_1647_, lean_object* v_m_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___redArg(v_m_1648_, v_a_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object* v_00_u03b2_1651_, lean_object* v_m_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3(v_00_u03b2_1651_, v_m_1652_, v_a_1653_);
lean_dec_ref(v_a_1653_);
lean_dec_ref(v_m_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object* v_00_u03b1_1655_, lean_object* v_ref_1656_, lean_object* v_msg_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___redArg(v_ref_1656_, v_msg_1657_, v___y_1658_, v___y_1659_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object* v_00_u03b1_1662_, lean_object* v_ref_1663_, lean_object* v_msg_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5(v_00_u03b1_1662_, v_ref_1663_, v_msg_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v_ref_1663_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object* v_upperBound_1669_, lean_object* v_snd_1670_, lean_object* v_fst_1671_, lean_object* v_inst_1672_, lean_object* v_R_1673_, lean_object* v_a_1674_, lean_object* v_b_1675_, lean_object* v_c_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_1669_, v_snd_1670_, v_fst_1671_, v_a_1674_, v_b_1675_, v___y_1677_, v___y_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object* v_upperBound_1681_, lean_object* v_snd_1682_, lean_object* v_fst_1683_, lean_object* v_inst_1684_, lean_object* v_R_1685_, lean_object* v_a_1686_, lean_object* v_b_1687_, lean_object* v_c_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(v_upperBound_1681_, v_snd_1682_, v_fst_1683_, v_inst_1684_, v_R_1685_, v_a_1686_, v_b_1687_, v_c_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec_ref(v_snd_1682_);
lean_dec(v_upperBound_1681_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11(lean_object* v_n_1693_, lean_object* v_as_1694_, lean_object* v_lo_1695_, lean_object* v_hi_1696_, lean_object* v_w_1697_, lean_object* v_hlo_1698_, lean_object* v_hhi_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___redArg(v_n_1693_, v_as_1694_, v_lo_1695_, v_hi_1696_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(lean_object* v_n_1701_, lean_object* v_as_1702_, lean_object* v_lo_1703_, lean_object* v_hi_1704_, lean_object* v_w_1705_, lean_object* v_hlo_1706_, lean_object* v_hhi_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11(v_n_1701_, v_as_1702_, v_lo_1703_, v_hi_1704_, v_w_1705_, v_hlo_1706_, v_hhi_1707_);
lean_dec(v_hi_1704_);
lean_dec(v_n_1701_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object* v_00_u03b2_1709_, lean_object* v_m_1710_, lean_object* v_query_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_m_1710_, v_query_1711_, v_x_1712_, v_x_1713_, v_x_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1717_, lean_object* v_m_1718_, lean_object* v_query_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_1717_, v_m_1718_, v_query_1719_, v_x_1720_, v_x_1721_, v_x_1722_, v_x_1723_);
lean_dec_ref(v_query_1719_);
lean_dec_ref(v_m_1718_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4(lean_object* v_00_u03b2_1725_, lean_object* v_init_1726_, lean_object* v_b_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___redArg(v_init_1726_, v_b_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1729_, lean_object* v_init_1730_, lean_object* v_b_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4(v_00_u03b2_1729_, v_init_1730_, v_b_1731_);
lean_dec_ref(v_b_1731_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6(lean_object* v_00_u03b2_1733_, lean_object* v_m_1734_, lean_object* v_query_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___redArg(v_m_1734_, v_query_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1737_, lean_object* v_m_1738_, lean_object* v_query_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__3_spec__6(v_00_u03b2_1737_, v_m_1738_, v_query_1739_);
lean_dec_ref(v_query_1739_);
lean_dec_ref(v_m_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11(lean_object* v_msgData_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___redArg(v_msgData_1741_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11___boxed(lean_object* v_msgData_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__11(v_msgData_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9(lean_object* v_00_u03b1_1751_, lean_object* v_msg_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___redArg(v_msg_1752_, v___y_1753_, v___y_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_msg_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9(v_00_u03b1_1757_, v_msg_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16(lean_object* v_00_u03b1_1763_, lean_object* v_msg_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___redArg(v_msg_1764_, v___y_1765_, v___y_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16___boxed(lean_object* v_00_u03b1_1769_, lean_object* v_msg_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__16(v_00_u03b1_1769_, v_msg_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12(lean_object* v_00_u03b1_1775_, lean_object* v_preNode_1776_, lean_object* v_postNode_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___redArg(v_preNode_1776_, v_postNode_1777_, v_x_1778_, v_x_1779_, v___y_1780_, v___y_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12___boxed(lean_object* v_00_u03b1_1784_, lean_object* v_preNode_1785_, lean_object* v_postNode_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12(v_00_u03b1_1784_, v_preNode_1785_, v_postNode_1786_, v_x_1787_, v_x_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18(lean_object* v_n_1793_, lean_object* v_lo_1794_, lean_object* v_hi_1795_, lean_object* v_hhi_1796_, lean_object* v_pivot_1797_, lean_object* v_as_1798_, lean_object* v_i_1799_, lean_object* v_k_1800_, lean_object* v_ilo_1801_, lean_object* v_ik_1802_, lean_object* v_w_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___redArg(v_hi_1795_, v_pivot_1797_, v_as_1798_, v_i_1799_, v_k_1800_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18___boxed(lean_object* v_n_1805_, lean_object* v_lo_1806_, lean_object* v_hi_1807_, lean_object* v_hhi_1808_, lean_object* v_pivot_1809_, lean_object* v_as_1810_, lean_object* v_i_1811_, lean_object* v_k_1812_, lean_object* v_ilo_1813_, lean_object* v_ik_1814_, lean_object* v_w_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__11_spec__18(v_n_1805_, v_lo_1806_, v_hi_1807_, v_hhi_1808_, v_pivot_1809_, v_as_1810_, v_i_1811_, v_k_1812_, v_ilo_1813_, v_ik_1814_, v_w_1815_);
lean_dec_ref(v_pivot_1809_);
lean_dec(v_hi_1807_);
lean_dec(v_lo_1806_);
lean_dec(v_n_1805_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1817_, lean_object* v_b_1818_, lean_object* v_acc_1819_, lean_object* v_i_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___redArg(v_b_1818_, v_acc_1819_, v_i_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1822_, lean_object* v_b_1823_, lean_object* v_acc_1824_, lean_object* v_i_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__4_spec__5(v_00_u03b2_1822_, v_b_1823_, v_acc_1824_, v_i_1825_);
lean_dec_ref(v_b_1823_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12(lean_object* v_msgData_1827_, lean_object* v_macroStack_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___redArg(v_msgData_1827_, v_macroStack_1828_, v___y_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12___boxed(lean_object* v_msgData_1833_, lean_object* v_macroStack_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__9_spec__12(v_msgData_1833_, v_macroStack_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17(lean_object* v_00_u03b1_1839_, lean_object* v_preNode_1840_, lean_object* v_postNode_1841_, lean_object* v___x_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___redArg(v_preNode_1840_, v_postNode_1841_, v___x_1842_, v_x_1843_, v_x_1844_, v___y_1845_, v___y_1846_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17___boxed(lean_object* v_00_u03b1_1849_, lean_object* v_preNode_1850_, lean_object* v_postNode_1851_, lean_object* v___x_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__7_spec__12_spec__17(v_00_u03b1_1849_, v_preNode_1850_, v_postNode_1851_, v___x_1852_, v_x_1853_, v_x_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_Lean_Linter_unusedSimpArgs));
v___x_1861_ = l_Lean_Elab_Command_addLinter(v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
return v_res_1863_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_UnusedSimpArgs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_UnusedSimpArgs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_UnusedSimpArgs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_UnusedSimpArgs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_UnusedSimpArgs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_UnusedSimpArgs(builtin);
}
#ifdef __cplusplus
}
#endif
