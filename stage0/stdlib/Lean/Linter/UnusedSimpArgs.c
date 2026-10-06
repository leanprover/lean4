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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_linter_unusedSimpArgs;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_getSimpParams(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setSimpParams(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "This simp argument is unused:"};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2_value;
static lean_once_cell_t l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3;
static const lean_array_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4_value;
static const lean_string_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Omit it from the simp argument list."};
static const lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5 = (const lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_value;
static const lean_ctor_object l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_value)}};
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Simp argument mask size mismatch: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " vs. "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(5, 49, 55, 92, 153, 191, 153, 249)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___closed__0;
static lean_once_cell_t l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___closed__1;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(lean_object*, lean_object*, lean_object*);
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
v___x_24_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_27_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
lean_ctor_set(v___x_30_, 3, v___x_29_);
lean_ctor_set(v___x_30_, 4, v___x_28_);
lean_ctor_set(v___x_30_, 5, v___x_28_);
lean_ctor_set(v___x_30_, 6, v___x_28_);
lean_ctor_set(v___x_30_, 7, v___x_28_);
lean_ctor_set(v___x_30_, 8, v___x_28_);
lean_ctor_set(v___x_30_, 9, v___x_28_);
lean_ctor_set(v___x_30_, 10, v___x_28_);
lean_ctor_set(v___x_30_, 11, v___x_27_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_unsigned_to_nat(32u);
v___x_32_ = lean_mk_empty_array_with_capacity(v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4(void){
_start:
{
size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = ((size_t)5ULL);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_unsigned_to_nat(32u);
v___x_37_ = lean_mk_empty_array_with_capacity(v___x_36_);
v___x_38_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3);
v___x_39_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_35_);
lean_ctor_set(v___x_39_, 3, v___x_35_);
lean_ctor_set_usize(v___x_39_, 4, v___x_34_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_box(1);
v___x_41_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4);
v___x_42_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
v___x_43_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set(v___x_43_, 2, v___x_40_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(lean_object* v_msgData_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_48_; lean_object* v_toCold_49_; lean_object* v_env_50_; lean_object* v_options_51_; uint8_t v___x_52_; lean_object* v_env_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_48_ = lean_st_ref_get(v___y_46_);
v_toCold_49_ = lean_ctor_get(v___y_45_, 0);
v_env_50_ = lean_ctor_get(v___x_48_, 0);
lean_inc_ref(v_env_50_);
lean_dec(v___x_48_);
v_options_51_ = lean_ctor_get(v_toCold_49_, 2);
v___x_52_ = 0;
v_env_53_ = l_Lean_Environment_setRecordingDeps(v_env_50_, v___x_52_);
v___x_54_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_55_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_51_);
v___x_56_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_56_, 0, v_env_53_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
lean_ctor_set(v___x_56_, 2, v___x_55_);
lean_ctor_set(v___x_56_, 3, v_options_51_);
v___x_57_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v_msgData_44_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___boxed(lean_object* v_msgData_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msgData_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(lean_object* v_msg_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_ref_68_; lean_object* v___x_69_; lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_78_; 
v_ref_68_ = lean_ctor_get(v___y_65_, 2);
v___x_69_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msg_64_, v___y_65_, v___y_66_);
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_78_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
lean_inc(v_ref_68_);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v_ref_68_);
lean_ctor_set(v___x_74_, 1, v_a_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set_tag(v___x_72_, 1);
lean_ctor_set(v___x_72_, 0, v___x_74_);
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg___boxed(lean_object* v_msg_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_83_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_92_, uint8_t v___y_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_94_) == 1)
{
lean_object* v_pre_95_; 
v_pre_95_ = lean_ctor_get(v_x_94_, 0);
switch(lean_obj_tag(v_pre_95_))
{
case 1:
{
lean_object* v_pre_96_; 
v_pre_96_ = lean_ctor_get(v_pre_95_, 0);
switch(lean_obj_tag(v_pre_96_))
{
case 0:
{
lean_object* v_str_97_; lean_object* v_str_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_str_97_ = lean_ctor_get(v_x_94_, 1);
v_str_98_ = lean_ctor_get(v_pre_95_, 1);
v___x_99_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_100_ = lean_string_dec_eq(v_str_98_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_102_ = lean_string_dec_eq(v_str_98_, v___x_101_);
if (v___x_102_ == 0)
{
return v___x_102_;
}
else
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_104_ = lean_string_dec_eq(v_str_97_, v___x_103_);
if (v___x_104_ == 0)
{
return v___x_104_;
}
else
{
return v_suppressElabErrors_92_;
}
}
}
else
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_106_ = lean_string_dec_eq(v_str_97_, v___x_105_);
if (v___x_106_ == 0)
{
return v___x_106_;
}
else
{
return v_suppressElabErrors_92_;
}
}
}
case 1:
{
lean_object* v_pre_107_; 
v_pre_107_ = lean_ctor_get(v_pre_96_, 0);
if (lean_obj_tag(v_pre_107_) == 0)
{
lean_object* v_str_108_; lean_object* v_str_109_; lean_object* v_str_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_str_108_ = lean_ctor_get(v_x_94_, 1);
v_str_109_ = lean_ctor_get(v_pre_95_, 1);
v_str_110_ = lean_ctor_get(v_pre_96_, 1);
v___x_111_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_112_ = lean_string_dec_eq(v_str_110_, v___x_111_);
if (v___x_112_ == 0)
{
return v___x_112_;
}
else
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_114_ = lean_string_dec_eq(v_str_109_, v___x_113_);
if (v___x_114_ == 0)
{
return v___x_114_;
}
else
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_116_ = lean_string_dec_eq(v_str_108_, v___x_115_);
if (v___x_116_ == 0)
{
return v___x_116_;
}
else
{
return v_suppressElabErrors_92_;
}
}
}
}
else
{
return v___y_93_;
}
}
default: 
{
return v___y_93_;
}
}
}
case 0:
{
lean_object* v_str_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_str_117_ = lean_ctor_get(v_x_94_, 1);
v___x_118_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_119_ = lean_string_dec_eq(v_str_117_, v___x_118_);
if (v___x_119_ == 0)
{
return v___x_119_;
}
else
{
return v_suppressElabErrors_92_;
}
}
default: 
{
return v___y_93_;
}
}
}
else
{
return v___y_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_120_, lean_object* v___y_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_suppressElabErrors_boxed_123_; uint8_t v___y_4819__boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_suppressElabErrors_boxed_123_ = lean_unbox(v_suppressElabErrors_120_);
v___y_4819__boxed_124_ = lean_unbox(v___y_121_);
v_res_125_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_123_, v___y_4819__boxed_124_, v_x_122_);
lean_dec(v_x_122_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_127_, lean_object* v_opt_128_){
_start:
{
lean_object* v_name_129_; lean_object* v_defValue_130_; lean_object* v_map_131_; lean_object* v___x_132_; 
v_name_129_ = lean_ctor_get(v_opt_128_, 0);
v_defValue_130_ = lean_ctor_get(v_opt_128_, 1);
v_map_131_ = lean_ctor_get(v_opts_127_, 0);
v___x_132_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_131_, v_name_129_);
if (lean_obj_tag(v___x_132_) == 0)
{
uint8_t v___x_133_; 
v___x_133_ = lean_unbox(v_defValue_130_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; 
v_val_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v___x_132_, 1);
if (lean_obj_tag(v_val_134_) == 1)
{
uint8_t v_v_135_; 
v_v_135_ = lean_ctor_get_uint8(v_val_134_, 0);
lean_dec_ref_known(v_val_134_, 0);
return v_v_135_;
}
else
{
uint8_t v___x_136_; 
lean_dec(v_val_134_);
v___x_136_ = lean_unbox(v_defValue_130_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_137_, v_opt_138_);
lean_dec_ref(v_opt_138_);
lean_dec_ref(v_opts_137_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(lean_object* v_ref_142_, lean_object* v_msgData_143_, uint8_t v_severity_144_, uint8_t v_isSilent_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___y_150_; lean_object* v___y_151_; uint8_t v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; uint8_t v___y_155_; lean_object* v___y_156_; lean_object* v_toCold_157_; lean_object* v___y_158_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; uint8_t v___y_191_; uint8_t v___y_192_; uint8_t v___y_193_; lean_object* v___y_194_; lean_object* v___y_214_; lean_object* v___y_215_; uint8_t v___y_216_; lean_object* v___y_217_; uint8_t v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; uint8_t v___y_224_; uint8_t v___y_225_; uint8_t v___y_226_; uint8_t v___x_237_; uint8_t v___y_239_; uint8_t v___y_240_; uint8_t v___y_241_; uint8_t v___y_243_; uint8_t v___x_251_; 
v___x_237_ = 2;
v___x_251_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_237_);
if (v___x_251_ == 0)
{
v___y_243_ = v___x_251_;
goto v___jp_242_;
}
else
{
uint8_t v___x_252_; 
lean_inc_ref(v_msgData_143_);
v___x_252_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_143_);
v___y_243_ = v___x_252_;
goto v___jp_242_;
}
v___jp_149_:
{
lean_object* v_currNamespace_159_; lean_object* v_openDecls_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v_env_165_; lean_object* v_nextMacroScope_166_; lean_object* v_ngen_167_; lean_object* v_auxDeclNGen_168_; lean_object* v_traceState_169_; lean_object* v_cache_170_; lean_object* v_recordedDeps_171_; lean_object* v_messages_172_; lean_object* v_infoState_173_; lean_object* v_snapshotTasks_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_185_; 
v_currNamespace_159_ = lean_ctor_get(v_toCold_157_, 4);
v_openDecls_160_ = lean_ctor_get(v_toCold_157_, 5);
lean_inc(v_openDecls_160_);
lean_inc(v_currNamespace_159_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v_currNamespace_159_);
lean_ctor_set(v___x_161_, 1, v_openDecls_160_);
v___x_162_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___y_156_);
lean_inc_ref(v___y_150_);
lean_inc_ref(v___y_153_);
v___x_163_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_163_, 0, v___y_153_);
lean_ctor_set(v___x_163_, 1, v___y_151_);
lean_ctor_set(v___x_163_, 2, v___y_154_);
lean_ctor_set(v___x_163_, 3, v___y_150_);
lean_ctor_set(v___x_163_, 4, v___x_162_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*5, v___y_155_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*5 + 1, v___y_152_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*5 + 2, v_isSilent_145_);
v___x_164_ = lean_st_ref_take(v___y_158_);
v_env_165_ = lean_ctor_get(v___x_164_, 0);
v_nextMacroScope_166_ = lean_ctor_get(v___x_164_, 1);
v_ngen_167_ = lean_ctor_get(v___x_164_, 2);
v_auxDeclNGen_168_ = lean_ctor_get(v___x_164_, 3);
v_traceState_169_ = lean_ctor_get(v___x_164_, 4);
v_cache_170_ = lean_ctor_get(v___x_164_, 5);
v_recordedDeps_171_ = lean_ctor_get(v___x_164_, 6);
v_messages_172_ = lean_ctor_get(v___x_164_, 7);
v_infoState_173_ = lean_ctor_get(v___x_164_, 8);
v_snapshotTasks_174_ = lean_ctor_get(v___x_164_, 9);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_185_ == 0)
{
v___x_176_ = v___x_164_;
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_snapshotTasks_174_);
lean_inc(v_infoState_173_);
lean_inc(v_messages_172_);
lean_inc(v_recordedDeps_171_);
lean_inc(v_cache_170_);
lean_inc(v_traceState_169_);
lean_inc(v_auxDeclNGen_168_);
lean_inc(v_ngen_167_);
lean_inc(v_nextMacroScope_166_);
lean_inc(v_env_165_);
lean_dec(v___x_164_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_185_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_178_ = lean_box(0);
v___x_179_ = l_Lean_MessageLog_add(v___x_163_, v_messages_172_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 7, v___x_179_);
v___x_181_ = v___x_176_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_env_165_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_nextMacroScope_166_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_ngen_167_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_auxDeclNGen_168_);
lean_ctor_set(v_reuseFailAlloc_184_, 4, v_traceState_169_);
lean_ctor_set(v_reuseFailAlloc_184_, 5, v_cache_170_);
lean_ctor_set(v_reuseFailAlloc_184_, 6, v_recordedDeps_171_);
lean_ctor_set(v_reuseFailAlloc_184_, 7, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_184_, 8, v_infoState_173_);
lean_ctor_set(v_reuseFailAlloc_184_, 9, v_snapshotTasks_174_);
v___x_181_ = v_reuseFailAlloc_184_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_st_ref_put(v___y_158_, v___x_181_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_178_);
return v___x_183_;
}
}
}
v___jp_186_:
{
lean_object* v_fileName_195_; lean_object* v_fileMap_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_212_; 
v_fileName_195_ = lean_ctor_get(v___y_190_, 0);
v_fileMap_196_ = lean_ctor_get(v___y_190_, 1);
v___x_197_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_143_);
v___x_198_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v___x_197_, v___y_146_, v___y_147_);
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_212_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_212_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
lean_inc_ref_n(v_fileMap_196_, 2);
v___x_203_ = l_Lean_FileMap_toPosition(v_fileMap_196_, v___y_189_);
lean_dec(v___y_189_);
v___x_204_ = l_Lean_FileMap_toPosition(v_fileMap_196_, v___y_194_);
lean_dec(v___y_194_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0));
if (v___y_191_ == 0)
{
lean_del_object(v___x_201_);
lean_dec_ref(v___y_188_);
v___y_150_ = v___x_206_;
v___y_151_ = v___x_203_;
v___y_152_ = v___y_192_;
v___y_153_ = v_fileName_195_;
v___y_154_ = v___x_205_;
v___y_155_ = v___y_193_;
v___y_156_ = v_a_199_;
v_toCold_157_ = v___y_187_;
v___y_158_ = v___y_147_;
goto v___jp_149_;
}
else
{
uint8_t v___x_207_; 
lean_inc(v_a_199_);
v___x_207_ = l_Lean_MessageData_hasTag(v___y_188_, v_a_199_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec_ref_known(v___x_205_, 1);
lean_dec_ref(v___x_203_);
lean_dec(v_a_199_);
v___x_208_ = lean_box(0);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_208_);
v___x_210_ = v___x_201_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
else
{
lean_del_object(v___x_201_);
v___y_150_ = v___x_206_;
v___y_151_ = v___x_203_;
v___y_152_ = v___y_192_;
v___y_153_ = v_fileName_195_;
v___y_154_ = v___x_205_;
v___y_155_ = v___y_193_;
v___y_156_ = v_a_199_;
v_toCold_157_ = v___y_187_;
v___y_158_ = v___y_147_;
goto v___jp_149_;
}
}
}
}
v___jp_213_:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Syntax_getTailPos_x3f(v___y_217_, v___y_219_);
lean_dec(v___y_217_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_inc(v___y_220_);
v___y_187_ = v___y_214_;
v___y_188_ = v___y_215_;
v___y_189_ = v___y_220_;
v___y_190_ = v___y_214_;
v___y_191_ = v___y_216_;
v___y_192_ = v___y_218_;
v___y_193_ = v___y_219_;
v___y_194_ = v___y_220_;
goto v___jp_186_;
}
else
{
lean_object* v_val_222_; 
v_val_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_222_);
lean_dec_ref_known(v___x_221_, 1);
v___y_187_ = v___y_214_;
v___y_188_ = v___y_215_;
v___y_189_ = v___y_220_;
v___y_190_ = v___y_214_;
v___y_191_ = v___y_216_;
v___y_192_ = v___y_218_;
v___y_193_ = v___y_219_;
v___y_194_ = v_val_222_;
goto v___jp_186_;
}
}
v___jp_223_:
{
lean_object* v_toCold_227_; lean_object* v_ref_228_; uint8_t v_suppressElabErrors_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v_ref_233_; lean_object* v___x_234_; 
v_toCold_227_ = lean_ctor_get(v___y_146_, 0);
v_ref_228_ = lean_ctor_get(v___y_146_, 2);
v_suppressElabErrors_229_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 2);
v___x_230_ = lean_box(v_suppressElabErrors_229_);
v___x_231_ = lean_box(v___y_224_);
v___f_232_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_232_, 0, v___x_230_);
lean_closure_set(v___f_232_, 1, v___x_231_);
v_ref_233_ = l_Lean_replaceRef(v_ref_142_, v_ref_228_);
v___x_234_ = l_Lean_Syntax_getPos_x3f(v_ref_233_, v___y_225_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___y_214_ = v_toCold_227_;
v___y_215_ = v___f_232_;
v___y_216_ = v_suppressElabErrors_229_;
v___y_217_ = v_ref_233_;
v___y_218_ = v___y_226_;
v___y_219_ = v___y_225_;
v___y_220_ = v___x_235_;
goto v___jp_213_;
}
else
{
lean_object* v_val_236_; 
v_val_236_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v___x_234_, 1);
v___y_214_ = v_toCold_227_;
v___y_215_ = v___f_232_;
v___y_216_ = v_suppressElabErrors_229_;
v___y_217_ = v_ref_233_;
v___y_218_ = v___y_226_;
v___y_219_ = v___y_225_;
v___y_220_ = v_val_236_;
goto v___jp_213_;
}
}
v___jp_238_:
{
if (v___y_241_ == 0)
{
v___y_224_ = v___y_239_;
v___y_225_ = v___y_240_;
v___y_226_ = v_severity_144_;
goto v___jp_223_;
}
else
{
v___y_224_ = v___y_239_;
v___y_225_ = v___y_240_;
v___y_226_ = v___x_237_;
goto v___jp_223_;
}
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
uint8_t v___x_244_; uint8_t v___x_245_; 
v___x_244_ = 1;
v___x_245_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_244_);
if (v___x_245_ == 0)
{
v___y_239_ = v___y_243_;
v___y_240_ = v___y_243_;
v___y_241_ = v___x_245_;
goto v___jp_238_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_246_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_146_);
v___x_247_ = l_Lean_warningAsError;
v___x_248_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v___x_246_, v___x_247_);
lean_dec_ref(v___x_246_);
v___y_239_ = v___y_243_;
v___y_240_ = v___y_243_;
v___y_241_ = v___x_248_;
goto v___jp_238_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v_msgData_143_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_253_, lean_object* v_msgData_254_, lean_object* v_severity_255_, lean_object* v_isSilent_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
uint8_t v_severity_boxed_260_; uint8_t v_isSilent_boxed_261_; lean_object* v_res_262_; 
v_severity_boxed_260_ = lean_unbox(v_severity_255_);
v_isSilent_boxed_261_ = lean_unbox(v_isSilent_256_);
v_res_262_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_253_, v_msgData_254_, v_severity_boxed_260_, v_isSilent_boxed_261_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v_ref_253_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(lean_object* v_ref_263_, lean_object* v_msgData_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
uint8_t v___x_268_; uint8_t v___x_269_; lean_object* v___x_270_; 
v___x_268_ = 1;
v___x_269_ = 0;
v___x_270_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_263_, v_msgData_264_, v___x_268_, v___x_269_, v___y_265_, v___y_266_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(lean_object* v_ref_271_, lean_object* v_msgData_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_271_, v_msgData_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v_ref_271_);
return v_res_276_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2));
v___x_282_ = l_Lean_stringToMessageData(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(lean_object* v_linterOption_283_, lean_object* v_stx_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_name_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_307_; 
v_name_289_ = lean_ctor_get(v_linterOption_283_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v_linterOption_283_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v_linterOption_283_, 1);
lean_dec(v_unused_308_);
v___x_291_ = v_linterOption_283_;
v_isShared_292_ = v_isSharedCheck_307_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_name_289_);
lean_dec(v_linterOption_283_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_307_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_293_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1);
lean_inc(v_name_289_);
v___x_294_ = l_Lean_MessageData_ofName(v_name_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 7);
lean_ctor_set(v___x_291_, 1, v___x_294_);
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_296_ = v___x_291_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_306_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_disable_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_297_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3);
v___x_298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v_disable_299_ = l_Lean_MessageData_note(v___x_298_);
v___x_300_ = l_Lean_Linter_linterMessageTag;
v___x_301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_301_, 0, v_msg_285_);
lean_ctor_set(v___x_301_, 1, v_disable_299_);
v___x_302_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v___x_303_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_303_, 0, v_name_289_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
lean_inc(v_stx_284_);
v___x_304_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_304_, 0, v_stx_284_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_stx_284_, v___x_304_, v___y_286_, v___y_287_);
lean_dec(v_stx_284_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(lean_object* v_linterOption_309_, lean_object* v_stx_310_, lean_object* v_msg_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_309_, v_stx_310_, v_msg_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_315_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2));
v___x_321_ = l_Lean_stringToMessageData(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6));
v___x_328_ = l_Lean_MessageData_ofFormat(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12));
v___x_339_ = l_Lean_stringToMessageData(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13);
v___x_341_ = l_Lean_MessageData_note(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15));
v___x_344_ = l_Lean_stringToMessageData(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(lean_object* v_stx_348_, lean_object* v_i_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v_hint_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_simpArgs_364_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_362_ = lean_box(0);
v___x_363_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1));
v_simpArgs_364_ = l_Lean_Elab_Tactic_getSimpParams(v_stx_348_);
v___x_415_ = lean_array_get_size(v_simpArgs_364_);
v___x_416_ = lean_nat_dec_lt(v_i_349_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref(v_simpArgs_364_);
v___x_417_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16);
v___x_418_ = l_Nat_reprFast(v_i_349_);
v___x_419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
v___x_420_ = l_Lean_MessageData_ofFormat(v___x_419_);
v___x_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_417_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18);
v___x_423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = l_Lean_MessageData_ofSyntax(v_stx_348_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v___x_425_, v_a_350_, v_a_351_);
return v___x_426_;
}
else
{
v___y_366_ = v_a_350_;
v___y_367_ = v_a_351_;
goto v___jp_365_;
}
v___jp_353_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___y_355_);
lean_ctor_set(v___x_360_, 1, v_hint_356_);
v___x_361_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_359_, v___y_354_, v___x_360_, v___y_357_, v___y_358_);
return v___x_361_;
}
v___jp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_argStx_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_msg_374_; lean_object* v_otherArgs_375_; lean_object* v___x_376_; 
v___x_368_ = lean_array_get_size(v_simpArgs_364_);
v___x_369_ = lean_unsigned_to_nat(0u);
v_argStx_370_ = lean_array_get(v___x_362_, v_simpArgs_364_, v_i_349_);
v___x_371_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3);
lean_inc(v_argStx_370_);
v___x_372_ = l_Lean_MessageData_ofSyntax(v_argStx_370_);
v___x_373_ = l_Lean_indentD(v___x_372_);
v_msg_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_374_, 0, v___x_371_);
lean_ctor_set(v_msg_374_, 1, v___x_373_);
v_otherArgs_375_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4));
v___x_376_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v___x_368_, v_i_349_, v_simpArgs_364_, v___x_369_, v_otherArgs_375_);
lean_dec_ref(v_simpArgs_364_);
lean_dec(v_i_349_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
lean_inc(v_stx_348_);
v___x_378_ = l_Lean_Elab_Tactic_setSimpParams(v_stx_348_, v_a_377_);
lean_dec(v_a_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_363_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = lean_box(0);
v___x_381_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
lean_ctor_set(v___x_381_, 2, v___x_380_);
lean_ctor_set(v___x_381_, 3, v___x_380_);
lean_ctor_set(v___x_381_, 4, v___x_380_);
lean_ctor_set(v___x_381_, 5, v___x_380_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v_stx_348_);
v___x_383_ = 4;
v___x_384_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_384_, 0, v___x_381_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___x_380_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*3, v___x_383_);
v___x_385_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_mk_empty_array_with_capacity(v___x_386_);
v___x_388_ = lean_array_push(v___x_387_, v___x_384_);
v___x_389_ = 0;
v___x_390_ = l_Lean_MessageData_hint(v___x_385_, v___x_388_, v___x_380_, v___x_380_, v___x_389_, v___y_366_, v___y_367_);
lean_dec_ref(v___x_388_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
lean_inc(v_argStx_370_);
v___x_392_ = l_Lean_Syntax_getKind(v_argStx_370_);
v___x_393_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11));
v___x_394_ = lean_name_eq(v___x_392_, v___x_393_);
lean_dec(v___x_392_);
if (v___x_394_ == 0)
{
v___y_354_ = v_argStx_370_;
v___y_355_ = v_msg_374_;
v_hint_356_ = v_a_391_;
v___y_357_ = v___y_366_;
v___y_358_ = v___y_367_;
goto v___jp_353_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_Syntax_getArg(v_argStx_370_, v___x_386_);
v___x_396_ = l_Lean_Syntax_isNone(v___x_395_);
lean_dec(v___x_395_);
if (v___x_396_ == 0)
{
if (v___x_394_ == 0)
{
v___y_354_ = v_argStx_370_;
v___y_355_ = v_msg_374_;
v_hint_356_ = v_a_391_;
v___y_357_ = v___y_366_;
v___y_358_ = v___y_367_;
goto v___jp_353_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v_a_391_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___y_354_ = v_argStx_370_;
v___y_355_ = v_msg_374_;
v_hint_356_ = v___x_398_;
v___y_357_ = v___y_366_;
v___y_358_ = v___y_367_;
goto v___jp_353_;
}
}
else
{
v___y_354_ = v_argStx_370_;
v___y_355_ = v_msg_374_;
v_hint_356_ = v_a_391_;
v___y_357_ = v___y_366_;
v___y_358_ = v___y_367_;
goto v___jp_353_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref_known(v_msg_374_, 2);
lean_dec(v_argStx_370_);
v_a_399_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_390_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_390_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref_known(v_msg_374_, 2);
lean_dec(v_argStx_370_);
lean_dec(v_stx_348_);
v_a_407_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_376_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_376_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed(lean_object* v_stx_427_, lean_object* v_i_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(v_stx_427_, v_i_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(lean_object* v_upperBound_433_, lean_object* v_i_434_, lean_object* v_simpArgs_435_, lean_object* v_inst_436_, lean_object* v_R_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_c_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_433_, v_i_434_, v_simpArgs_435_, v_a_438_, v_b_439_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(lean_object* v_upperBound_445_, lean_object* v_i_446_, lean_object* v_simpArgs_447_, lean_object* v_inst_448_, lean_object* v_R_449_, lean_object* v_a_450_, lean_object* v_b_451_, lean_object* v_c_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_445_, v_i_446_, v_simpArgs_447_, v_inst_448_, v_R_449_, v_a_450_, v_b_451_, v_c_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec_ref(v_simpArgs_447_);
lean_dec(v_i_446_);
lean_dec(v_upperBound_445_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(lean_object* v_00_u03b1_457_, lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_458_, v___y_459_, v___y_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(lean_object* v_00_u03b1_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(v_00_u03b1_463_, v_msg_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object* v_upperBound_469_, lean_object* v_snd_470_, lean_object* v_fst_471_, lean_object* v_a_472_, lean_object* v_b_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_a_478_; uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_lt(v_a_472_, v_upperBound_469_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec(v_a_472_);
lean_dec(v_fst_471_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v_b_473_);
return v___x_483_;
}
else
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_484_ = 0;
v___x_485_ = lean_box(0);
v___x_486_ = lean_box(v___x_484_);
v___x_487_ = lean_array_get(v___x_486_, v_snd_470_, v_a_472_);
lean_dec(v___x_486_);
v___x_488_ = lean_unbox(v___x_487_);
lean_dec(v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_inc(v_a_472_);
lean_inc(v_fst_471_);
v___x_489_ = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed), 5, 2);
lean_closure_set(v___x_489_, 0, v_fst_471_);
lean_closure_set(v___x_489_, 1, v_a_472_);
v___x_490_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_489_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_dec_ref_known(v___x_490_, 1);
v_a_478_ = v___x_485_;
goto v___jp_477_;
}
else
{
lean_dec(v_a_472_);
lean_dec(v_fst_471_);
return v___x_490_;
}
}
else
{
v_a_478_ = v___x_485_;
goto v___jp_477_;
}
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_add(v_a_472_, v___x_479_);
lean_dec(v_a_472_);
v_a_472_ = v___x_480_;
v_b_473_ = v_a_478_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object* v_upperBound_491_, lean_object* v_snd_492_, lean_object* v_fst_493_, lean_object* v_a_494_, lean_object* v_b_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_491_, v_snd_492_, v_fst_493_, v_a_494_, v_b_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec_ref(v_snd_492_);
lean_dec(v_upperBound_491_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(lean_object* v_as_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_b_503_);
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v_snd_510_; lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_a_509_ = lean_array_uget_borrowed(v_as_500_, v_i_502_);
v_snd_510_ = lean_ctor_get(v_a_509_, 1);
v_fst_511_ = lean_ctor_get(v_snd_510_, 0);
v_snd_512_ = lean_ctor_get(v_snd_510_, 1);
v___x_513_ = lean_box(0);
v___x_514_ = lean_array_get_size(v_snd_512_);
v___x_515_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_511_);
v___x_516_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_514_, v_snd_512_, v_fst_511_, v___x_515_, v___x_513_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_516_) == 0)
{
size_t v___x_517_; size_t v___x_518_; 
lean_dec_ref_known(v___x_516_, 1);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_502_, v___x_517_);
v_i_502_ = v___x_518_;
v_b_503_ = v___x_513_;
goto _start;
}
else
{
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object* v_as_520_, lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
size_t v_sz_boxed_527_; size_t v_i_boxed_528_; lean_object* v_res_529_; 
v_sz_boxed_527_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_528_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_520_, v_sz_boxed_527_, v_i_boxed_528_, v_b_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v_as_520_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(lean_object* v_hi_530_, lean_object* v_pivot_531_, lean_object* v_as_532_, lean_object* v_i_533_, lean_object* v_k_534_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = lean_nat_dec_lt(v_k_534_, v_hi_530_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_k_534_);
v___x_536_ = lean_array_fswap(v_as_532_, v_i_533_, v_hi_530_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v_i_533_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v_fst_539_; lean_object* v_fst_540_; lean_object* v_start_541_; lean_object* v_start_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_538_ = lean_array_fget_borrowed(v_as_532_, v_k_534_);
v_fst_539_ = lean_ctor_get(v___x_538_, 0);
v_fst_540_ = lean_ctor_get(v_pivot_531_, 0);
v_start_541_ = lean_ctor_get(v_fst_539_, 0);
v_start_542_ = lean_ctor_get(v_fst_540_, 0);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_add(v_start_541_, v___x_543_);
v___x_545_ = lean_nat_dec_le(v___x_544_, v_start_542_);
lean_dec(v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_nat_add(v_k_534_, v___x_543_);
lean_dec(v_k_534_);
v_k_534_ = v___x_546_;
goto _start;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_array_fswap(v_as_532_, v_i_533_, v_k_534_);
v___x_549_ = lean_nat_add(v_i_533_, v___x_543_);
lean_dec(v_i_533_);
v___x_550_ = lean_nat_add(v_k_534_, v___x_543_);
lean_dec(v_k_534_);
v_as_532_ = v___x_548_;
v_i_533_ = v___x_549_;
v_k_534_ = v___x_550_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg___boxed(lean_object* v_hi_552_, lean_object* v_pivot_553_, lean_object* v_as_554_, lean_object* v_i_555_, lean_object* v_k_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_552_, v_pivot_553_, v_as_554_, v_i_555_, v_k_556_);
lean_dec_ref(v_pivot_553_);
lean_dec(v_hi_552_);
return v_res_557_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(lean_object* v_x1_558_, lean_object* v_x2_559_){
_start:
{
lean_object* v_fst_560_; lean_object* v_fst_561_; lean_object* v_start_562_; lean_object* v_start_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_fst_560_ = lean_ctor_get(v_x1_558_, 0);
v_fst_561_ = lean_ctor_get(v_x2_559_, 0);
v_start_562_ = lean_ctor_get(v_fst_560_, 0);
v_start_563_ = lean_ctor_get(v_fst_561_, 0);
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_nat_add(v_start_562_, v___x_564_);
v___x_566_ = lean_nat_dec_le(v___x_565_, v_start_563_);
lean_dec(v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0___boxed(lean_object* v_x1_567_, lean_object* v_x2_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v_x1_567_, v_x2_568_);
lean_dec_ref(v_x2_568_);
lean_dec_ref(v_x1_567_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(lean_object* v_n_571_, lean_object* v_as_572_, lean_object* v_lo_573_, lean_object* v_hi_574_){
_start:
{
lean_object* v___y_576_; uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v_lo_573_, v_hi_574_);
if (v___x_586_ == 0)
{
lean_dec(v_lo_573_);
return v_as_572_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_mid_589_; lean_object* v___y_591_; lean_object* v___y_597_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_587_ = lean_nat_add(v_lo_573_, v_hi_574_);
v___x_588_ = lean_unsigned_to_nat(1u);
v_mid_589_ = lean_nat_shiftr(v___x_587_, v___x_588_);
lean_dec(v___x_587_);
v___x_602_ = lean_array_fget_borrowed(v_as_572_, v_mid_589_);
v___x_603_ = lean_array_fget_borrowed(v_as_572_, v_lo_573_);
v___x_604_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
v___y_597_ = v_as_572_;
goto v___jp_596_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = lean_array_fswap(v_as_572_, v_lo_573_, v_mid_589_);
v___y_597_ = v___x_605_;
goto v___jp_596_;
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = lean_array_fget_borrowed(v___y_591_, v_mid_589_);
v___x_593_ = lean_array_fget_borrowed(v___y_591_, v_hi_574_);
v___x_594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v_mid_589_);
v___y_576_ = v___y_591_;
goto v___jp_575_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = lean_array_fswap(v___y_591_, v_mid_589_, v_hi_574_);
lean_dec(v_mid_589_);
v___y_576_ = v___x_595_;
goto v___jp_575_;
}
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_array_fget_borrowed(v___y_597_, v_hi_574_);
v___x_599_ = lean_array_fget_borrowed(v___y_597_, v_lo_573_);
v___x_600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_598_, v___x_599_);
if (v___x_600_ == 0)
{
v___y_591_ = v___y_597_;
goto v___jp_590_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_array_fswap(v___y_597_, v_lo_573_, v_hi_574_);
v___y_591_ = v___x_601_;
goto v___jp_590_;
}
}
}
v___jp_575_:
{
lean_object* v_pivot_577_; lean_object* v___x_578_; lean_object* v_fst_579_; lean_object* v_snd_580_; uint8_t v___x_581_; 
v_pivot_577_ = lean_array_fget(v___y_576_, v_hi_574_);
lean_inc_n(v_lo_573_, 2);
v___x_578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_574_, v_pivot_577_, v___y_576_, v_lo_573_, v_lo_573_);
lean_dec(v_pivot_577_);
v_fst_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_fst_579_);
v_snd_580_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_snd_580_);
lean_dec_ref(v___x_578_);
v___x_581_ = lean_nat_dec_le(v_hi_574_, v_fst_579_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_571_, v_snd_580_, v_lo_573_, v_fst_579_);
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_fst_579_, v___x_583_);
lean_dec(v_fst_579_);
v_as_572_ = v___x_582_;
v_lo_573_ = v___x_584_;
goto _start;
}
else
{
lean_dec(v_fst_579_);
lean_dec(v_lo_573_);
return v_snd_580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___boxed(lean_object* v_n_606_, lean_object* v_as_607_, lean_object* v_lo_608_, lean_object* v_hi_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_606_, v_as_607_, v_lo_608_, v_hi_609_);
lean_dec(v_hi_609_);
lean_dec(v_n_606_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
return v_x_611_;
}
else
{
lean_object* v_key_613_; lean_object* v_value_614_; lean_object* v_tail_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_key_613_ = lean_ctor_get(v_x_612_, 0);
v_value_614_ = lean_ctor_get(v_x_612_, 1);
v_tail_615_ = lean_ctor_get(v_x_612_, 2);
lean_inc(v_value_614_);
lean_inc(v_key_613_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v_key_613_);
lean_ctor_set(v___x_616_, 1, v_value_614_);
v___x_617_ = lean_array_push(v_x_611_, v___x_616_);
v_x_611_ = v___x_617_;
v_x_612_ = v_tail_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10___boxed(lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_x_619_, v_x_620_);
lean_dec(v_x_620_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(lean_object* v_as_622_, size_t v_i_623_, size_t v_stop_624_, lean_object* v_b_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_eq(v_i_623_, v_stop_624_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; size_t v___x_629_; size_t v___x_630_; 
v___x_627_ = lean_array_uget_borrowed(v_as_622_, v_i_623_);
v___x_628_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_b_625_, v___x_627_);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = lean_usize_add(v_i_623_, v___x_629_);
v_i_623_ = v___x_630_;
v_b_625_ = v___x_628_;
goto _start;
}
else
{
return v_b_625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(lean_object* v_as_632_, lean_object* v_i_633_, lean_object* v_stop_634_, lean_object* v_b_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; lean_object* v_res_638_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_634_);
lean_dec(v_stop_634_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_as_632_, v_i_boxed_636_, v_stop_boxed_637_, v_b_635_);
lean_dec_ref(v_as_632_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(lean_object* v_o_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_env_644_; lean_object* v___x_645_; lean_object* v_toEnvExtension_646_; lean_object* v_asyncMode_647_; lean_object* v___x_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v_merged_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_659_; 
v___x_642_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_643_ = lean_st_ref_get(v___y_640_);
v_env_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc_ref(v_env_644_);
lean_dec(v___x_643_);
v___x_645_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_646_ = lean_ctor_get(v___x_645_, 0);
v_asyncMode_647_ = lean_ctor_get(v_toEnvExtension_646_, 2);
v___x_648_ = lean_box(0);
v___x_649_ = 0;
v___x_650_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_642_, v___x_645_, v_env_644_, v_asyncMode_647_, v___x_648_, v___x_649_);
v_merged_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_650_, 1);
lean_dec(v_unused_660_);
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_merged_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_merged_651_);
lean_ctor_set(v___x_653_, 0, v_o_639_);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_o_639_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_merged_651_);
v___x_656_ = v_reuseFailAlloc_658_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; 
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(lean_object* v_o_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_661_, v___y_662_);
lean_dec(v___y_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_scopes_670_; lean_object* v___x_671_; lean_object* v_opts_672_; lean_object* v___x_673_; 
v___x_668_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_669_ = lean_st_ref_get(v___y_666_);
v_scopes_670_ = lean_ctor_get(v___x_669_, 2);
lean_inc(v_scopes_670_);
lean_dec(v___x_669_);
v___x_671_ = l_List_head_x21___redArg(v___x_668_, v_scopes_670_);
lean_dec(v_scopes_670_);
v_opts_672_ = lean_ctor_get(v___x_671_, 1);
lean_inc_ref(v_opts_672_);
lean_dec(v___x_671_);
v___x_673_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_opts_672_, v___y_666_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
lean_object* v___x_680_; 
v___x_680_ = lean_box(0);
return v___x_680_;
}
else
{
lean_object* v_key_681_; lean_object* v_value_682_; lean_object* v_tail_683_; uint8_t v___x_684_; 
v_key_681_ = lean_ctor_get(v_x_679_, 0);
v_value_682_ = lean_ctor_get(v_x_679_, 1);
v_tail_683_ = lean_ctor_get(v_x_679_, 2);
v___x_684_ = l_Lean_Syntax_instBEqRange_beq(v_key_681_, v_a_678_);
if (v___x_684_ == 0)
{
v_x_679_ = v_tail_683_;
goto _start;
}
else
{
lean_object* v___x_686_; 
lean_inc(v_value_682_);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_value_682_);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(lean_object* v_a_687_, lean_object* v_x_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_687_, v_x_688_);
lean_dec(v_x_688_);
lean_dec_ref(v_a_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object* v_m_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_buckets_692_; lean_object* v___x_693_; uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v___x_696_; uint64_t v_fold_697_; uint64_t v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_buckets_692_ = lean_ctor_get(v_m_690_, 1);
v___x_693_ = lean_array_get_size(v_buckets_692_);
v___x_694_ = l_Lean_Syntax_instHashableRange_hash(v_a_691_);
v___x_695_ = 32ULL;
v___x_696_ = lean_uint64_shift_right(v___x_694_, v___x_695_);
v_fold_697_ = lean_uint64_xor(v___x_694_, v___x_696_);
v___x_698_ = 16ULL;
v___x_699_ = lean_uint64_shift_right(v_fold_697_, v___x_698_);
v___x_700_ = lean_uint64_xor(v_fold_697_, v___x_699_);
v___x_701_ = lean_uint64_to_usize(v___x_700_);
v___x_702_ = lean_usize_of_nat(v___x_693_);
v___x_703_ = ((size_t)1ULL);
v___x_704_ = lean_usize_sub(v___x_702_, v___x_703_);
v___x_705_ = lean_usize_land(v___x_701_, v___x_704_);
v___x_706_ = lean_array_uget_borrowed(v_buckets_692_, v___x_705_);
v___x_707_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_691_, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object* v_m_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_708_, v_a_709_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_m_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(uint8_t v___x_711_, lean_object* v_as_712_, lean_object* v_bs_713_, lean_object* v_i_714_, lean_object* v_cs_715_){
_start:
{
uint8_t v___y_717_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = lean_array_get_size(v_as_712_);
v___x_724_ = lean_nat_dec_lt(v_i_714_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v_i_714_);
return v_cs_715_;
}
else
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = lean_array_get_size(v_bs_713_);
v___x_726_ = lean_nat_dec_lt(v_i_714_, v___x_725_);
if (v___x_726_ == 0)
{
lean_dec(v_i_714_);
return v_cs_715_;
}
else
{
lean_object* v_a_727_; uint8_t v___x_728_; 
v_a_727_ = lean_array_fget_borrowed(v_as_712_, v_i_714_);
v___x_728_ = lean_unbox(v_a_727_);
if (v___x_728_ == 0)
{
lean_object* v_b_729_; uint8_t v___x_730_; 
v_b_729_ = lean_array_fget_borrowed(v_bs_713_, v_i_714_);
v___x_730_ = lean_unbox(v_b_729_);
v___y_717_ = v___x_730_;
goto v___jp_716_;
}
else
{
v___y_717_ = v___x_711_;
goto v___jp_716_;
}
}
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_i_714_, v___x_718_);
lean_dec(v_i_714_);
v___x_720_ = lean_box(v___y_717_);
v___x_721_ = lean_array_push(v_cs_715_, v___x_720_);
v_i_714_ = v___x_719_;
v_cs_715_ = v___x_721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object* v___x_731_, lean_object* v_as_732_, lean_object* v_bs_733_, lean_object* v_i_734_, lean_object* v_cs_735_){
_start:
{
uint8_t v___x_12861__boxed_736_; lean_object* v_res_737_; 
v___x_12861__boxed_736_ = lean_unbox(v___x_731_);
v_res_737_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_12861__boxed_736_, v_as_732_, v_bs_733_, v_i_734_, v_cs_735_);
lean_dec_ref(v_bs_733_);
lean_dec_ref(v_as_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(lean_object* v_msgData_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; lean_object* v_env_742_; uint8_t v___x_743_; lean_object* v_env_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v_scopes_747_; lean_object* v___x_748_; lean_object* v_opts_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_741_ = lean_st_ref_get(v___y_739_);
v_env_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc_ref(v_env_742_);
lean_dec(v___x_741_);
v___x_743_ = 0;
v_env_744_ = l_Lean_Environment_setRecordingDeps(v_env_742_, v___x_743_);
v___x_745_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_746_ = lean_st_ref_get(v___y_739_);
v_scopes_747_ = lean_ctor_get(v___x_746_, 2);
lean_inc(v_scopes_747_);
lean_dec(v___x_746_);
v___x_748_ = l_List_head_x21___redArg(v___x_745_, v_scopes_747_);
lean_dec(v_scopes_747_);
v_opts_749_ = lean_ctor_get(v___x_748_, 1);
lean_inc_ref(v_opts_749_);
lean_dec(v___x_748_);
v___x_750_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_751_ = lean_unsigned_to_nat(32u);
v___x_752_ = lean_mk_empty_array_with_capacity(v___x_751_);
lean_dec_ref(v___x_752_);
v___x_753_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
v___x_754_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_754_, 0, v_env_744_);
lean_ctor_set(v___x_754_, 1, v___x_750_);
lean_ctor_set(v___x_754_, 2, v___x_753_);
lean_ctor_set(v___x_754_, 3, v_opts_749_);
v___x_755_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v_msgData_738_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_757_, v___y_758_);
lean_dec(v___y_758_);
return v_res_760_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_box(1);
v___x_762_ = l_Lean_MessageData_ofFormat(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2));
v___x_767_ = l_Lean_MessageData_ofFormat(v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
if (lean_obj_tag(v_x_769_) == 0)
{
return v_x_768_;
}
else
{
lean_object* v_head_770_; lean_object* v_tail_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_793_; 
v_head_770_ = lean_ctor_get(v_x_769_, 0);
v_tail_771_ = lean_ctor_get(v_x_769_, 1);
v_isSharedCheck_793_ = !lean_is_exclusive(v_x_769_);
if (v_isSharedCheck_793_ == 0)
{
v___x_773_ = v_x_769_;
v_isShared_774_ = v_isSharedCheck_793_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_tail_771_);
lean_inc(v_head_770_);
lean_dec(v_x_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_793_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_before_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_791_; 
v_before_775_ = lean_ctor_get(v_head_770_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_head_770_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_head_770_, 1);
lean_dec(v_unused_792_);
v___x_777_ = v_head_770_;
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_before_775_);
lean_dec(v_head_770_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_791_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_779_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 7);
lean_ctor_set(v___x_777_, 1, v___x_779_);
lean_ctor_set(v___x_777_, 0, v_x_768_);
v___x_781_ = v___x_777_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_x_768_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_790_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3);
if (v_isShared_774_ == 0)
{
lean_ctor_set_tag(v___x_773_, 7);
lean_ctor_set(v___x_773_, 1, v___x_782_);
lean_ctor_set(v___x_773_, 0, v___x_781_);
v___x_784_ = v___x_773_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_782_);
v___x_784_ = v_reuseFailAlloc_789_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = l_Lean_MessageData_ofSyntax(v_before_775_);
v___x_786_ = l_Lean_indentD(v___x_785_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_784_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v_x_768_ = v___x_787_;
v_x_769_ = v_tail_771_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1));
v___x_798_ = l_Lean_MessageData_ofFormat(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(lean_object* v_msgData_799_, lean_object* v_macroStack_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v_scopes_805_; lean_object* v___x_806_; lean_object* v_opts_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_803_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_804_ = lean_st_ref_get(v___y_801_);
v_scopes_805_ = lean_ctor_get(v___x_804_, 2);
lean_inc(v_scopes_805_);
lean_dec(v___x_804_);
v___x_806_ = l_List_head_x21___redArg(v___x_803_, v_scopes_805_);
lean_dec(v_scopes_805_);
v_opts_807_ = lean_ctor_get(v___x_806_, 1);
lean_inc_ref(v_opts_807_);
lean_dec(v___x_806_);
v___x_808_ = l_Lean_Elab_pp_macroStack;
v___x_809_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_807_, v___x_808_);
lean_dec_ref(v_opts_807_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec(v_macroStack_800_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v_msgData_799_);
return v___x_810_;
}
else
{
if (lean_obj_tag(v_macroStack_800_) == 0)
{
lean_object* v___x_811_; 
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_msgData_799_);
return v___x_811_;
}
else
{
lean_object* v_head_812_; lean_object* v_after_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_828_; 
v_head_812_ = lean_ctor_get(v_macroStack_800_, 0);
lean_inc(v_head_812_);
v_after_813_ = lean_ctor_get(v_head_812_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_head_812_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_head_812_, 0);
lean_dec(v_unused_829_);
v___x_815_ = v_head_812_;
v_isShared_816_ = v_isSharedCheck_828_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_after_813_);
lean_dec(v_head_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_828_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 7);
lean_ctor_set(v___x_815_, 1, v___x_817_);
lean_ctor_set(v___x_815_, 0, v_msgData_799_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_msgData_799_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_827_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_msgData_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_820_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = l_Lean_MessageData_ofSyntax(v_after_813_);
v___x_823_ = l_Lean_indentD(v___x_822_);
v_msgData_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_824_, 0, v___x_821_);
lean_ctor_set(v_msgData_824_, 1, v___x_823_);
v___x_825_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(v_msgData_824_, v_macroStack_800_);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v_msgData_830_, lean_object* v_macroStack_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_830_, v_macroStack_831_, v___y_832_);
lean_dec(v___y_832_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Elab_Command_getRef___redArg(v___y_836_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v_macroStack_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v_macroStack_841_ = lean_ctor_get(v___y_836_, 4);
v___x_842_ = l_Lean_Elab_getBetterRef(v_a_840_, v_macroStack_841_);
lean_dec(v_a_840_);
v___x_843_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msg_835_, v___y_837_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_843_);
lean_inc(v_macroStack_841_);
v___x_845_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_a_844_, v_macroStack_841_, v___y_837_);
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_854_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_842_);
lean_ctor_set(v___x_850_, 1, v_a_846_);
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 1);
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_msg_835_);
v_a_855_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_839_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_839_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg___boxed(lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_863_, v___y_864_, v___y_865_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(lean_object* v_ref_868_, lean_object* v_msg_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Elab_Command_getRef___redArg(v___y_870_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v_fileName_875_; lean_object* v_fileMap_876_; lean_object* v_currRecDepth_877_; lean_object* v_cmdPos_878_; lean_object* v_macroStack_879_; lean_object* v_quotContext_x3f_880_; lean_object* v_currMacroScope_881_; lean_object* v_snap_x3f_882_; lean_object* v_cancelTk_x3f_883_; uint8_t v_suppressElabErrors_884_; lean_object* v_ref_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
v_fileName_875_ = lean_ctor_get(v___y_870_, 0);
v_fileMap_876_ = lean_ctor_get(v___y_870_, 1);
v_currRecDepth_877_ = lean_ctor_get(v___y_870_, 2);
v_cmdPos_878_ = lean_ctor_get(v___y_870_, 3);
v_macroStack_879_ = lean_ctor_get(v___y_870_, 4);
v_quotContext_x3f_880_ = lean_ctor_get(v___y_870_, 5);
v_currMacroScope_881_ = lean_ctor_get(v___y_870_, 6);
v_snap_x3f_882_ = lean_ctor_get(v___y_870_, 8);
v_cancelTk_x3f_883_ = lean_ctor_get(v___y_870_, 9);
v_suppressElabErrors_884_ = lean_ctor_get_uint8(v___y_870_, sizeof(void*)*10);
v_ref_885_ = l_Lean_replaceRef(v_ref_868_, v_a_874_);
lean_dec(v_a_874_);
lean_inc(v_cancelTk_x3f_883_);
lean_inc(v_snap_x3f_882_);
lean_inc(v_currMacroScope_881_);
lean_inc(v_quotContext_x3f_880_);
lean_inc(v_macroStack_879_);
lean_inc(v_cmdPos_878_);
lean_inc(v_currRecDepth_877_);
lean_inc_ref(v_fileMap_876_);
lean_inc_ref(v_fileName_875_);
v___x_886_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_886_, 0, v_fileName_875_);
lean_ctor_set(v___x_886_, 1, v_fileMap_876_);
lean_ctor_set(v___x_886_, 2, v_currRecDepth_877_);
lean_ctor_set(v___x_886_, 3, v_cmdPos_878_);
lean_ctor_set(v___x_886_, 4, v_macroStack_879_);
lean_ctor_set(v___x_886_, 5, v_quotContext_x3f_880_);
lean_ctor_set(v___x_886_, 6, v_currMacroScope_881_);
lean_ctor_set(v___x_886_, 7, v_ref_885_);
lean_ctor_set(v___x_886_, 8, v_snap_x3f_882_);
lean_ctor_set(v___x_886_, 9, v_cancelTk_x3f_883_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*10, v_suppressElabErrors_884_);
v___x_887_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_869_, v___x_886_, v___y_871_);
lean_dec_ref_known(v___x_886_, 10);
return v___x_887_;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v_msg_869_);
v_a_888_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_873_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_873_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg___boxed(lean_object* v_ref_896_, lean_object* v_msg_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_896_, v_msg_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v_ref_896_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
return v_x_902_;
}
else
{
lean_object* v_key_904_; lean_object* v_value_905_; lean_object* v_tail_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_929_; 
v_key_904_ = lean_ctor_get(v_x_903_, 0);
v_value_905_ = lean_ctor_get(v_x_903_, 1);
v_tail_906_ = lean_ctor_get(v_x_903_, 2);
v_isSharedCheck_929_ = !lean_is_exclusive(v_x_903_);
if (v_isSharedCheck_929_ == 0)
{
v___x_908_ = v_x_903_;
v_isShared_909_ = v_isSharedCheck_929_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_tail_906_);
lean_inc(v_value_905_);
lean_inc(v_key_904_);
lean_dec(v_x_903_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_929_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; uint64_t v___x_913_; uint64_t v_fold_914_; uint64_t v___x_915_; uint64_t v___x_916_; uint64_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_910_ = lean_array_get_size(v_x_902_);
v___x_911_ = l_Lean_Syntax_instHashableRange_hash(v_key_904_);
v___x_912_ = 32ULL;
v___x_913_ = lean_uint64_shift_right(v___x_911_, v___x_912_);
v_fold_914_ = lean_uint64_xor(v___x_911_, v___x_913_);
v___x_915_ = 16ULL;
v___x_916_ = lean_uint64_shift_right(v_fold_914_, v___x_915_);
v___x_917_ = lean_uint64_xor(v_fold_914_, v___x_916_);
v___x_918_ = lean_uint64_to_usize(v___x_917_);
v___x_919_ = lean_usize_of_nat(v___x_910_);
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_sub(v___x_919_, v___x_920_);
v___x_922_ = lean_usize_land(v___x_918_, v___x_921_);
v___x_923_ = lean_array_uget_borrowed(v_x_902_, v___x_922_);
lean_inc(v___x_923_);
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 2, v___x_923_);
v___x_925_ = v___x_908_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_key_904_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_value_905_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v___x_923_);
v___x_925_ = v_reuseFailAlloc_928_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; 
v___x_926_ = lean_array_uset(v_x_902_, v___x_922_, v___x_925_);
v_x_902_ = v___x_926_;
v_x_903_ = v_tail_906_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(lean_object* v_i_930_, lean_object* v_source_931_, lean_object* v_target_932_){
_start:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_get_size(v_source_931_);
v___x_934_ = lean_nat_dec_lt(v_i_930_, v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v_source_931_);
lean_dec(v_i_930_);
return v_target_932_;
}
else
{
lean_object* v_es_935_; lean_object* v___x_936_; lean_object* v_source_937_; lean_object* v_target_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v_es_935_ = lean_array_fget(v_source_931_, v_i_930_);
v___x_936_ = lean_box(0);
v_source_937_ = lean_array_fset(v_source_931_, v_i_930_, v___x_936_);
v_target_938_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_target_932_, v_es_935_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_add(v_i_930_, v___x_939_);
lean_dec(v_i_930_);
v_i_930_ = v___x_940_;
v_source_931_ = v_source_937_;
v_target_932_ = v_target_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(lean_object* v_data_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_nbuckets_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_943_ = lean_array_get_size(v_data_942_);
v___x_944_ = lean_unsigned_to_nat(2u);
v_nbuckets_945_ = lean_nat_mul(v___x_943_, v___x_944_);
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_box(0);
v___x_948_ = lean_mk_array(v_nbuckets_945_, v___x_947_);
v___x_949_ = lean_array_propagate_mark(v_data_942_, v___x_948_);
v___x_950_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v___x_946_, v_data_942_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object* v_a_951_, lean_object* v_x_952_){
_start:
{
if (lean_obj_tag(v_x_952_) == 0)
{
uint8_t v___x_953_; 
v___x_953_ = 0;
return v___x_953_;
}
else
{
lean_object* v_key_954_; lean_object* v_tail_955_; uint8_t v___x_956_; 
v_key_954_ = lean_ctor_get(v_x_952_, 0);
v_tail_955_ = lean_ctor_get(v_x_952_, 2);
v___x_956_ = l_Lean_Syntax_instBEqRange_beq(v_key_954_, v_a_951_);
if (v___x_956_ == 0)
{
v_x_952_ = v_tail_955_;
goto _start;
}
else
{
return v___x_956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object* v_a_958_, lean_object* v_x_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_958_, v_x_959_);
lean_dec(v_x_959_);
lean_dec_ref(v_a_958_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(lean_object* v_a_962_, lean_object* v_b_963_, lean_object* v_x_964_){
_start:
{
if (lean_obj_tag(v_x_964_) == 0)
{
lean_dec(v_b_963_);
lean_dec_ref(v_a_962_);
return v_x_964_;
}
else
{
lean_object* v_key_965_; lean_object* v_value_966_; lean_object* v_tail_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_979_; 
v_key_965_ = lean_ctor_get(v_x_964_, 0);
v_value_966_ = lean_ctor_get(v_x_964_, 1);
v_tail_967_ = lean_ctor_get(v_x_964_, 2);
v_isSharedCheck_979_ = !lean_is_exclusive(v_x_964_);
if (v_isSharedCheck_979_ == 0)
{
v___x_969_ = v_x_964_;
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_tail_967_);
lean_inc(v_value_966_);
lean_inc(v_key_965_);
lean_dec(v_x_964_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
uint8_t v___x_971_; 
v___x_971_ = l_Lean_Syntax_instBEqRange_beq(v_key_965_, v_a_962_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_962_, v_b_963_, v_tail_967_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 2, v___x_972_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_key_965_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_value_966_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
else
{
lean_object* v___x_977_; 
lean_dec(v_value_966_);
lean_dec(v_key_965_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_b_963_);
lean_ctor_set(v___x_969_, 0, v_a_962_);
v___x_977_ = v___x_969_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_962_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_b_963_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_tail_967_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object* v_m_980_, lean_object* v_a_981_, lean_object* v_b_982_){
_start:
{
lean_object* v_size_983_; lean_object* v_buckets_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1027_; 
v_size_983_ = lean_ctor_get(v_m_980_, 0);
v_buckets_984_ = lean_ctor_get(v_m_980_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_m_980_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_986_ = v_m_980_;
v_isShared_987_ = v_isSharedCheck_1027_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_buckets_984_);
lean_inc(v_size_983_);
lean_dec(v_m_980_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1027_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; uint64_t v___x_989_; uint64_t v___x_990_; uint64_t v___x_991_; uint64_t v_fold_992_; uint64_t v___x_993_; uint64_t v___x_994_; uint64_t v___x_995_; size_t v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v_bkt_1001_; uint8_t v___x_1002_; 
v___x_988_ = lean_array_get_size(v_buckets_984_);
v___x_989_ = l_Lean_Syntax_instHashableRange_hash(v_a_981_);
v___x_990_ = 32ULL;
v___x_991_ = lean_uint64_shift_right(v___x_989_, v___x_990_);
v_fold_992_ = lean_uint64_xor(v___x_989_, v___x_991_);
v___x_993_ = 16ULL;
v___x_994_ = lean_uint64_shift_right(v_fold_992_, v___x_993_);
v___x_995_ = lean_uint64_xor(v_fold_992_, v___x_994_);
v___x_996_ = lean_uint64_to_usize(v___x_995_);
v___x_997_ = lean_usize_of_nat(v___x_988_);
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_sub(v___x_997_, v___x_998_);
v___x_1000_ = lean_usize_land(v___x_996_, v___x_999_);
v_bkt_1001_ = lean_array_uget_borrowed(v_buckets_984_, v___x_1000_);
v___x_1002_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_981_, v_bkt_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v_size_x27_1004_; lean_object* v___x_1005_; lean_object* v_buckets_x27_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v_size_x27_1004_ = lean_nat_add(v_size_983_, v___x_1003_);
lean_dec(v_size_983_);
lean_inc(v_bkt_1001_);
v___x_1005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1005_, 0, v_a_981_);
lean_ctor_set(v___x_1005_, 1, v_b_982_);
lean_ctor_set(v___x_1005_, 2, v_bkt_1001_);
v_buckets_x27_1006_ = lean_array_uset(v_buckets_984_, v___x_1000_, v___x_1005_);
v___x_1007_ = lean_unsigned_to_nat(4u);
v___x_1008_ = lean_nat_mul(v_size_x27_1004_, v___x_1007_);
v___x_1009_ = lean_unsigned_to_nat(3u);
v___x_1010_ = lean_nat_div(v___x_1008_, v___x_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_array_get_size(v_buckets_x27_1006_);
v___x_1012_ = lean_nat_dec_le(v___x_1010_, v___x_1011_);
lean_dec(v___x_1010_);
if (v___x_1012_ == 0)
{
lean_object* v_val_1013_; lean_object* v___x_1015_; 
v_val_1013_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_buckets_x27_1006_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_val_1013_);
lean_ctor_set(v___x_986_, 0, v_size_x27_1004_);
v___x_1015_ = v___x_986_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_size_x27_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_val_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v___x_1018_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v_buckets_x27_1006_);
lean_ctor_set(v___x_986_, 0, v_size_x27_1004_);
v___x_1018_ = v___x_986_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_size_x27_1004_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_buckets_x27_1006_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v___x_1020_; lean_object* v_buckets_x27_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_inc(v_bkt_1001_);
v___x_1020_ = lean_box(0);
v_buckets_x27_1021_ = lean_array_uset(v_buckets_984_, v___x_1000_, v___x_1020_);
v___x_1022_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_981_, v_b_982_, v_bkt_1001_);
v___x_1023_ = lean_array_uset(v_buckets_x27_1021_, v___x_1000_, v___x_1022_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 1, v___x_1023_);
v___x_1025_ = v___x_986_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_size_983_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(lean_object* v___x_1048_, lean_object* v_val_1049_, uint8_t v___x_1050_, lean_object* v_ci_1051_, lean_object* v_info_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
if (lean_obj_tag(v_info_1052_) == 10)
{
lean_object* v_i_1057_; lean_object* v_stx_1058_; lean_object* v_value_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1153_; 
v_i_1057_ = lean_ctor_get(v_info_1052_, 0);
lean_inc_ref(v_i_1057_);
v_stx_1058_ = lean_ctor_get(v_i_1057_, 0);
v_value_1059_ = lean_ctor_get(v_i_1057_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_i_1057_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1061_ = v_i_1057_;
v_isShared_1062_ = v_isSharedCheck_1153_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_value_1059_);
lean_inc(v_stx_1058_);
lean_dec(v_i_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1153_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; 
v___x_1063_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_1059_, v___x_1048_);
lean_dec(v_value_1059_);
if (lean_obj_tag(v___x_1063_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1143_; 
v_val_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1143_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1143_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Elab_Info_range_x3f(v_info_1052_);
if (lean_obj_tag(v___x_1068_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1138_; 
v_val_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1138_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_val_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1138_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_maskAcc_1074_; lean_object* v___y_1085_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6));
lean_inc(v_stx_1058_);
v___x_1126_ = l_Lean_Syntax_isOfKind(v_stx_1058_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8));
lean_inc(v_stx_1058_);
v___x_1128_ = l_Lean_Syntax_isOfKind(v_stx_1058_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
lean_del_object(v___x_1071_);
lean_dec(v_val_1069_);
lean_del_object(v___x_1066_);
lean_dec(v_val_1064_);
lean_del_object(v___x_1061_);
lean_dec(v_stx_1058_);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_info_1052_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_info_1052_, 0);
lean_dec(v_unused_1137_);
v___x_1130_ = v_info_1052_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_dec(v_info_1052_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_box(0);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
else
{
goto v___jp_1089_;
}
}
else
{
goto v___jp_1089_;
}
v___jp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_st_ref_take(v_val_1049_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v_maskAcc_1074_);
v___x_1077_ = v___x_1061_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_stx_1058_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_maskAcc_1074_);
v___x_1077_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1078_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_1075_, v_val_1069_, v___x_1077_);
v___x_1079_ = lean_st_ref_put(v_val_1049_, v___x_1078_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1079_);
v___x_1081_ = v___x_1071_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
v___jp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_unsigned_to_nat(0u);
v___x_1087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0));
v___x_1088_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_1050_, v_val_1064_, v___y_1085_, v___x_1086_, v___x_1087_);
lean_dec_ref(v___y_1085_);
lean_dec(v_val_1064_);
v_maskAcc_1074_ = v___x_1088_;
goto v___jp_1073_;
}
v___jp_1089_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_st_ref_get(v_val_1049_);
v___x_1091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_1090_, v_val_1069_);
lean_dec(v___x_1090_);
if (lean_obj_tag(v___x_1091_) == 1)
{
lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1124_; 
v_val_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1124_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1124_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_snd_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1122_; 
v_snd_1096_ = lean_ctor_get(v_val_1092_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_val_1092_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_val_1092_, 0);
lean_dec(v_unused_1123_);
v___x_1098_ = v_val_1092_;
v_isShared_1099_ = v_isSharedCheck_1122_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_snd_1096_);
lean_dec(v_val_1092_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1122_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1100_ = lean_array_get_size(v_val_1064_);
v___x_1101_ = lean_array_get_size(v_snd_1096_);
v___x_1102_ = lean_nat_dec_eq(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1103_ = l_Lean_Elab_Info_stx(v_info_1052_);
lean_dec_ref_known(v_info_1052_, 1);
v___x_1104_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2);
v___x_1105_ = l_Nat_reprFast(v___x_1101_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 3);
lean_ctor_set(v___x_1094_, 0, v___x_1105_);
v___x_1107_ = v___x_1094_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = l_Lean_MessageData_ofFormat(v___x_1107_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 7);
lean_ctor_set(v___x_1098_, 1, v___x_1108_);
lean_ctor_set(v___x_1098_, 0, v___x_1104_);
v___x_1110_ = v___x_1098_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1111_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Nat_reprFast(v___x_1100_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 3);
lean_ctor_set(v___x_1066_, 0, v___x_1113_);
v___x_1115_ = v___x_1066_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = l_Lean_MessageData_ofFormat(v___x_1115_);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1112_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v___x_1103_, v___x_1117_, v___y_1054_, v___y_1055_);
lean_dec(v___x_1103_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_dec_ref_known(v___x_1118_, 1);
v___y_1085_ = v_snd_1096_;
goto v___jp_1084_;
}
else
{
lean_dec(v_snd_1096_);
lean_del_object(v___x_1071_);
lean_dec(v_val_1069_);
lean_dec(v_val_1064_);
lean_del_object(v___x_1061_);
lean_dec(v_stx_1058_);
return v___x_1118_;
}
}
}
}
}
else
{
lean_del_object(v___x_1098_);
lean_del_object(v___x_1094_);
lean_del_object(v___x_1066_);
lean_dec_ref_known(v_info_1052_, 1);
v___y_1085_ = v_snd_1096_;
goto v___jp_1084_;
}
}
}
}
else
{
lean_dec(v___x_1091_);
lean_del_object(v___x_1066_);
lean_dec_ref_known(v_info_1052_, 1);
v_maskAcc_1074_ = v_val_1064_;
goto v___jp_1073_;
}
}
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_dec(v___x_1068_);
lean_dec(v_val_1064_);
lean_del_object(v___x_1061_);
lean_dec(v_stx_1058_);
lean_dec_ref_known(v_info_1052_, 1);
v___x_1139_ = lean_box(0);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1139_);
v___x_1141_ = v___x_1066_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v___x_1063_);
lean_del_object(v___x_1061_);
lean_dec(v_stx_1058_);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_info_1052_);
if (v_isSharedCheck_1151_ == 0)
{
lean_object* v_unused_1152_; 
v_unused_1152_ = lean_ctor_get(v_info_1052_, 0);
lean_dec(v_unused_1152_);
v___x_1145_ = v_info_1052_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_dec(v_info_1052_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_box(0);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v_info_1052_);
v___x_1154_ = lean_box(0);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(lean_object* v___x_1156_, lean_object* v_val_1157_, lean_object* v___x_1158_, lean_object* v_ci_1159_, lean_object* v_info_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v___x_13439__boxed_1165_; lean_object* v_res_1166_; 
v___x_13439__boxed_1165_ = lean_unbox(v___x_1158_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v___x_1156_, v_val_1157_, v___x_13439__boxed_1165_, v_ci_1159_, v_info_1160_, v_x_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec_ref(v_x_1161_);
lean_dec_ref(v_ci_1159_);
lean_dec(v_val_1157_);
lean_dec(v___x_1156_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(lean_object* v_postNode_1167_, lean_object* v_ci_1168_, lean_object* v_i_1169_, lean_object* v_cs_1170_, lean_object* v_x_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
v___x_1175_ = lean_apply_6(v_postNode_1167_, v_ci_1168_, v_i_1169_, v_cs_1170_, v___y_1172_, v___y_1173_, lean_box(0));
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(lean_object* v_postNode_1176_, lean_object* v_ci_1177_, lean_object* v_i_1178_, lean_object* v_cs_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(v_postNode_1176_, v_ci_1177_, v_i_1178_, v_cs_1179_, v_x_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v_x_1180_);
return v_res_1184_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_instMonadEIO___redArg();
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(lean_object* v_msg_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_toApplicative_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1225_; 
v___x_1192_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0);
v___x_1193_ = l_StateRefT_x27_instMonad___redArg(v___x_1192_);
v_toApplicative_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1193_, 1);
lean_dec(v_unused_1226_);
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1225_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_toApplicative_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1225_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_toFunctor_1198_; lean_object* v_toSeq_1199_; lean_object* v_toSeqLeft_1200_; lean_object* v_toSeqRight_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1223_; 
v_toFunctor_1198_ = lean_ctor_get(v_toApplicative_1194_, 0);
v_toSeq_1199_ = lean_ctor_get(v_toApplicative_1194_, 2);
v_toSeqLeft_1200_ = lean_ctor_get(v_toApplicative_1194_, 3);
v_toSeqRight_1201_ = lean_ctor_get(v_toApplicative_1194_, 4);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_toApplicative_1194_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_toApplicative_1194_, 1);
lean_dec(v_unused_1224_);
v___x_1203_ = v_toApplicative_1194_;
v_isShared_1204_ = v_isSharedCheck_1223_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_toSeqRight_1201_);
lean_inc(v_toSeqLeft_1200_);
lean_inc(v_toSeq_1199_);
lean_inc(v_toFunctor_1198_);
lean_dec(v_toApplicative_1194_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1223_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___f_1212_; lean_object* v___x_1214_; 
v___f_1205_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1));
v___f_1206_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2));
lean_inc_ref(v_toFunctor_1198_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toFunctor_1198_);
v___f_1208_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1208_, 0, v_toFunctor_1198_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___f_1207_);
lean_ctor_set(v___x_1209_, 1, v___f_1208_);
v___f_1210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1210_, 0, v_toSeqRight_1201_);
v___f_1211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1211_, 0, v_toSeqLeft_1200_);
v___f_1212_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1212_, 0, v_toSeq_1199_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 4, v___f_1210_);
lean_ctor_set(v___x_1203_, 3, v___f_1211_);
lean_ctor_set(v___x_1203_, 2, v___f_1212_);
lean_ctor_set(v___x_1203_, 1, v___f_1205_);
lean_ctor_set(v___x_1203_, 0, v___x_1209_);
v___x_1214_ = v___x_1203_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___f_1205_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v___f_1212_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v___f_1211_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v___f_1210_);
v___x_1214_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1216_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___f_1206_);
lean_ctor_set(v___x_1196_, 0, v___x_1214_);
v___x_1216_ = v___x_1196_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___f_1206_);
v___x_1216_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_11903__overap_1219_; lean_object* v___x_1220_; 
v___x_1217_ = lean_box(0);
v___x_1218_ = l_instInhabitedOfMonad___redArg(v___x_1216_, v___x_1217_);
v___x_11903__overap_1219_ = lean_panic_fn_borrowed(v___x_1218_, v_msg_1188_);
lean_dec(v___x_1218_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
v___x_1220_ = lean_apply_3(v___x_11903__overap_1219_, v___y_1189_, v___y_1190_, lean_box(0));
return v___x_1220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(lean_object* v_msg_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1231_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1235_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2));
v___x_1236_ = lean_unsigned_to_nat(21u);
v___x_1237_ = lean_unsigned_to_nat(65u);
v___x_1238_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1));
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0));
v___x_1240_ = l_mkPanicMessageWithDecl(v___x_1239_, v___x_1238_, v___x_1237_, v___x_1236_, v___x_1235_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(lean_object* v_preNode_1241_, lean_object* v_postNode_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
switch(lean_obj_tag(v_x_1244_))
{
case 0:
{
lean_object* v_i_1248_; lean_object* v_t_1249_; lean_object* v___x_1250_; 
v_i_1248_ = lean_ctor_get(v_x_1244_, 0);
lean_inc_ref(v_i_1248_);
v_t_1249_ = lean_ctor_get(v_x_1244_, 1);
lean_inc_ref(v_t_1249_);
lean_dec_ref_known(v_x_1244_, 2);
v___x_1250_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1248_, v_x_1243_);
v_x_1243_ = v___x_1250_;
v_x_1244_ = v_t_1249_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1243_) == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec_ref_known(v_x_1244_, 2);
lean_dec_ref(v_postNode_1242_);
lean_dec_ref(v_preNode_1241_);
v___x_1252_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3);
v___x_1253_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v___x_1252_, v___y_1245_, v___y_1246_);
return v___x_1253_;
}
else
{
lean_object* v_i_1254_; lean_object* v_children_1255_; lean_object* v_val_1256_; lean_object* v___x_1257_; 
v_i_1254_ = lean_ctor_get(v_x_1244_, 0);
lean_inc_ref_n(v_i_1254_, 2);
v_children_1255_ = lean_ctor_get(v_x_1244_, 1);
lean_inc_ref_n(v_children_1255_, 2);
lean_dec_ref_known(v_x_1244_, 2);
v_val_1256_ = lean_ctor_get(v_x_1243_, 0);
lean_inc_n(v_val_1256_, 2);
lean_inc_ref(v_preNode_1241_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
v___x_1257_ = lean_apply_6(v_preNode_1241_, v_val_1256_, v_i_1254_, v_children_1255_, v___y_1245_, v___y_1246_, lean_box(0));
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; uint8_t v___x_1259_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1257_, 1);
v___x_1259_ = lean_unbox(v_a_1258_);
lean_dec(v_a_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_preNode_1241_);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_x_1243_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v_x_1243_, 0);
lean_dec(v_unused_1285_);
v___x_1261_ = v_x_1243_;
v_isShared_1262_ = v_isSharedCheck_1284_;
goto v_resetjp_1260_;
}
else
{
lean_dec(v_x_1243_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1284_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_box(0);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
v___x_1264_ = lean_apply_7(v_postNode_1242_, v_val_1256_, v_i_1254_, v_children_1255_, v___x_1263_, v___y_1245_, v___y_1246_, lean_box(0));
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1275_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1275_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_a_1265_);
v___x_1270_ = v___x_1261_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1270_);
v___x_1272_ = v___x_1267_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_del_object(v___x_1261_);
v_a_1276_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1264_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1264_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1243_, v_i_1254_);
v___x_1287_ = l_Lean_PersistentArray_toList___redArg(v_children_1255_);
v___x_1288_ = lean_box(0);
lean_inc_ref(v_postNode_1242_);
v___x_1289_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1241_, v_postNode_1242_, v___x_1286_, v___x_1287_, v___x_1288_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
v___x_1291_ = lean_apply_7(v_postNode_1242_, v_val_1256_, v_i_1254_, v_children_1255_, v_a_1290_, v___y_1245_, v___y_1246_, lean_box(0));
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1300_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_a_1292_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1296_);
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
v_a_1301_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1291_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1291_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_val_1256_);
lean_dec_ref(v_children_1255_);
lean_dec_ref(v_i_1254_);
lean_dec_ref(v_postNode_1242_);
v_a_1309_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1289_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1289_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_val_1256_);
lean_dec_ref(v_children_1255_);
lean_dec_ref(v_i_1254_);
lean_dec_ref_known(v_x_1243_, 1);
lean_dec_ref(v_postNode_1242_);
lean_dec_ref(v_preNode_1241_);
v_a_1317_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1257_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1257_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
default: 
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_x_1243_);
lean_dec_ref(v_postNode_1242_);
lean_dec_ref(v_preNode_1241_);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_x_1244_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v_x_1244_, 0);
lean_dec(v_unused_1333_);
v___x_1326_ = v_x_1244_;
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v_x_1244_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1332_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = lean_box(0);
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1328_);
v___x_1330_ = v___x_1326_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(lean_object* v_preNode_1334_, lean_object* v_postNode_1335_, lean_object* v___x_1336_, lean_object* v_x_1337_, lean_object* v_x_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
if (lean_obj_tag(v_x_1337_) == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v___x_1336_);
lean_dec_ref(v_postNode_1335_);
lean_dec_ref(v_preNode_1334_);
v___x_1342_ = l_List_reverse___redArg(v_x_1338_);
v___x_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
else
{
lean_object* v_head_1344_; lean_object* v_tail_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1363_; 
v_head_1344_ = lean_ctor_get(v_x_1337_, 0);
v_tail_1345_ = lean_ctor_get(v_x_1337_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_x_1337_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1347_ = v_x_1337_;
v_isShared_1348_ = v_isSharedCheck_1363_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_tail_1345_);
lean_inc(v_head_1344_);
lean_dec(v_x_1337_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1363_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; 
lean_inc(v___x_1336_);
lean_inc_ref(v_postNode_1335_);
lean_inc_ref(v_preNode_1334_);
v___x_1349_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1334_, v_postNode_1335_, v___x_1336_, v_head_1344_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1352_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v_x_1338_);
lean_ctor_set(v___x_1347_, 0, v_a_1350_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1350_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_x_1338_);
v___x_1352_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
v_x_1337_ = v_tail_1345_;
v_x_1338_ = v___x_1352_;
goto _start;
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_del_object(v___x_1347_);
lean_dec(v_tail_1345_);
lean_dec(v_x_1338_);
lean_dec(v___x_1336_);
lean_dec_ref(v_postNode_1335_);
lean_dec_ref(v_preNode_1334_);
v_a_1355_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1349_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1349_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(lean_object* v_preNode_1364_, lean_object* v_postNode_1365_, lean_object* v___x_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1364_, v_postNode_1365_, v___x_1366_, v_x_1367_, v_x_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(lean_object* v_preNode_1373_, lean_object* v_postNode_1374_, lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1373_, v_postNode_1374_, v_x_1375_, v_x_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object* v_preNode_1381_, lean_object* v_postNode_1382_, lean_object* v_ctx_x3f_1383_, lean_object* v_t_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___f_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___f_1388_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1388_, 0, v_postNode_1382_);
v___x_1389_ = lean_box(0);
v___x_1390_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1381_, v___f_1388_, v_ctx_x3f_1383_, v_t_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1390_, 0);
lean_dec(v_unused_1398_);
v___x_1392_ = v___x_1390_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v___x_1390_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1389_);
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1389_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1390_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object* v_preNode_1407_, lean_object* v_postNode_1408_, lean_object* v_ctx_x3f_1409_, lean_object* v_t_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v_preNode_1407_, v_postNode_1408_, v_ctx_x3f_1409_, v_t_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(uint8_t v___x_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_box(v___x_1415_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object* v___x_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
uint8_t v___x_14088__boxed_1431_; lean_object* v_res_1432_; 
v___x_14088__boxed_1431_ = lean_unbox(v___x_1424_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v___x_14088__boxed_1431_, v_x_1425_, v_x_1426_, v_x_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec_ref(v_x_1427_);
lean_dec_ref(v_x_1426_);
lean_dec_ref(v_x_1425_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(uint8_t v___x_1433_, lean_object* v_val_1434_, lean_object* v_as_1435_, size_t v_sz_1436_, size_t v_i_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v___x_1442_; 
v___x_1442_ = lean_usize_dec_lt(v_i_1437_, v_sz_1436_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_val_1434_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_b_1438_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; lean_object* v_a_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1444_ = lean_box(v___x_1433_);
v___f_1445_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1445_, 0, v___x_1444_);
v___x_1446_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
v___x_1447_ = lean_box(v___x_1433_);
lean_inc(v_val_1434_);
v___f_1448_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1448_, 0, v___x_1446_);
lean_closure_set(v___f_1448_, 1, v_val_1434_);
lean_closure_set(v___f_1448_, 2, v___x_1447_);
v___x_1449_ = lean_box(0);
v_a_1450_ = lean_array_uget_borrowed(v_as_1435_, v_i_1437_);
v___x_1451_ = lean_box(0);
lean_inc(v_a_1450_);
v___x_1452_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v___f_1445_, v___f_1448_, v___x_1451_, v_a_1450_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1452_) == 0)
{
size_t v___x_1453_; size_t v___x_1454_; 
lean_dec_ref_known(v___x_1452_, 1);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1437_, v___x_1453_);
v_i_1437_ = v___x_1454_;
v_b_1438_ = v___x_1449_;
goto _start;
}
else
{
lean_dec(v_val_1434_);
return v___x_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object* v___x_1456_, lean_object* v_val_1457_, lean_object* v_as_1458_, lean_object* v_sz_1459_, lean_object* v_i_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v___x_14113__boxed_1465_; size_t v_sz_boxed_1466_; size_t v_i_boxed_1467_; lean_object* v_res_1468_; 
v___x_14113__boxed_1465_ = lean_unbox(v___x_1456_);
v_sz_boxed_1466_ = lean_unbox_usize(v_sz_1459_);
lean_dec(v_sz_1459_);
v_i_boxed_1467_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_res_1468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_14113__boxed_1465_, v_val_1457_, v_as_1458_, v_sz_boxed_1466_, v_i_boxed_1467_, v_b_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec_ref(v_as_1458_);
return v_res_1468_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = lean_box(0);
v___x_1470_ = lean_unsigned_to_nat(16u);
v___x_1471_ = lean_mk_array(v___x_1470_, v___x_1469_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__0, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0);
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v___x_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0(lean_object* v_cmdStx_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1546_; 
v___x_1479_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_1476_, v___y_1477_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1546_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1546_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1484_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_1485_ = l_Lean_Linter_getLinterValue(v___x_1484_, v_a_1480_);
lean_dec(v_a_1480_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = lean_box(0);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1486_);
v___x_1488_ = v___x_1482_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
else
{
uint8_t v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = 0;
v___x_1491_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1475_, v___x_1490_);
if (lean_obj_tag(v___x_1491_) == 1)
{
lean_object* v___x_1492_; lean_object* v_infoState_1493_; lean_object* v_trees_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; size_t v_sz_1500_; size_t v___x_1501_; lean_object* v___x_1502_; 
lean_dec_ref_known(v___x_1491_, 1);
lean_del_object(v___x_1482_);
v___x_1492_ = lean_st_ref_get(v___y_1477_);
v_infoState_1493_ = lean_ctor_get(v___x_1492_, 8);
lean_inc_ref(v_infoState_1493_);
lean_dec(v___x_1492_);
v_trees_1494_ = lean_ctor_get(v_infoState_1493_, 2);
lean_inc_ref(v_trees_1494_);
lean_dec_ref(v_infoState_1493_);
v___x_1495_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1494_);
lean_dec_ref(v_trees_1494_);
v___x_1496_ = lean_unsigned_to_nat(0u);
v___x_1497_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__1, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1);
v___x_1498_ = lean_st_mk_ref(v___x_1497_);
v___x_1499_ = lean_box(0);
v_sz_1500_ = lean_array_size(v___x_1495_);
v___x_1501_ = ((size_t)0ULL);
lean_inc(v___x_1498_);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_1485_, v___x_1498_, v___x_1495_, v_sz_1500_, v___x_1501_, v___x_1499_, v___y_1476_, v___y_1477_);
lean_dec_ref(v___x_1495_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1503_; lean_object* v___y_1505_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1529_; lean_object* v_size_1535_; lean_object* v_buckets_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
lean_dec_ref_known(v___x_1502_, 1);
v___x_1503_ = lean_st_ref_get(v___x_1498_);
lean_dec(v___x_1498_);
v_size_1535_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_size_1535_);
v_buckets_1536_ = lean_ctor_get(v___x_1503_, 1);
lean_inc_ref(v_buckets_1536_);
lean_dec(v___x_1503_);
v___x_1537_ = lean_mk_empty_array_with_capacity(v_size_1535_);
lean_dec(v_size_1535_);
v___x_1538_ = lean_array_get_size(v_buckets_1536_);
v___x_1539_ = lean_nat_dec_lt(v___x_1496_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_dec_ref(v_buckets_1536_);
v___y_1529_ = v___x_1537_;
goto v___jp_1528_;
}
else
{
size_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_usize_of_nat(v___x_1538_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_1536_, v___x_1501_, v___x_1540_, v___x_1537_);
lean_dec_ref(v_buckets_1536_);
v___y_1529_ = v___x_1541_;
goto v___jp_1528_;
}
v___jp_1504_:
{
size_t v_sz_1506_; lean_object* v___x_1507_; 
v_sz_1506_ = lean_array_size(v___y_1505_);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___y_1505_, v_sz_1506_, v___x_1501_, v___x_1499_, v___y_1476_, v___y_1477_);
lean_dec_ref(v___y_1505_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v___x_1507_, 0);
lean_dec(v_unused_1515_);
v___x_1509_ = v___x_1507_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v___x_1507_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1499_);
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1499_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
return v___x_1507_;
}
}
v___jp_1516_:
{
lean_object* v___x_1521_; 
v___x_1521_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v___y_1518_, v___y_1517_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec(v___y_1518_);
v___y_1505_ = v___x_1521_;
goto v___jp_1504_;
}
v___jp_1522_:
{
uint8_t v___x_1527_; 
v___x_1527_ = lean_nat_dec_le(v___y_1526_, v___y_1523_);
if (v___x_1527_ == 0)
{
lean_dec(v___y_1523_);
lean_inc(v___y_1526_);
v___y_1517_ = v___y_1524_;
v___y_1518_ = v___y_1525_;
v___y_1519_ = v___y_1526_;
v___y_1520_ = v___y_1526_;
goto v___jp_1516_;
}
else
{
v___y_1517_ = v___y_1524_;
v___y_1518_ = v___y_1525_;
v___y_1519_ = v___y_1526_;
v___y_1520_ = v___y_1523_;
goto v___jp_1516_;
}
}
v___jp_1528_:
{
lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1530_ = lean_array_get_size(v___y_1529_);
v___x_1531_ = lean_nat_dec_eq(v___x_1530_, v___x_1496_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1532_ = lean_unsigned_to_nat(1u);
v___x_1533_ = lean_nat_sub(v___x_1530_, v___x_1532_);
v___x_1534_ = lean_nat_dec_le(v___x_1496_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_inc(v___x_1533_);
v___y_1523_ = v___x_1533_;
v___y_1524_ = v___y_1529_;
v___y_1525_ = v___x_1530_;
v___y_1526_ = v___x_1533_;
goto v___jp_1522_;
}
else
{
v___y_1523_ = v___x_1533_;
v___y_1524_ = v___y_1529_;
v___y_1525_ = v___x_1530_;
v___y_1526_ = v___x_1496_;
goto v___jp_1522_;
}
}
else
{
v___y_1505_ = v___y_1529_;
goto v___jp_1504_;
}
}
}
else
{
lean_dec(v___x_1498_);
return v___x_1502_;
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec(v___x_1491_);
v___x_1542_ = lean_box(0);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1542_);
v___x_1544_ = v___x_1482_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
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
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___boxed(lean_object* v_cmdStx_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v_cmdStx_1547_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(lean_object* v_o_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_1563_, v___y_1565_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(lean_object* v_o_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object* v_00_u03b2_1573_, lean_object* v_m_1574_, lean_object* v_a_1575_, lean_object* v_b_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_1574_, v_a_1575_, v_b_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object* v_00_u03b2_1578_, lean_object* v_m_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_1579_, v_a_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object* v_00_u03b2_1582_, lean_object* v_m_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(v_00_u03b2_1582_, v_m_1583_, v_a_1584_);
lean_dec_ref(v_a_1584_);
lean_dec_ref(v_m_1583_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(lean_object* v_00_u03b1_1586_, lean_object* v_ref_1587_, lean_object* v_msg_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_1587_, v_msg_1588_, v___y_1589_, v___y_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_ref_1594_, lean_object* v_msg_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(v_00_u03b1_1593_, v_ref_1594_, v_msg_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v_ref_1594_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object* v_upperBound_1600_, lean_object* v_snd_1601_, lean_object* v_fst_1602_, lean_object* v_inst_1603_, lean_object* v_R_1604_, lean_object* v_a_1605_, lean_object* v_b_1606_, lean_object* v_c_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_1600_, v_snd_1601_, v_fst_1602_, v_a_1605_, v_b_1606_, v___y_1608_, v___y_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object* v_upperBound_1612_, lean_object* v_snd_1613_, lean_object* v_fst_1614_, lean_object* v_inst_1615_, lean_object* v_R_1616_, lean_object* v_a_1617_, lean_object* v_b_1618_, lean_object* v_c_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(v_upperBound_1612_, v_snd_1613_, v_fst_1614_, v_inst_1615_, v_R_1616_, v_a_1617_, v_b_1618_, v_c_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_snd_1613_);
lean_dec(v_upperBound_1612_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object* v_n_1624_, lean_object* v_as_1625_, lean_object* v_lo_1626_, lean_object* v_hi_1627_, lean_object* v_w_1628_, lean_object* v_hlo_1629_, lean_object* v_hhi_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_1624_, v_as_1625_, v_lo_1626_, v_hi_1627_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object* v_n_1632_, lean_object* v_as_1633_, lean_object* v_lo_1634_, lean_object* v_hi_1635_, lean_object* v_w_1636_, lean_object* v_hlo_1637_, lean_object* v_hhi_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(v_n_1632_, v_as_1633_, v_lo_1634_, v_hi_1635_, v_w_1636_, v_hlo_1637_, v_hhi_1638_);
lean_dec(v_hi_1635_);
lean_dec(v_n_1632_);
return v_res_1639_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object* v_00_u03b2_1640_, lean_object* v_a_1641_, lean_object* v_x_1642_){
_start:
{
uint8_t v___x_1643_; 
v___x_1643_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1641_, v_x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1644_, lean_object* v_a_1645_, lean_object* v_x_1646_){
_start:
{
uint8_t v_res_1647_; lean_object* v_r_1648_; 
v_res_1647_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_1644_, v_a_1645_, v_x_1646_);
lean_dec(v_x_1646_);
lean_dec_ref(v_a_1645_);
v_r_1648_ = lean_box(v_res_1647_);
return v_r_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(lean_object* v_00_u03b2_1649_, lean_object* v_data_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_data_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(lean_object* v_00_u03b2_1652_, lean_object* v_a_1653_, lean_object* v_b_1654_, lean_object* v_x_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1653_, v_b_1654_, v_x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(lean_object* v_00_u03b2_1657_, lean_object* v_a_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_1658_, v_x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1661_, lean_object* v_a_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(v_00_u03b2_1661_, v_a_1662_, v_x_1663_);
lean_dec(v_x_1663_);
lean_dec_ref(v_a_1662_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(lean_object* v_msgData_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_1665_, v___y_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(lean_object* v_msgData_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(lean_object* v_00_u03b1_1675_, lean_object* v_msg_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_1676_, v___y_1677_, v___y_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1681_, lean_object* v_msg_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(v_00_u03b1_1681_, v_msg_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_object* v_00_u03b1_1687_, lean_object* v_msg_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1688_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1693_, lean_object* v_msg_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(v_00_u03b1_1693_, v_msg_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_object* v_00_u03b1_1699_, lean_object* v_preNode_1700_, lean_object* v_postNode_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1700_, v_postNode_1701_, v_x_1702_, v_x_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_preNode_1709_, lean_object* v_postNode_1710_, lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(v_00_u03b1_1708_, v_preNode_1709_, v_postNode_1710_, v_x_1711_, v_x_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(lean_object* v_n_1717_, lean_object* v_lo_1718_, lean_object* v_hi_1719_, lean_object* v_hhi_1720_, lean_object* v_pivot_1721_, lean_object* v_as_1722_, lean_object* v_i_1723_, lean_object* v_k_1724_, lean_object* v_ilo_1725_, lean_object* v_ik_1726_, lean_object* v_w_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_1719_, v_pivot_1721_, v_as_1722_, v_i_1723_, v_k_1724_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(lean_object* v_n_1729_, lean_object* v_lo_1730_, lean_object* v_hi_1731_, lean_object* v_hhi_1732_, lean_object* v_pivot_1733_, lean_object* v_as_1734_, lean_object* v_i_1735_, lean_object* v_k_1736_, lean_object* v_ilo_1737_, lean_object* v_ik_1738_, lean_object* v_w_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(v_n_1729_, v_lo_1730_, v_hi_1731_, v_hhi_1732_, v_pivot_1733_, v_as_1734_, v_i_1735_, v_k_1736_, v_ilo_1737_, v_ik_1738_, v_w_1739_);
lean_dec_ref(v_pivot_1733_);
lean_dec(v_hi_1731_);
lean_dec(v_lo_1730_);
lean_dec(v_n_1729_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1741_, lean_object* v_i_1742_, lean_object* v_source_1743_, lean_object* v_target_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v_i_1742_, v_source_1743_, v_target_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(lean_object* v_msgData_1746_, lean_object* v_macroStack_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_1746_, v_macroStack_1747_, v___y_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_1752_, lean_object* v_macroStack_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_1752_, v_macroStack_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_object* v_00_u03b1_1758_, lean_object* v_preNode_1759_, lean_object* v_postNode_1760_, lean_object* v___x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1759_, v_postNode_1760_, v___x_1761_, v_x_1762_, v_x_1763_, v___y_1764_, v___y_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(lean_object* v_00_u03b1_1768_, lean_object* v_preNode_1769_, lean_object* v_postNode_1770_, lean_object* v___x_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(v_00_u03b1_1768_, v_preNode_1769_, v_postNode_1770_, v___x_1771_, v_x_1772_, v_x_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_x_1779_, v_x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_Linter_unusedSimpArgs));
v___x_1784_ = l_Lean_Elab_Command_addLinter(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
return v_res_1786_;
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
