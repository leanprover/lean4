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
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(lean_object* v_upperBound_1_, lean_object* v_i_2_, lean_object* v_simpArgs_3_, lean_object* v_a_4_, lean_object* v_b_5_){
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
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1_ = stack[0].m_obj;
lean_object* v_i_2_ = stack[1].m_obj;
lean_object* v_simpArgs_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_b_5_ = stack[4].m_obj;
lean_object* v_res_17_;
v_res_17_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_1_, v_i_2_, v_simpArgs_3_, v_a_4_, v_b_5_);
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg___boxed(lean_object* v_upperBound_18_, lean_object* v_i_19_, lean_object* v_simpArgs_20_, lean_object* v_a_21_, lean_object* v_b_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_18_, v_i_19_, v_simpArgs_20_, v_a_21_, v_b_22_);
lean_dec_ref(v_simpArgs_20_);
lean_dec(v_i_19_);
lean_dec(v_upperBound_18_);
return v_res_24_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_25_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__0);
v___x_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_28_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_29_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
lean_ctor_set(v___x_31_, 2, v___x_30_);
lean_ctor_set(v___x_31_, 3, v___x_30_);
lean_ctor_set(v___x_31_, 4, v___x_29_);
lean_ctor_set(v___x_31_, 5, v___x_29_);
lean_ctor_set(v___x_31_, 6, v___x_29_);
lean_ctor_set(v___x_31_, 7, v___x_29_);
lean_ctor_set(v___x_31_, 8, v___x_29_);
lean_ctor_set(v___x_31_, 9, v___x_29_);
lean_ctor_set(v___x_31_, 10, v___x_29_);
lean_ctor_set(v___x_31_, 11, v___x_28_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_unsigned_to_nat(32u);
v___x_33_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4(void){
_start:
{
size_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_35_ = ((size_t)5ULL);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_unsigned_to_nat(32u);
v___x_38_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_39_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__3);
v___x_40_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
lean_ctor_set(v___x_40_, 2, v___x_36_);
lean_ctor_set(v___x_40_, 3, v___x_36_);
lean_ctor_set_usize(v___x_40_, 4, v___x_35_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = lean_box(1);
v___x_42_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__4);
v___x_43_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
v___x_44_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_41_);
return v___x_44_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(lean_object* v_msgData_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; lean_object* v_toCold_50_; lean_object* v_env_51_; lean_object* v_options_52_; uint8_t v___x_53_; lean_object* v_env_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_49_ = lean_st_ref_get(v___y_47_);
v_toCold_50_ = lean_ctor_get(v___y_46_, 0);
v_env_51_ = lean_ctor_get(v___x_49_, 0);
lean_inc_ref(v_env_51_);
lean_dec(v___x_49_);
v_options_52_ = lean_ctor_get(v_toCold_50_, 2);
v___x_53_ = 0;
v_env_54_ = l_Lean_Environment_setRecordingDeps(v_env_51_, v___x_53_);
v___x_55_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_56_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_52_);
v___x_57_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_57_, 0, v_env_54_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_56_);
lean_ctor_set(v___x_57_, 3, v_options_52_);
v___x_58_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v_msgData_45_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_45_ = stack[0].m_obj;
lean_object* v___y_46_ = stack[1].m_obj;
lean_object* v___y_47_ = stack[2].m_obj;
lean_object* v_res_60_;
v_res_60_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msgData_45_, v___y_46_, v___y_47_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___boxed(lean_object* v_msgData_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msgData_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
return v_res_65_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(lean_object* v_msg_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_ref_70_; lean_object* v___x_71_; lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_80_; 
v_ref_70_ = lean_ctor_get(v___y_67_, 2);
v___x_71_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msg_66_, v___y_67_, v___y_68_);
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_80_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
lean_inc(v_ref_70_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v_ref_70_);
lean_ctor_set(v___x_76_, 1, v_a_72_);
if (v_isShared_75_ == 0)
{
lean_ctor_set_tag(v___x_74_, 1);
lean_ctor_set(v___x_74_, 0, v___x_76_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_66_ = stack[0].m_obj;
lean_object* v___y_67_ = stack[1].m_obj;
lean_object* v___y_68_ = stack[2].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_66_, v___y_67_, v___y_68_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg___boxed(lean_object* v_msg_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_86_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_95_, uint8_t v___y_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_97_) == 1)
{
lean_object* v_pre_98_; 
v_pre_98_ = lean_ctor_get(v_x_97_, 0);
switch(lean_obj_tag(v_pre_98_))
{
case 1:
{
lean_object* v_pre_99_; 
v_pre_99_ = lean_ctor_get(v_pre_98_, 0);
switch(lean_obj_tag(v_pre_99_))
{
case 0:
{
lean_object* v_str_100_; lean_object* v_str_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_str_100_ = lean_ctor_get(v_x_97_, 1);
v_str_101_ = lean_ctor_get(v_pre_98_, 1);
v___x_102_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_103_ = lean_string_dec_eq(v_str_101_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_105_ = lean_string_dec_eq(v_str_101_, v___x_104_);
if (v___x_105_ == 0)
{
return v___x_105_;
}
else
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_107_ = lean_string_dec_eq(v_str_100_, v___x_106_);
if (v___x_107_ == 0)
{
return v___x_107_;
}
else
{
return v_suppressElabErrors_95_;
}
}
}
else
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_109_ = lean_string_dec_eq(v_str_100_, v___x_108_);
if (v___x_109_ == 0)
{
return v___x_109_;
}
else
{
return v_suppressElabErrors_95_;
}
}
}
case 1:
{
lean_object* v_pre_110_; 
v_pre_110_ = lean_ctor_get(v_pre_99_, 0);
if (lean_obj_tag(v_pre_110_) == 0)
{
lean_object* v_str_111_; lean_object* v_str_112_; lean_object* v_str_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_str_111_ = lean_ctor_get(v_x_97_, 1);
v_str_112_ = lean_ctor_get(v_pre_98_, 1);
v_str_113_ = lean_ctor_get(v_pre_99_, 1);
v___x_114_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_115_ = lean_string_dec_eq(v_str_113_, v___x_114_);
if (v___x_115_ == 0)
{
return v___x_115_;
}
else
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_117_ = lean_string_dec_eq(v_str_112_, v___x_116_);
if (v___x_117_ == 0)
{
return v___x_117_;
}
else
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_119_ = lean_string_dec_eq(v_str_111_, v___x_118_);
if (v___x_119_ == 0)
{
return v___x_119_;
}
else
{
return v_suppressElabErrors_95_;
}
}
}
}
else
{
return v___y_96_;
}
}
default: 
{
return v___y_96_;
}
}
}
case 0:
{
lean_object* v_str_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_str_120_ = lean_ctor_get(v_x_97_, 1);
v___x_121_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_122_ = lean_string_dec_eq(v_str_120_, v___x_121_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
return v_suppressElabErrors_95_;
}
}
default: 
{
return v___y_96_;
}
}
}
else
{
return v___y_96_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_95_ = stack[0].m_num;
uint8_t v___y_96_ = stack[1].m_num;
lean_object* v_x_97_ = stack[2].m_obj;
uint8_t v_res_123_;
v_res_123_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_95_, v___y_96_, v_x_97_);
stack->m_num = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_124_, lean_object* v___y_125_, lean_object* v_x_126_){
_start:
{
uint8_t v_suppressElabErrors_boxed_127_; uint8_t v___y_4882__boxed_128_; uint8_t v_res_129_; lean_object* v_r_130_; 
v_suppressElabErrors_boxed_127_ = lean_unbox(v_suppressElabErrors_124_);
v___y_4882__boxed_128_ = lean_unbox(v___y_125_);
v_res_129_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_127_, v___y_4882__boxed_128_, v_x_126_);
lean_dec(v_x_126_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_131_, lean_object* v_opt_132_){
_start:
{
lean_object* v_name_133_; lean_object* v_defValue_134_; lean_object* v_map_135_; lean_object* v___x_136_; 
v_name_133_ = lean_ctor_get(v_opt_132_, 0);
v_defValue_134_ = lean_ctor_get(v_opt_132_, 1);
v_map_135_ = lean_ctor_get(v_opts_131_, 0);
v___x_136_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_135_, v_name_133_);
if (lean_obj_tag(v___x_136_) == 0)
{
uint8_t v___x_137_; 
v___x_137_ = lean_unbox(v_defValue_134_);
return v___x_137_;
}
else
{
lean_object* v_val_138_; 
v_val_138_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_val_138_);
lean_dec_ref_known(v___x_136_, 1);
if (lean_obj_tag(v_val_138_) == 1)
{
uint8_t v_v_139_; 
v_v_139_ = lean_ctor_get_uint8(v_val_138_, 0);
lean_dec_ref_known(v_val_138_, 0);
return v_v_139_;
}
else
{
uint8_t v___x_140_; 
lean_dec(v_val_138_);
v___x_140_ = lean_unbox(v_defValue_134_);
return v___x_140_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_131_ = stack[0].m_obj;
lean_object* v_opt_132_ = stack[1].m_obj;
uint8_t v_res_141_;
v_res_141_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_131_, v_opt_132_);
stack->m_num = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_142_, lean_object* v_opt_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_142_, v_opt_143_);
lean_dec_ref(v_opt_143_);
lean_dec_ref(v_opts_142_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(lean_object* v_ref_147_, lean_object* v_msgData_148_, uint8_t v_severity_149_, uint8_t v_isSilent_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___y_155_; lean_object* v___y_156_; uint8_t v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; uint8_t v___y_160_; lean_object* v___y_161_; lean_object* v_toCold_162_; lean_object* v___y_163_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; uint8_t v___y_196_; uint8_t v___y_197_; uint8_t v___y_198_; lean_object* v___y_199_; lean_object* v___y_219_; lean_object* v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; uint8_t v___y_223_; uint8_t v___y_224_; lean_object* v___y_225_; uint8_t v___y_229_; uint8_t v___y_230_; uint8_t v___y_231_; uint8_t v___x_242_; uint8_t v___y_244_; uint8_t v___y_245_; uint8_t v___y_246_; uint8_t v___y_248_; uint8_t v___x_256_; 
v___x_242_ = 2;
v___x_256_ = l_Lean_instBEqMessageSeverity_beq(v_severity_149_, v___x_242_);
if (v___x_256_ == 0)
{
v___y_248_ = v___x_256_;
goto v___jp_247_;
}
else
{
uint8_t v___x_257_; 
lean_inc_ref(v_msgData_148_);
v___x_257_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_148_);
v___y_248_ = v___x_257_;
goto v___jp_247_;
}
v___jp_154_:
{
lean_object* v_currNamespace_164_; lean_object* v_openDecls_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_env_170_; lean_object* v_nextMacroScope_171_; lean_object* v_ngen_172_; lean_object* v_auxDeclNGen_173_; lean_object* v_traceState_174_; lean_object* v_cache_175_; lean_object* v_recordedDeps_176_; lean_object* v_messages_177_; lean_object* v_infoState_178_; lean_object* v_snapshotTasks_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_190_; 
v_currNamespace_164_ = lean_ctor_get(v_toCold_162_, 4);
v_openDecls_165_ = lean_ctor_get(v_toCold_162_, 5);
lean_inc(v_openDecls_165_);
lean_inc(v_currNamespace_164_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v_currNamespace_164_);
lean_ctor_set(v___x_166_, 1, v_openDecls_165_);
v___x_167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___y_161_);
lean_inc_ref(v___y_155_);
lean_inc_ref(v___y_158_);
v___x_168_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_168_, 0, v___y_158_);
lean_ctor_set(v___x_168_, 1, v___y_156_);
lean_ctor_set(v___x_168_, 2, v___y_159_);
lean_ctor_set(v___x_168_, 3, v___y_155_);
lean_ctor_set(v___x_168_, 4, v___x_167_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*5, v___y_160_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*5 + 1, v___y_157_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*5 + 2, v_isSilent_150_);
v___x_169_ = lean_st_ref_take(v___y_163_);
v_env_170_ = lean_ctor_get(v___x_169_, 0);
v_nextMacroScope_171_ = lean_ctor_get(v___x_169_, 1);
v_ngen_172_ = lean_ctor_get(v___x_169_, 2);
v_auxDeclNGen_173_ = lean_ctor_get(v___x_169_, 3);
v_traceState_174_ = lean_ctor_get(v___x_169_, 4);
v_cache_175_ = lean_ctor_get(v___x_169_, 5);
v_recordedDeps_176_ = lean_ctor_get(v___x_169_, 6);
v_messages_177_ = lean_ctor_get(v___x_169_, 7);
v_infoState_178_ = lean_ctor_get(v___x_169_, 8);
v_snapshotTasks_179_ = lean_ctor_get(v___x_169_, 9);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_190_ == 0)
{
v___x_181_ = v___x_169_;
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snapshotTasks_179_);
lean_inc(v_infoState_178_);
lean_inc(v_messages_177_);
lean_inc(v_recordedDeps_176_);
lean_inc(v_cache_175_);
lean_inc(v_traceState_174_);
lean_inc(v_auxDeclNGen_173_);
lean_inc(v_ngen_172_);
lean_inc(v_nextMacroScope_171_);
lean_inc(v_env_170_);
lean_dec(v___x_169_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_190_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = lean_box(0);
v___x_184_ = l_Lean_MessageLog_add(v___x_168_, v_messages_177_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 7, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_env_170_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_nextMacroScope_171_);
lean_ctor_set(v_reuseFailAlloc_189_, 2, v_ngen_172_);
lean_ctor_set(v_reuseFailAlloc_189_, 3, v_auxDeclNGen_173_);
lean_ctor_set(v_reuseFailAlloc_189_, 4, v_traceState_174_);
lean_ctor_set(v_reuseFailAlloc_189_, 5, v_cache_175_);
lean_ctor_set(v_reuseFailAlloc_189_, 6, v_recordedDeps_176_);
lean_ctor_set(v_reuseFailAlloc_189_, 7, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_189_, 8, v_infoState_178_);
lean_ctor_set(v_reuseFailAlloc_189_, 9, v_snapshotTasks_179_);
v___x_186_ = v_reuseFailAlloc_189_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_st_ref_put(v___y_163_, v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_183_);
return v___x_188_;
}
}
}
v___jp_191_:
{
lean_object* v_fileName_200_; lean_object* v_fileMap_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_217_; 
v_fileName_200_ = lean_ctor_get(v___y_195_, 0);
v_fileMap_201_ = lean_ctor_get(v___y_195_, 1);
v___x_202_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_148_);
v___x_203_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v___x_202_, v___y_151_, v___y_152_);
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_217_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_217_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_217_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_inc_ref_n(v_fileMap_201_, 2);
v___x_208_ = l_Lean_FileMap_toPosition(v_fileMap_201_, v___y_194_);
lean_dec(v___y_194_);
v___x_209_ = l_Lean_FileMap_toPosition(v_fileMap_201_, v___y_199_);
lean_dec(v___y_199_);
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
v___x_211_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0));
if (v___y_196_ == 0)
{
lean_del_object(v___x_206_);
lean_dec_ref(v___y_193_);
v___y_155_ = v___x_211_;
v___y_156_ = v___x_208_;
v___y_157_ = v___y_197_;
v___y_158_ = v_fileName_200_;
v___y_159_ = v___x_210_;
v___y_160_ = v___y_198_;
v___y_161_ = v_a_204_;
v_toCold_162_ = v___y_192_;
v___y_163_ = v___y_152_;
goto v___jp_154_;
}
else
{
uint8_t v___x_212_; 
lean_inc(v_a_204_);
v___x_212_ = l_Lean_MessageData_hasTag(v___y_193_, v_a_204_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_215_; 
lean_dec_ref_known(v___x_210_, 1);
lean_dec_ref(v___x_208_);
lean_dec(v_a_204_);
v___x_213_ = lean_box(0);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_213_);
v___x_215_ = v___x_206_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
else
{
lean_del_object(v___x_206_);
v___y_155_ = v___x_211_;
v___y_156_ = v___x_208_;
v___y_157_ = v___y_197_;
v___y_158_ = v_fileName_200_;
v___y_159_ = v___x_210_;
v___y_160_ = v___y_198_;
v___y_161_ = v_a_204_;
v_toCold_162_ = v___y_192_;
v___y_163_ = v___y_152_;
goto v___jp_154_;
}
}
}
}
v___jp_218_:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Syntax_getTailPos_x3f(v___y_222_, v___y_224_);
lean_dec(v___y_222_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_inc(v___y_225_);
v___y_192_ = v___y_219_;
v___y_193_ = v___y_220_;
v___y_194_ = v___y_225_;
v___y_195_ = v___y_219_;
v___y_196_ = v___y_221_;
v___y_197_ = v___y_223_;
v___y_198_ = v___y_224_;
v___y_199_ = v___y_225_;
goto v___jp_191_;
}
else
{
lean_object* v_val_227_; 
v_val_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_226_, 1);
v___y_192_ = v___y_219_;
v___y_193_ = v___y_220_;
v___y_194_ = v___y_225_;
v___y_195_ = v___y_219_;
v___y_196_ = v___y_221_;
v___y_197_ = v___y_223_;
v___y_198_ = v___y_224_;
v___y_199_ = v_val_227_;
goto v___jp_191_;
}
}
v___jp_228_:
{
lean_object* v_toCold_232_; lean_object* v_ref_233_; uint8_t v_suppressElabErrors_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___f_237_; lean_object* v_ref_238_; lean_object* v___x_239_; 
v_toCold_232_ = lean_ctor_get(v___y_151_, 0);
v_ref_233_ = lean_ctor_get(v___y_151_, 2);
v_suppressElabErrors_234_ = lean_ctor_get_uint8(v___y_151_, sizeof(void*)*3 + 2);
v___x_235_ = lean_box(v_suppressElabErrors_234_);
v___x_236_ = lean_box(v___y_229_);
v___f_237_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_237_, 0, v___x_235_);
lean_closure_set(v___f_237_, 1, v___x_236_);
v_ref_238_ = l_Lean_replaceRef(v_ref_147_, v_ref_233_);
v___x_239_ = l_Lean_Syntax_getPos_x3f(v_ref_238_, v___y_230_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___y_219_ = v_toCold_232_;
v___y_220_ = v___f_237_;
v___y_221_ = v_suppressElabErrors_234_;
v___y_222_ = v_ref_238_;
v___y_223_ = v___y_231_;
v___y_224_ = v___y_230_;
v___y_225_ = v___x_240_;
goto v___jp_218_;
}
else
{
lean_object* v_val_241_; 
v_val_241_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_239_, 1);
v___y_219_ = v_toCold_232_;
v___y_220_ = v___f_237_;
v___y_221_ = v_suppressElabErrors_234_;
v___y_222_ = v_ref_238_;
v___y_223_ = v___y_231_;
v___y_224_ = v___y_230_;
v___y_225_ = v_val_241_;
goto v___jp_218_;
}
}
v___jp_243_:
{
if (v___y_246_ == 0)
{
v___y_229_ = v___y_244_;
v___y_230_ = v___y_245_;
v___y_231_ = v_severity_149_;
goto v___jp_228_;
}
else
{
v___y_229_ = v___y_244_;
v___y_230_ = v___y_245_;
v___y_231_ = v___x_242_;
goto v___jp_228_;
}
}
v___jp_247_:
{
if (v___y_248_ == 0)
{
uint8_t v___x_249_; uint8_t v___x_250_; 
v___x_249_ = 1;
v___x_250_ = l_Lean_instBEqMessageSeverity_beq(v_severity_149_, v___x_249_);
if (v___x_250_ == 0)
{
v___y_244_ = v___y_248_;
v___y_245_ = v___y_248_;
v___y_246_ = v___x_250_;
goto v___jp_243_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_151_);
v___x_252_ = l_Lean_warningAsError;
v___x_253_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v___x_251_, v___x_252_);
lean_dec_ref(v___x_251_);
v___y_244_ = v___y_248_;
v___y_245_ = v___y_248_;
v___y_246_ = v___x_253_;
goto v___jp_243_;
}
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec_ref(v_msgData_148_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_147_ = stack[0].m_obj;
lean_object* v_msgData_148_ = stack[1].m_obj;
uint8_t v_severity_149_ = stack[2].m_num;
uint8_t v_isSilent_150_ = stack[3].m_num;
lean_object* v___y_151_ = stack[4].m_obj;
lean_object* v___y_152_ = stack[5].m_obj;
lean_object* v_res_258_;
v_res_258_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_147_, v_msgData_148_, v_severity_149_, v_isSilent_150_, v___y_151_, v___y_152_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_259_, lean_object* v_msgData_260_, lean_object* v_severity_261_, lean_object* v_isSilent_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
uint8_t v_severity_boxed_266_; uint8_t v_isSilent_boxed_267_; lean_object* v_res_268_; 
v_severity_boxed_266_ = lean_unbox(v_severity_261_);
v_isSilent_boxed_267_ = lean_unbox(v_isSilent_262_);
v_res_268_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_259_, v_msgData_260_, v_severity_boxed_266_, v_isSilent_boxed_267_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v_ref_259_);
return v_res_268_;
}
}
lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(lean_object* v_ref_269_, lean_object* v_msgData_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
uint8_t v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; 
v___x_274_ = 1;
v___x_275_ = 0;
v___x_276_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_269_, v_msgData_270_, v___x_274_, v___x_275_, v___y_271_, v___y_272_);
return v___x_276_;
}
}
LEAN_EXPORT void l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_269_ = stack[0].m_obj;
lean_object* v_msgData_270_ = stack[1].m_obj;
lean_object* v___y_271_ = stack[2].m_obj;
lean_object* v___y_272_ = stack[3].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_269_, v_msgData_270_, v___y_271_, v___y_272_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(lean_object* v_ref_278_, lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_278_, v_msgData_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v_ref_278_);
return v_res_283_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2));
v___x_289_ = l_Lean_stringToMessageData(v___x_288_);
return v___x_289_;
}
}
lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(lean_object* v_linterOption_290_, lean_object* v_stx_291_, lean_object* v_msg_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_name_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_314_; 
v_name_296_ = lean_ctor_get(v_linterOption_290_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v_linterOption_290_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v_linterOption_290_, 1);
lean_dec(v_unused_315_);
v___x_298_ = v_linterOption_290_;
v_isShared_299_ = v_isSharedCheck_314_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_name_296_);
lean_dec(v_linterOption_290_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_314_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_300_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1);
lean_inc(v_name_296_);
v___x_301_ = l_Lean_MessageData_ofName(v_name_296_);
if (v_isShared_299_ == 0)
{
lean_ctor_set_tag(v___x_298_, 7);
lean_ctor_set(v___x_298_, 1, v___x_301_);
lean_ctor_set(v___x_298_, 0, v___x_300_);
v___x_303_ = v___x_298_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_301_);
v___x_303_ = v_reuseFailAlloc_313_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_disable_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_304_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v_disable_306_ = l_Lean_MessageData_note(v___x_305_);
v___x_307_ = l_Lean_Linter_linterMessageTag;
v___x_308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_308_, 0, v_msg_292_);
lean_ctor_set(v___x_308_, 1, v_disable_306_);
v___x_309_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_310_, 0, v_name_296_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
lean_inc(v_stx_291_);
v___x_311_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_311_, 0, v_stx_291_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_stx_291_, v___x_311_, v___y_293_, v___y_294_);
lean_dec(v_stx_291_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_linterOption_290_ = stack[0].m_obj;
lean_object* v_stx_291_ = stack[1].m_obj;
lean_object* v_msg_292_ = stack[2].m_obj;
lean_object* v___y_293_ = stack[3].m_obj;
lean_object* v___y_294_ = stack[4].m_obj;
lean_object* v_res_316_;
v_res_316_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_290_, v_stx_291_, v_msg_292_, v___y_293_, v___y_294_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(lean_object* v_linterOption_317_, lean_object* v_stx_318_, lean_object* v_msg_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_317_, v_stx_318_, v_msg_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_323_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6));
v___x_336_ = l_Lean_MessageData_ofFormat(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13);
v___x_349_ = l_Lean_MessageData_note(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17));
v___x_355_ = l_Lean_stringToMessageData(v___x_354_);
return v___x_355_;
}
}
lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(lean_object* v_stx_356_, lean_object* v_i_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v_hint_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_simpArgs_372_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_370_ = lean_box(0);
v___x_371_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1));
v_simpArgs_372_ = l_Lean_Elab_Tactic_getSimpParams(v_stx_356_);
v___x_423_ = lean_array_get_size(v_simpArgs_372_);
v___x_424_ = lean_nat_dec_lt(v_i_357_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec_ref(v_simpArgs_372_);
v___x_425_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16);
v___x_426_ = l_Nat_reprFast(v_i_357_);
v___x_427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
v___x_428_ = l_Lean_MessageData_ofFormat(v___x_427_);
v___x_429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_425_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18);
v___x_431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = l_Lean_MessageData_ofSyntax(v_stx_356_);
v___x_433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v___x_432_);
v___x_434_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v___x_433_, v_a_358_, v_a_359_);
return v___x_434_;
}
else
{
v___y_374_ = v_a_358_;
v___y_375_ = v_a_359_;
goto v___jp_373_;
}
v___jp_361_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___y_363_);
lean_ctor_set(v___x_368_, 1, v_hint_364_);
v___x_369_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_367_, v___y_362_, v___x_368_, v___y_365_, v___y_366_);
return v___x_369_;
}
v___jp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_argStx_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_msg_382_; lean_object* v_otherArgs_383_; lean_object* v___x_384_; 
v___x_376_ = lean_array_get_size(v_simpArgs_372_);
v___x_377_ = lean_unsigned_to_nat(0u);
v_argStx_378_ = lean_array_get(v___x_370_, v_simpArgs_372_, v_i_357_);
v___x_379_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3);
lean_inc(v_argStx_378_);
v___x_380_ = l_Lean_MessageData_ofSyntax(v_argStx_378_);
v___x_381_ = l_Lean_indentD(v___x_380_);
v_msg_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_382_, 0, v___x_379_);
lean_ctor_set(v_msg_382_, 1, v___x_381_);
v_otherArgs_383_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4));
v___x_384_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v___x_376_, v_i_357_, v_simpArgs_372_, v___x_377_, v_otherArgs_383_);
lean_dec_ref(v_simpArgs_372_);
lean_dec(v_i_357_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
lean_inc(v_stx_356_);
v___x_386_ = l_Lean_Elab_Tactic_setSimpParams(v_stx_356_, v_a_385_);
lean_dec(v_a_385_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_371_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_box(0);
v___x_389_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
lean_ctor_set(v___x_389_, 3, v___x_388_);
lean_ctor_set(v___x_389_, 4, v___x_388_);
lean_ctor_set(v___x_389_, 5, v___x_388_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v_stx_356_);
v___x_391_ = 4;
v___x_392_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_392_, 0, v___x_389_);
lean_ctor_set(v___x_392_, 1, v___x_390_);
lean_ctor_set(v___x_392_, 2, v___x_388_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*3, v___x_391_);
v___x_393_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7);
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_mk_empty_array_with_capacity(v___x_394_);
v___x_396_ = lean_array_push(v___x_395_, v___x_392_);
v___x_397_ = 0;
v___x_398_ = l_Lean_MessageData_hint(v___x_393_, v___x_396_, v___x_388_, v___x_388_, v___x_397_, v___y_374_, v___y_375_);
lean_dec_ref(v___x_396_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
lean_inc(v_argStx_378_);
v___x_400_ = l_Lean_Syntax_getKind(v_argStx_378_);
v___x_401_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11));
v___x_402_ = lean_name_eq(v___x_400_, v___x_401_);
lean_dec(v___x_400_);
if (v___x_402_ == 0)
{
v___y_362_ = v_argStx_378_;
v___y_363_ = v_msg_382_;
v_hint_364_ = v_a_399_;
v___y_365_ = v___y_374_;
v___y_366_ = v___y_375_;
goto v___jp_361_;
}
else
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = l_Lean_Syntax_getArg(v_argStx_378_, v___x_394_);
v___x_404_ = l_Lean_Syntax_isNone(v___x_403_);
lean_dec(v___x_403_);
if (v___x_404_ == 0)
{
if (v___x_402_ == 0)
{
v___y_362_ = v_argStx_378_;
v___y_363_ = v_msg_382_;
v_hint_364_ = v_a_399_;
v___y_365_ = v___y_374_;
v___y_366_ = v___y_375_;
goto v___jp_361_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14);
v___x_406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_406_, 0, v_a_399_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___y_362_ = v_argStx_378_;
v___y_363_ = v_msg_382_;
v_hint_364_ = v___x_406_;
v___y_365_ = v___y_374_;
v___y_366_ = v___y_375_;
goto v___jp_361_;
}
}
else
{
v___y_362_ = v_argStx_378_;
v___y_363_ = v_msg_382_;
v_hint_364_ = v_a_399_;
v___y_365_ = v___y_374_;
v___y_366_ = v___y_375_;
goto v___jp_361_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref_known(v_msg_382_, 2);
lean_dec(v_argStx_378_);
v_a_407_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_398_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_398_);
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
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref_known(v_msg_382_, 2);
lean_dec(v_argStx_378_);
lean_dec(v_stx_356_);
v_a_415_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_384_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_384_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_356_ = stack[0].m_obj;
lean_object* v_i_357_ = stack[1].m_obj;
lean_object* v_a_358_ = stack[2].m_obj;
lean_object* v_a_359_ = stack[3].m_obj;
lean_object* v_res_435_;
v_res_435_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(v_stx_356_, v_i_357_, v_a_358_, v_a_359_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed(lean_object* v_stx_436_, lean_object* v_i_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(v_stx_436_, v_i_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_441_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(lean_object* v_upperBound_442_, lean_object* v_i_443_, lean_object* v_simpArgs_444_, lean_object* v_inst_445_, lean_object* v_R_446_, lean_object* v_a_447_, lean_object* v_b_448_, lean_object* v_c_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_442_, v_i_443_, v_simpArgs_444_, v_a_447_, v_b_448_);
return v___x_453_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_442_ = stack[0].m_obj;
lean_object* v_i_443_ = stack[1].m_obj;
lean_object* v_simpArgs_444_ = stack[2].m_obj;
lean_object* v_a_447_ = stack[5].m_obj;
lean_object* v_b_448_ = stack[6].m_obj;
lean_object* v___y_450_ = stack[8].m_obj;
lean_object* v___y_451_ = stack[9].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_442_, v_i_443_, v_simpArgs_444_, lean_box(0), lean_box(0), v_a_447_, v_b_448_, lean_box(0), v___y_450_, v___y_451_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(lean_object* v_upperBound_455_, lean_object* v_i_456_, lean_object* v_simpArgs_457_, lean_object* v_inst_458_, lean_object* v_R_459_, lean_object* v_a_460_, lean_object* v_b_461_, lean_object* v_c_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_455_, v_i_456_, v_simpArgs_457_, v_inst_458_, v_R_459_, v_a_460_, v_b_461_, v_c_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_simpArgs_457_);
lean_dec(v_i_456_);
lean_dec(v_upperBound_455_);
return v_res_466_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(lean_object* v_00_u03b1_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_468_, v___y_469_, v___y_470_);
return v___x_472_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_468_ = stack[1].m_obj;
lean_object* v___y_469_ = stack[2].m_obj;
lean_object* v___y_470_ = stack[3].m_obj;
lean_object* v_res_473_;
v_res_473_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(lean_box(0), v_msg_468_, v___y_469_, v___y_470_);
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(lean_object* v_00_u03b1_474_, lean_object* v_msg_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(v_00_u03b1_474_, v_msg_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_479_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object* v_upperBound_480_, lean_object* v_snd_481_, lean_object* v_fst_482_, lean_object* v_a_483_, lean_object* v_b_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_a_489_; uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_lt(v_a_483_, v_upperBound_480_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v_a_483_);
lean_dec(v_fst_482_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_b_484_);
return v___x_494_;
}
else
{
uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_495_ = 0;
v___x_496_ = lean_box(0);
v___x_497_ = lean_box(v___x_495_);
v___x_498_ = lean_array_get(v___x_497_, v_snd_481_, v_a_483_);
lean_dec(v___x_497_);
v___x_499_ = lean_unbox(v___x_498_);
lean_dec(v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_inc(v_a_483_);
lean_inc(v_fst_482_);
v___x_500_ = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed), 5, 2);
lean_closure_set(v___x_500_, 0, v_fst_482_);
lean_closure_set(v___x_500_, 1, v_a_483_);
v___x_501_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_500_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_dec_ref_known(v___x_501_, 1);
v_a_489_ = v___x_496_;
goto v___jp_488_;
}
else
{
lean_dec(v_a_483_);
lean_dec(v_fst_482_);
return v___x_501_;
}
}
else
{
v_a_489_ = v___x_496_;
goto v___jp_488_;
}
}
v___jp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_a_483_, v___x_490_);
lean_dec(v_a_483_);
v_a_483_ = v___x_491_;
v_b_484_ = v_a_489_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_480_ = stack[0].m_obj;
lean_object* v_snd_481_ = stack[1].m_obj;
lean_object* v_fst_482_ = stack[2].m_obj;
lean_object* v_a_483_ = stack[3].m_obj;
lean_object* v_b_484_ = stack[4].m_obj;
lean_object* v___y_485_ = stack[5].m_obj;
lean_object* v___y_486_ = stack[6].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_480_, v_snd_481_, v_fst_482_, v_a_483_, v_b_484_, v___y_485_, v___y_486_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object* v_upperBound_503_, lean_object* v_snd_504_, lean_object* v_fst_505_, lean_object* v_a_506_, lean_object* v_b_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_503_, v_snd_504_, v_fst_505_, v_a_506_, v_b_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_snd_504_);
lean_dec(v_upperBound_503_);
return v_res_511_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(lean_object* v_as_512_, size_t v_sz_513_, size_t v_i_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_usize_dec_lt(v_i_514_, v_sz_513_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v_b_515_);
return v___x_520_;
}
else
{
lean_object* v_a_521_; lean_object* v_snd_522_; lean_object* v_fst_523_; lean_object* v_snd_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_a_521_ = lean_array_uget_borrowed(v_as_512_, v_i_514_);
v_snd_522_ = lean_ctor_get(v_a_521_, 1);
v_fst_523_ = lean_ctor_get(v_snd_522_, 0);
v_snd_524_ = lean_ctor_get(v_snd_522_, 1);
v___x_525_ = lean_box(0);
v___x_526_ = lean_array_get_size(v_snd_524_);
v___x_527_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_523_);
v___x_528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_526_, v_snd_524_, v_fst_523_, v___x_527_, v___x_525_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_528_) == 0)
{
size_t v___x_529_; size_t v___x_530_; 
lean_dec_ref_known(v___x_528_, 1);
v___x_529_ = ((size_t)1ULL);
v___x_530_ = lean_usize_add(v_i_514_, v___x_529_);
v_i_514_ = v___x_530_;
v_b_515_ = v___x_525_;
goto _start;
}
else
{
return v___x_528_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_512_ = stack[0].m_obj;
size_t v_sz_513_ = stack[1].m_num;
size_t v_i_514_ = stack[2].m_num;
lean_object* v_b_515_ = stack[3].m_obj;
lean_object* v___y_516_ = stack[4].m_obj;
lean_object* v___y_517_ = stack[5].m_obj;
lean_object* v_res_532_;
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_512_, v_sz_513_, v_i_514_, v_b_515_, v___y_516_, v___y_517_);
stack->m_obj
 = v_res_532_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object* v_as_533_, lean_object* v_sz_534_, lean_object* v_i_535_, lean_object* v_b_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_534_);
lean_dec(v_sz_534_);
v_i_boxed_541_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_533_, v_sz_boxed_540_, v_i_boxed_541_, v_b_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec_ref(v_as_533_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(lean_object* v_hi_543_, lean_object* v_pivot_544_, lean_object* v_as_545_, lean_object* v_i_546_, lean_object* v_k_547_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = lean_nat_dec_lt(v_k_547_, v_hi_543_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v_k_547_);
v___x_549_ = lean_array_fswap(v_as_545_, v_i_546_, v_hi_543_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_i_546_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v_fst_552_; lean_object* v_fst_553_; lean_object* v_start_554_; lean_object* v_start_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_551_ = lean_array_fget_borrowed(v_as_545_, v_k_547_);
v_fst_552_ = lean_ctor_get(v___x_551_, 0);
v_fst_553_ = lean_ctor_get(v_pivot_544_, 0);
v_start_554_ = lean_ctor_get(v_fst_552_, 0);
v_start_555_ = lean_ctor_get(v_fst_553_, 0);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_add(v_start_554_, v___x_556_);
v___x_558_ = lean_nat_dec_le(v___x_557_, v_start_555_);
lean_dec(v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
v___x_559_ = lean_nat_add(v_k_547_, v___x_556_);
lean_dec(v_k_547_);
v_k_547_ = v___x_559_;
goto _start;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_array_fswap(v_as_545_, v_i_546_, v_k_547_);
v___x_562_ = lean_nat_add(v_i_546_, v___x_556_);
lean_dec(v_i_546_);
v___x_563_ = lean_nat_add(v_k_547_, v___x_556_);
lean_dec(v_k_547_);
v_as_545_ = v___x_561_;
v_i_546_ = v___x_562_;
v_k_547_ = v___x_563_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg___boxed(lean_object* v_hi_565_, lean_object* v_pivot_566_, lean_object* v_as_567_, lean_object* v_i_568_, lean_object* v_k_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_565_, v_pivot_566_, v_as_567_, v_i_568_, v_k_569_);
lean_dec_ref(v_pivot_566_);
lean_dec(v_hi_565_);
return v_res_570_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(lean_object* v_x1_571_, lean_object* v_x2_572_){
_start:
{
lean_object* v_fst_573_; lean_object* v_fst_574_; lean_object* v_start_575_; lean_object* v_start_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_fst_573_ = lean_ctor_get(v_x1_571_, 0);
v_fst_574_ = lean_ctor_get(v_x2_572_, 0);
v_start_575_ = lean_ctor_get(v_fst_573_, 0);
v_start_576_ = lean_ctor_get(v_fst_574_, 0);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_start_575_, v___x_577_);
v___x_579_ = lean_nat_dec_le(v___x_578_, v_start_576_);
lean_dec(v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_571_ = stack[0].m_obj;
lean_object* v_x2_572_ = stack[1].m_obj;
uint8_t v_res_580_;
v_res_580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v_x1_571_, v_x2_572_);
stack->m_num = v_res_580_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0___boxed(lean_object* v_x1_581_, lean_object* v_x2_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v_x1_581_, v_x2_582_);
lean_dec_ref(v_x2_582_);
lean_dec_ref(v_x1_581_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(lean_object* v_n_585_, lean_object* v_as_586_, lean_object* v_lo_587_, lean_object* v_hi_588_){
_start:
{
lean_object* v___y_590_; uint8_t v___x_600_; 
v___x_600_ = lean_nat_dec_lt(v_lo_587_, v_hi_588_);
if (v___x_600_ == 0)
{
lean_dec(v_lo_587_);
return v_as_586_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_mid_603_; lean_object* v___y_605_; lean_object* v___y_611_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_601_ = lean_nat_add(v_lo_587_, v_hi_588_);
v___x_602_ = lean_unsigned_to_nat(1u);
v_mid_603_ = lean_nat_shiftr(v___x_601_, v___x_602_);
lean_dec(v___x_601_);
v___x_616_ = lean_array_fget_borrowed(v_as_586_, v_mid_603_);
v___x_617_ = lean_array_fget_borrowed(v_as_586_, v_lo_587_);
v___x_618_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
v___y_611_ = v_as_586_;
goto v___jp_610_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_array_fswap(v_as_586_, v_lo_587_, v_mid_603_);
v___y_611_ = v___x_619_;
goto v___jp_610_;
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_array_fget_borrowed(v___y_605_, v_mid_603_);
v___x_607_ = lean_array_fget_borrowed(v___y_605_, v_hi_588_);
v___x_608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_mid_603_);
v___y_590_ = v___y_605_;
goto v___jp_589_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_array_fswap(v___y_605_, v_mid_603_, v_hi_588_);
lean_dec(v_mid_603_);
v___y_590_ = v___x_609_;
goto v___jp_589_;
}
}
v___jp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_array_fget_borrowed(v___y_611_, v_hi_588_);
v___x_613_ = lean_array_fget_borrowed(v___y_611_, v_lo_587_);
v___x_614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
v___y_605_ = v___y_611_;
goto v___jp_604_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_fswap(v___y_611_, v_lo_587_, v_hi_588_);
v___y_605_ = v___x_615_;
goto v___jp_604_;
}
}
}
v___jp_589_:
{
lean_object* v_pivot_591_; lean_object* v___x_592_; lean_object* v_fst_593_; lean_object* v_snd_594_; uint8_t v___x_595_; 
v_pivot_591_ = lean_array_fget(v___y_590_, v_hi_588_);
lean_inc_n(v_lo_587_, 2);
v___x_592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_588_, v_pivot_591_, v___y_590_, v_lo_587_, v_lo_587_);
lean_dec(v_pivot_591_);
v_fst_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_fst_593_);
v_snd_594_ = lean_ctor_get(v___x_592_, 1);
lean_inc(v_snd_594_);
lean_dec_ref(v___x_592_);
v___x_595_ = lean_nat_dec_le(v_hi_588_, v_fst_593_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_585_, v_snd_594_, v_lo_587_, v_fst_593_);
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_fst_593_, v___x_597_);
lean_dec(v_fst_593_);
v_as_586_ = v___x_596_;
v_lo_587_ = v___x_598_;
goto _start;
}
else
{
lean_dec(v_fst_593_);
lean_dec(v_lo_587_);
return v_snd_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___boxed(lean_object* v_n_620_, lean_object* v_as_621_, lean_object* v_lo_622_, lean_object* v_hi_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_620_, v_as_621_, v_lo_622_, v_hi_623_);
lean_dec(v_hi_623_);
lean_dec(v_n_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
if (lean_obj_tag(v_x_626_) == 0)
{
return v_x_625_;
}
else
{
lean_object* v_key_627_; lean_object* v_value_628_; lean_object* v_tail_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_key_627_ = lean_ctor_get(v_x_626_, 0);
v_value_628_ = lean_ctor_get(v_x_626_, 1);
v_tail_629_ = lean_ctor_get(v_x_626_, 2);
lean_inc(v_value_628_);
lean_inc(v_key_627_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_key_627_);
lean_ctor_set(v___x_630_, 1, v_value_628_);
v___x_631_ = lean_array_push(v_x_625_, v___x_630_);
v_x_625_ = v___x_631_;
v_x_626_ = v_tail_629_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10___boxed(lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_x_633_, v_x_634_);
lean_dec(v_x_634_);
return v_res_635_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_eq(v_i_637_, v_stop_638_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; size_t v___x_643_; size_t v___x_644_; 
v___x_641_ = lean_array_uget_borrowed(v_as_636_, v_i_637_);
v___x_642_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_b_639_, v___x_641_);
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_637_, v___x_643_);
v_i_637_ = v___x_644_;
v_b_639_ = v___x_642_;
goto _start;
}
else
{
return v_b_639_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_636_ = stack[0].m_obj;
size_t v_i_637_ = stack[1].m_num;
size_t v_stop_638_ = stack[2].m_num;
lean_object* v_b_639_ = stack[3].m_obj;
lean_object* v_res_646_;
v_res_646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_as_636_, v_i_637_, v_stop_638_, v_b_639_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(lean_object* v_as_647_, lean_object* v_i_648_, lean_object* v_stop_649_, lean_object* v_b_650_){
_start:
{
size_t v_i_boxed_651_; size_t v_stop_boxed_652_; lean_object* v_res_653_; 
v_i_boxed_651_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_stop_boxed_652_ = lean_unbox_usize(v_stop_649_);
lean_dec(v_stop_649_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_as_647_, v_i_boxed_651_, v_stop_boxed_652_, v_b_650_);
lean_dec_ref(v_as_647_);
return v_res_653_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(lean_object* v_o_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_env_659_; lean_object* v___x_660_; lean_object* v_toEnvExtension_661_; lean_object* v_asyncMode_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v_merged_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v___x_657_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_658_ = lean_st_ref_get(v___y_655_);
v_env_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref(v_env_659_);
lean_dec(v___x_658_);
v___x_660_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_661_ = lean_ctor_get(v___x_660_, 0);
v_asyncMode_662_ = lean_ctor_get(v_toEnvExtension_661_, 2);
v___x_663_ = lean_box(0);
v___x_664_ = 0;
v___x_665_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_657_, v___x_660_, v_env_659_, v_asyncMode_662_, v___x_663_, v___x_664_);
v_merged_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_665_, 1);
lean_dec(v_unused_675_);
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_merged_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v_merged_666_);
lean_ctor_set(v___x_668_, 0, v_o_654_);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_o_654_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_merged_666_);
v___x_671_ = v_reuseFailAlloc_673_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_654_ = stack[0].m_obj;
lean_object* v___y_655_ = stack[1].m_obj;
lean_object* v_res_676_;
v_res_676_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_654_, v___y_655_);
stack->m_obj
 = v_res_676_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(lean_object* v_o_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_677_, v___y_678_);
lean_dec(v___y_678_);
return v_res_680_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_scopes_686_; lean_object* v___x_687_; lean_object* v_opts_688_; lean_object* v___x_689_; 
v___x_684_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_685_ = lean_st_ref_get(v___y_682_);
v_scopes_686_ = lean_ctor_get(v___x_685_, 2);
lean_inc(v_scopes_686_);
lean_dec(v___x_685_);
v___x_687_ = l_List_head_x21___redArg(v___x_684_, v_scopes_686_);
lean_dec(v_scopes_686_);
v_opts_688_ = lean_ctor_get(v___x_687_, 1);
lean_inc_ref(v_opts_688_);
lean_dec(v___x_687_);
v___x_689_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_opts_688_, v___y_682_);
return v___x_689_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_681_ = stack[0].m_obj;
lean_object* v___y_682_ = stack[1].m_obj;
lean_object* v_res_690_;
v_res_690_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_681_, v___y_682_);
stack->m_obj
 = v_res_690_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(lean_object* v_a_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_box(0);
return v___x_697_;
}
else
{
lean_object* v_key_698_; lean_object* v_value_699_; lean_object* v_tail_700_; uint8_t v___x_701_; 
v_key_698_ = lean_ctor_get(v_x_696_, 0);
v_value_699_ = lean_ctor_get(v_x_696_, 1);
v_tail_700_ = lean_ctor_get(v_x_696_, 2);
v___x_701_ = l_Lean_Syntax_instBEqRange_beq(v_key_698_, v_a_695_);
if (v___x_701_ == 0)
{
v_x_696_ = v_tail_700_;
goto _start;
}
else
{
lean_object* v___x_703_; 
lean_inc(v_value_699_);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v_value_699_);
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(lean_object* v_a_704_, lean_object* v_x_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_704_, v_x_705_);
lean_dec(v_x_705_);
lean_dec_ref(v_a_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object* v_m_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_buckets_709_; lean_object* v___x_710_; uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; uint64_t v_fold_714_; uint64_t v___x_715_; uint64_t v___x_716_; uint64_t v___x_717_; size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_buckets_709_ = lean_ctor_get(v_m_707_, 1);
v___x_710_ = lean_array_get_size(v_buckets_709_);
v___x_711_ = l_Lean_Syntax_instHashableRange_hash(v_a_708_);
v___x_712_ = 32ULL;
v___x_713_ = lean_uint64_shift_right(v___x_711_, v___x_712_);
v_fold_714_ = lean_uint64_xor(v___x_711_, v___x_713_);
v___x_715_ = 16ULL;
v___x_716_ = lean_uint64_shift_right(v_fold_714_, v___x_715_);
v___x_717_ = lean_uint64_xor(v_fold_714_, v___x_716_);
v___x_718_ = lean_uint64_to_usize(v___x_717_);
v___x_719_ = lean_usize_of_nat(v___x_710_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_sub(v___x_719_, v___x_720_);
v___x_722_ = lean_usize_land(v___x_718_, v___x_721_);
v___x_723_ = lean_array_uget_borrowed(v_buckets_709_, v___x_722_);
v___x_724_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_708_, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object* v_m_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_725_, v_a_726_);
lean_dec_ref(v_a_726_);
lean_dec_ref(v_m_725_);
return v_res_727_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(uint8_t v___x_728_, lean_object* v_as_729_, lean_object* v_bs_730_, lean_object* v_i_731_, lean_object* v_cs_732_){
_start:
{
uint8_t v___y_734_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = lean_array_get_size(v_as_729_);
v___x_741_ = lean_nat_dec_lt(v_i_731_, v___x_740_);
if (v___x_741_ == 0)
{
lean_dec(v_i_731_);
return v_cs_732_;
}
else
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_array_get_size(v_bs_730_);
v___x_743_ = lean_nat_dec_lt(v_i_731_, v___x_742_);
if (v___x_743_ == 0)
{
lean_dec(v_i_731_);
return v_cs_732_;
}
else
{
lean_object* v_a_744_; uint8_t v___x_745_; 
v_a_744_ = lean_array_fget_borrowed(v_as_729_, v_i_731_);
v___x_745_ = lean_unbox(v_a_744_);
if (v___x_745_ == 0)
{
lean_object* v_b_746_; uint8_t v___x_747_; 
v_b_746_ = lean_array_fget_borrowed(v_bs_730_, v_i_731_);
v___x_747_ = lean_unbox(v_b_746_);
v___y_734_ = v___x_747_;
goto v___jp_733_;
}
else
{
v___y_734_ = v___x_728_;
goto v___jp_733_;
}
}
}
v___jp_733_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_i_731_, v___x_735_);
lean_dec(v_i_731_);
v___x_737_ = lean_box(v___y_734_);
v___x_738_ = lean_array_push(v_cs_732_, v___x_737_);
v_i_731_ = v___x_736_;
v_cs_732_ = v___x_738_;
goto _start;
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_728_ = stack[0].m_num;
lean_object* v_as_729_ = stack[1].m_obj;
lean_object* v_bs_730_ = stack[2].m_obj;
lean_object* v_i_731_ = stack[3].m_obj;
lean_object* v_cs_732_ = stack[4].m_obj;
lean_object* v_res_748_;
v_res_748_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_728_, v_as_729_, v_bs_730_, v_i_731_, v_cs_732_);
stack->m_obj
 = v_res_748_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object* v___x_749_, lean_object* v_as_750_, lean_object* v_bs_751_, lean_object* v_i_752_, lean_object* v_cs_753_){
_start:
{
uint8_t v___x_13023__boxed_754_; lean_object* v_res_755_; 
v___x_13023__boxed_754_ = lean_unbox(v___x_749_);
v_res_755_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_13023__boxed_754_, v_as_750_, v_bs_751_, v_i_752_, v_cs_753_);
lean_dec_ref(v_bs_751_);
lean_dec_ref(v_as_750_);
return v_res_755_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(lean_object* v_msgData_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_759_; lean_object* v_env_760_; uint8_t v___x_761_; lean_object* v_env_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_scopes_765_; lean_object* v___x_766_; lean_object* v_opts_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_759_ = lean_st_ref_get(v___y_757_);
v_env_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc_ref(v_env_760_);
lean_dec(v___x_759_);
v___x_761_ = 0;
v_env_762_ = l_Lean_Environment_setRecordingDeps(v_env_760_, v___x_761_);
v___x_763_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_764_ = lean_st_ref_get(v___y_757_);
v_scopes_765_ = lean_ctor_get(v___x_764_, 2);
lean_inc(v_scopes_765_);
lean_dec(v___x_764_);
v___x_766_ = l_List_head_x21___redArg(v___x_763_, v_scopes_765_);
lean_dec(v_scopes_765_);
v_opts_767_ = lean_ctor_get(v___x_766_, 1);
lean_inc_ref(v_opts_767_);
lean_dec(v___x_766_);
v___x_768_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_769_ = lean_unsigned_to_nat(32u);
v___x_770_ = lean_mk_empty_array_with_capacity(v___x_769_);
lean_dec_ref(v___x_770_);
v___x_771_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
v___x_772_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_772_, 0, v_env_762_);
lean_ctor_set(v___x_772_, 1, v___x_768_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
lean_ctor_set(v___x_772_, 3, v_opts_767_);
v___x_773_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_msgData_756_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_756_ = stack[0].m_obj;
lean_object* v___y_757_ = stack[1].m_obj;
lean_object* v_res_775_;
v_res_775_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_756_, v___y_757_);
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_776_, v___y_777_);
lean_dec(v___y_777_);
return v_res_779_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(1);
v___x_781_ = l_Lean_MessageData_ofFormat(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2));
v___x_786_ = l_Lean_MessageData_ofFormat(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(lean_object* v_x_787_, lean_object* v_x_788_){
_start:
{
if (lean_obj_tag(v_x_788_) == 0)
{
return v_x_787_;
}
else
{
lean_object* v_head_789_; lean_object* v_tail_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_812_; 
v_head_789_ = lean_ctor_get(v_x_788_, 0);
v_tail_790_ = lean_ctor_get(v_x_788_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_788_);
if (v_isSharedCheck_812_ == 0)
{
v___x_792_ = v_x_788_;
v_isShared_793_ = v_isSharedCheck_812_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_tail_790_);
lean_inc(v_head_789_);
lean_dec(v_x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_812_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_before_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_810_; 
v_before_794_ = lean_ctor_get(v_head_789_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_head_789_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_head_789_, 1);
lean_dec(v_unused_811_);
v___x_796_ = v_head_789_;
v_isShared_797_ = v_isSharedCheck_810_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_before_794_);
lean_dec(v_head_789_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_810_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_797_ == 0)
{
lean_ctor_set_tag(v___x_796_, 7);
lean_ctor_set(v___x_796_, 1, v___x_798_);
lean_ctor_set(v___x_796_, 0, v_x_787_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_x_787_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_809_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 7);
lean_ctor_set(v___x_792_, 1, v___x_801_);
lean_ctor_set(v___x_792_, 0, v___x_800_);
v___x_803_ = v___x_792_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v___x_801_);
v___x_803_ = v_reuseFailAlloc_808_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = l_Lean_MessageData_ofSyntax(v_before_794_);
v___x_805_ = l_Lean_indentD(v___x_804_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_803_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v_x_787_ = v___x_806_;
v_x_788_ = v_tail_790_;
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
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1));
v___x_817_ = l_Lean_MessageData_ofFormat(v___x_816_);
return v___x_817_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(lean_object* v_msgData_818_, lean_object* v_macroStack_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_scopes_824_; lean_object* v___x_825_; lean_object* v_opts_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_822_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_823_ = lean_st_ref_get(v___y_820_);
v_scopes_824_ = lean_ctor_get(v___x_823_, 2);
lean_inc(v_scopes_824_);
lean_dec(v___x_823_);
v___x_825_ = l_List_head_x21___redArg(v___x_822_, v_scopes_824_);
lean_dec(v_scopes_824_);
v_opts_826_ = lean_ctor_get(v___x_825_, 1);
lean_inc_ref(v_opts_826_);
lean_dec(v___x_825_);
v___x_827_ = l_Lean_Elab_pp_macroStack;
v___x_828_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_826_, v___x_827_);
lean_dec_ref(v_opts_826_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v_macroStack_819_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v_msgData_818_);
return v___x_829_;
}
else
{
if (lean_obj_tag(v_macroStack_819_) == 0)
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_msgData_818_);
return v___x_830_;
}
else
{
lean_object* v_head_831_; lean_object* v_after_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_847_; 
v_head_831_ = lean_ctor_get(v_macroStack_819_, 0);
lean_inc(v_head_831_);
v_after_832_ = lean_ctor_get(v_head_831_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v_head_831_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v_head_831_, 0);
lean_dec(v_unused_848_);
v___x_834_ = v_head_831_;
v_isShared_835_ = v_isSharedCheck_847_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_after_832_);
lean_dec(v_head_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_847_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 7);
lean_ctor_set(v___x_834_, 1, v___x_836_);
lean_ctor_set(v___x_834_, 0, v_msgData_818_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_msgData_818_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_836_);
v___x_838_ = v_reuseFailAlloc_846_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v_msgData_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_839_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = l_Lean_MessageData_ofSyntax(v_after_832_);
v___x_842_ = l_Lean_indentD(v___x_841_);
v_msgData_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_843_, 0, v___x_840_);
lean_ctor_set(v_msgData_843_, 1, v___x_842_);
v___x_844_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(v_msgData_843_, v_macroStack_819_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_818_ = stack[0].m_obj;
lean_object* v_macroStack_819_ = stack[1].m_obj;
lean_object* v___y_820_ = stack[2].m_obj;
lean_object* v_res_849_;
v_res_849_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_818_, v_macroStack_819_, v___y_820_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v_msgData_850_, lean_object* v_macroStack_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_850_, v_macroStack_851_, v___y_852_);
lean_dec(v___y_852_);
return v_res_854_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(lean_object* v_msg_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Elab_Command_getRef___redArg(v___y_856_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v_macroStack_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_a_864_; lean_object* v___x_865_; lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_874_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v_macroStack_861_ = lean_ctor_get(v___y_856_, 4);
v___x_862_ = l_Lean_Elab_getBetterRef(v_a_860_, v_macroStack_861_);
lean_dec(v_a_860_);
v___x_863_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msg_855_, v___y_857_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
lean_inc(v_macroStack_861_);
v___x_865_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_a_864_, v_macroStack_861_, v___y_857_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_874_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_862_);
lean_ctor_set(v___x_870_, 1, v_a_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 1);
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_msg_855_);
v_a_875_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_859_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_859_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_855_ = stack[0].m_obj;
lean_object* v___y_856_ = stack[1].m_obj;
lean_object* v___y_857_ = stack[2].m_obj;
lean_object* v_res_883_;
v_res_883_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_855_, v___y_856_, v___y_857_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg___boxed(lean_object* v_msg_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
return v_res_888_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(lean_object* v_ref_889_, lean_object* v_msg_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Elab_Command_getRef___redArg(v___y_891_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v_fileName_896_; lean_object* v_fileMap_897_; lean_object* v_currRecDepth_898_; lean_object* v_cmdPos_899_; lean_object* v_macroStack_900_; lean_object* v_quotContext_x3f_901_; lean_object* v_currMacroScope_902_; lean_object* v_snap_x3f_903_; lean_object* v_cancelTk_x3f_904_; uint8_t v_suppressElabErrors_905_; lean_object* v_ref_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v_fileName_896_ = lean_ctor_get(v___y_891_, 0);
v_fileMap_897_ = lean_ctor_get(v___y_891_, 1);
v_currRecDepth_898_ = lean_ctor_get(v___y_891_, 2);
v_cmdPos_899_ = lean_ctor_get(v___y_891_, 3);
v_macroStack_900_ = lean_ctor_get(v___y_891_, 4);
v_quotContext_x3f_901_ = lean_ctor_get(v___y_891_, 5);
v_currMacroScope_902_ = lean_ctor_get(v___y_891_, 6);
v_snap_x3f_903_ = lean_ctor_get(v___y_891_, 8);
v_cancelTk_x3f_904_ = lean_ctor_get(v___y_891_, 9);
v_suppressElabErrors_905_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*10);
v_ref_906_ = l_Lean_replaceRef(v_ref_889_, v_a_895_);
lean_dec(v_a_895_);
lean_inc(v_cancelTk_x3f_904_);
lean_inc(v_snap_x3f_903_);
lean_inc(v_currMacroScope_902_);
lean_inc(v_quotContext_x3f_901_);
lean_inc(v_macroStack_900_);
lean_inc(v_cmdPos_899_);
lean_inc(v_currRecDepth_898_);
lean_inc_ref(v_fileMap_897_);
lean_inc_ref(v_fileName_896_);
v___x_907_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_907_, 0, v_fileName_896_);
lean_ctor_set(v___x_907_, 1, v_fileMap_897_);
lean_ctor_set(v___x_907_, 2, v_currRecDepth_898_);
lean_ctor_set(v___x_907_, 3, v_cmdPos_899_);
lean_ctor_set(v___x_907_, 4, v_macroStack_900_);
lean_ctor_set(v___x_907_, 5, v_quotContext_x3f_901_);
lean_ctor_set(v___x_907_, 6, v_currMacroScope_902_);
lean_ctor_set(v___x_907_, 7, v_ref_906_);
lean_ctor_set(v___x_907_, 8, v_snap_x3f_903_);
lean_ctor_set(v___x_907_, 9, v_cancelTk_x3f_904_);
lean_ctor_set_uint8(v___x_907_, sizeof(void*)*10, v_suppressElabErrors_905_);
v___x_908_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_890_, v___x_907_, v___y_892_);
lean_dec_ref_known(v___x_907_, 10);
return v___x_908_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_msg_890_);
v_a_909_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_894_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_894_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_889_ = stack[0].m_obj;
lean_object* v_msg_890_ = stack[1].m_obj;
lean_object* v___y_891_ = stack[2].m_obj;
lean_object* v___y_892_ = stack[3].m_obj;
lean_object* v_res_917_;
v_res_917_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_889_, v_msg_890_, v___y_891_, v___y_892_);
stack->m_obj
 = v_res_917_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg___boxed(lean_object* v_ref_918_, lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_918_, v_msg_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v_ref_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
if (lean_obj_tag(v_x_925_) == 0)
{
return v_x_924_;
}
else
{
lean_object* v_key_926_; lean_object* v_value_927_; lean_object* v_tail_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_951_; 
v_key_926_ = lean_ctor_get(v_x_925_, 0);
v_value_927_ = lean_ctor_get(v_x_925_, 1);
v_tail_928_ = lean_ctor_get(v_x_925_, 2);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x_925_);
if (v_isSharedCheck_951_ == 0)
{
v___x_930_ = v_x_925_;
v_isShared_931_ = v_isSharedCheck_951_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_tail_928_);
lean_inc(v_value_927_);
lean_inc(v_key_926_);
lean_dec(v_x_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_951_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; uint64_t v___x_933_; uint64_t v___x_934_; uint64_t v___x_935_; uint64_t v_fold_936_; uint64_t v___x_937_; uint64_t v___x_938_; uint64_t v___x_939_; size_t v___x_940_; size_t v___x_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_932_ = lean_array_get_size(v_x_924_);
v___x_933_ = l_Lean_Syntax_instHashableRange_hash(v_key_926_);
v___x_934_ = 32ULL;
v___x_935_ = lean_uint64_shift_right(v___x_933_, v___x_934_);
v_fold_936_ = lean_uint64_xor(v___x_933_, v___x_935_);
v___x_937_ = 16ULL;
v___x_938_ = lean_uint64_shift_right(v_fold_936_, v___x_937_);
v___x_939_ = lean_uint64_xor(v_fold_936_, v___x_938_);
v___x_940_ = lean_uint64_to_usize(v___x_939_);
v___x_941_ = lean_usize_of_nat(v___x_932_);
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_sub(v___x_941_, v___x_942_);
v___x_944_ = lean_usize_land(v___x_940_, v___x_943_);
v___x_945_ = lean_array_uget_borrowed(v_x_924_, v___x_944_);
lean_inc(v___x_945_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 2, v___x_945_);
v___x_947_ = v___x_930_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_key_926_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_value_927_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v___x_945_);
v___x_947_ = v_reuseFailAlloc_950_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; 
v___x_948_ = lean_array_uset(v_x_924_, v___x_944_, v___x_947_);
v_x_924_ = v___x_948_;
v_x_925_ = v_tail_928_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(lean_object* v_i_952_, lean_object* v_source_953_, lean_object* v_target_954_){
_start:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_array_get_size(v_source_953_);
v___x_956_ = lean_nat_dec_lt(v_i_952_, v___x_955_);
if (v___x_956_ == 0)
{
lean_dec_ref(v_source_953_);
lean_dec(v_i_952_);
return v_target_954_;
}
else
{
lean_object* v_es_957_; lean_object* v___x_958_; lean_object* v_source_959_; lean_object* v_target_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_es_957_ = lean_array_fget(v_source_953_, v_i_952_);
v___x_958_ = lean_box(0);
v_source_959_ = lean_array_fset(v_source_953_, v_i_952_, v___x_958_);
v_target_960_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_target_954_, v_es_957_);
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_add(v_i_952_, v___x_961_);
lean_dec(v_i_952_);
v_i_952_ = v___x_962_;
v_source_953_ = v_source_959_;
v_target_954_ = v_target_960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(lean_object* v_data_964_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_nbuckets_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_965_ = lean_array_get_size(v_data_964_);
v___x_966_ = lean_unsigned_to_nat(2u);
v_nbuckets_967_ = lean_nat_mul(v___x_965_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_box(0);
v___x_970_ = lean_mk_array(v_nbuckets_967_, v___x_969_);
v___x_971_ = lean_array_propagate_mark(v_data_964_, v___x_970_);
v___x_972_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v___x_968_, v_data_964_, v___x_971_);
return v___x_972_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object* v_a_973_, lean_object* v_x_974_){
_start:
{
if (lean_obj_tag(v_x_974_) == 0)
{
uint8_t v___x_975_; 
v___x_975_ = 0;
return v___x_975_;
}
else
{
lean_object* v_key_976_; lean_object* v_tail_977_; uint8_t v___x_978_; 
v_key_976_ = lean_ctor_get(v_x_974_, 0);
v_tail_977_ = lean_ctor_get(v_x_974_, 2);
v___x_978_ = l_Lean_Syntax_instBEqRange_beq(v_key_976_, v_a_973_);
if (v___x_978_ == 0)
{
v_x_974_ = v_tail_977_;
goto _start;
}
else
{
return v___x_978_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_973_ = stack[0].m_obj;
lean_object* v_x_974_ = stack[1].m_obj;
uint8_t v_res_980_;
v_res_980_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_973_, v_x_974_);
stack->m_num = v_res_980_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object* v_a_981_, lean_object* v_x_982_){
_start:
{
uint8_t v_res_983_; lean_object* v_r_984_; 
v_res_983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_981_, v_x_982_);
lean_dec(v_x_982_);
lean_dec_ref(v_a_981_);
v_r_984_ = lean_box(v_res_983_);
return v_r_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(lean_object* v_a_985_, lean_object* v_b_986_, lean_object* v_x_987_){
_start:
{
if (lean_obj_tag(v_x_987_) == 0)
{
lean_dec(v_b_986_);
lean_dec_ref(v_a_985_);
return v_x_987_;
}
else
{
lean_object* v_key_988_; lean_object* v_value_989_; lean_object* v_tail_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1002_; 
v_key_988_ = lean_ctor_get(v_x_987_, 0);
v_value_989_ = lean_ctor_get(v_x_987_, 1);
v_tail_990_ = lean_ctor_get(v_x_987_, 2);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_987_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_992_ = v_x_987_;
v_isShared_993_ = v_isSharedCheck_1002_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_tail_990_);
lean_inc(v_value_989_);
lean_inc(v_key_988_);
lean_dec(v_x_987_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1002_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___x_994_; 
v___x_994_ = l_Lean_Syntax_instBEqRange_beq(v_key_988_, v_a_985_);
if (v___x_994_ == 0)
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_985_, v_b_986_, v_tail_990_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 2, v___x_995_);
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_key_988_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_value_989_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
else
{
lean_object* v___x_1000_; 
lean_dec(v_value_989_);
lean_dec(v_key_988_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v_b_986_);
lean_ctor_set(v___x_992_, 0, v_a_985_);
v___x_1000_ = v___x_992_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_985_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_b_986_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_tail_990_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object* v_m_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_){
_start:
{
lean_object* v_size_1006_; lean_object* v_buckets_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1050_; 
v_size_1006_ = lean_ctor_get(v_m_1003_, 0);
v_buckets_1007_ = lean_ctor_get(v_m_1003_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_m_1003_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1009_ = v_m_1003_;
v_isShared_1010_ = v_isSharedCheck_1050_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_buckets_1007_);
lean_inc(v_size_1006_);
lean_dec(v_m_1003_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1050_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; uint64_t v___x_1012_; uint64_t v___x_1013_; uint64_t v___x_1014_; uint64_t v_fold_1015_; uint64_t v___x_1016_; uint64_t v___x_1017_; uint64_t v___x_1018_; size_t v___x_1019_; size_t v___x_1020_; size_t v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; lean_object* v_bkt_1024_; uint8_t v___x_1025_; 
v___x_1011_ = lean_array_get_size(v_buckets_1007_);
v___x_1012_ = l_Lean_Syntax_instHashableRange_hash(v_a_1004_);
v___x_1013_ = 32ULL;
v___x_1014_ = lean_uint64_shift_right(v___x_1012_, v___x_1013_);
v_fold_1015_ = lean_uint64_xor(v___x_1012_, v___x_1014_);
v___x_1016_ = 16ULL;
v___x_1017_ = lean_uint64_shift_right(v_fold_1015_, v___x_1016_);
v___x_1018_ = lean_uint64_xor(v_fold_1015_, v___x_1017_);
v___x_1019_ = lean_uint64_to_usize(v___x_1018_);
v___x_1020_ = lean_usize_of_nat(v___x_1011_);
v___x_1021_ = ((size_t)1ULL);
v___x_1022_ = lean_usize_sub(v___x_1020_, v___x_1021_);
v___x_1023_ = lean_usize_land(v___x_1019_, v___x_1022_);
v_bkt_1024_ = lean_array_uget_borrowed(v_buckets_1007_, v___x_1023_);
v___x_1025_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1004_, v_bkt_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v_size_x27_1027_; lean_object* v___x_1028_; lean_object* v_buckets_x27_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1026_ = lean_unsigned_to_nat(1u);
v_size_x27_1027_ = lean_nat_add(v_size_1006_, v___x_1026_);
lean_dec(v_size_1006_);
lean_inc(v_bkt_1024_);
v___x_1028_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1028_, 0, v_a_1004_);
lean_ctor_set(v___x_1028_, 1, v_b_1005_);
lean_ctor_set(v___x_1028_, 2, v_bkt_1024_);
v_buckets_x27_1029_ = lean_array_uset(v_buckets_1007_, v___x_1023_, v___x_1028_);
v___x_1030_ = lean_unsigned_to_nat(4u);
v___x_1031_ = lean_nat_mul(v_size_x27_1027_, v___x_1030_);
v___x_1032_ = lean_unsigned_to_nat(3u);
v___x_1033_ = lean_nat_div(v___x_1031_, v___x_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_array_get_size(v_buckets_x27_1029_);
v___x_1035_ = lean_nat_dec_le(v___x_1033_, v___x_1034_);
lean_dec(v___x_1033_);
if (v___x_1035_ == 0)
{
lean_object* v_val_1036_; lean_object* v___x_1038_; 
v_val_1036_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_buckets_x27_1029_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v_val_1036_);
lean_ctor_set(v___x_1009_, 0, v_size_x27_1027_);
v___x_1038_ = v___x_1009_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_size_x27_1027_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_val_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v___x_1041_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v_buckets_x27_1029_);
lean_ctor_set(v___x_1009_, 0, v_size_x27_1027_);
v___x_1041_ = v___x_1009_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_size_x27_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_buckets_x27_1029_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v___x_1043_; lean_object* v_buckets_x27_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
lean_inc(v_bkt_1024_);
v___x_1043_ = lean_box(0);
v_buckets_x27_1044_ = lean_array_uset(v_buckets_1007_, v___x_1023_, v___x_1043_);
v___x_1045_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1004_, v_b_1005_, v_bkt_1024_);
v___x_1046_ = lean_array_uset(v_buckets_x27_1044_, v___x_1023_, v___x_1045_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1046_);
v___x_1048_ = v___x_1009_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_size_1006_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(lean_object* v___x_1071_, lean_object* v_val_1072_, uint8_t v___x_1073_, lean_object* v_ci_1074_, lean_object* v_info_1075_, lean_object* v_x_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
if (lean_obj_tag(v_info_1075_) == 10)
{
lean_object* v_i_1080_; lean_object* v_stx_1081_; lean_object* v_value_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1176_; 
v_i_1080_ = lean_ctor_get(v_info_1075_, 0);
lean_inc_ref(v_i_1080_);
v_stx_1081_ = lean_ctor_get(v_i_1080_, 0);
v_value_1082_ = lean_ctor_get(v_i_1080_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_i_1080_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1084_ = v_i_1080_;
v_isShared_1085_ = v_isSharedCheck_1176_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_value_1082_);
lean_inc(v_stx_1081_);
lean_dec(v_i_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1176_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; 
v___x_1086_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_1082_, v___x_1071_);
lean_dec(v_value_1082_);
if (lean_obj_tag(v___x_1086_) == 1)
{
lean_object* v_val_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1166_; 
v_val_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1166_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_val_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1166_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_Elab_Info_range_x3f(v_info_1075_);
if (lean_obj_tag(v___x_1091_) == 1)
{
lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1161_; 
v_val_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1161_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1161_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_maskAcc_1097_; lean_object* v___y_1108_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6));
lean_inc(v_stx_1081_);
v___x_1149_ = l_Lean_Syntax_isOfKind(v_stx_1081_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8));
lean_inc(v_stx_1081_);
v___x_1151_ = l_Lean_Syntax_isOfKind(v_stx_1081_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
lean_del_object(v___x_1094_);
lean_dec(v_val_1092_);
lean_del_object(v___x_1089_);
lean_dec(v_val_1087_);
lean_del_object(v___x_1084_);
lean_dec(v_stx_1081_);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_info_1075_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v_info_1075_, 0);
lean_dec(v_unused_1160_);
v___x_1153_ = v_info_1075_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_dec(v_info_1075_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 0);
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
goto v___jp_1112_;
}
}
else
{
goto v___jp_1112_;
}
v___jp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1098_ = lean_st_ref_take(v_val_1072_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v_maskAcc_1097_);
v___x_1100_ = v___x_1084_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_stx_1081_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_maskAcc_1097_);
v___x_1100_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_1098_, v_val_1092_, v___x_1100_);
v___x_1102_ = lean_st_ref_put(v_val_1072_, v___x_1101_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1102_);
v___x_1104_ = v___x_1094_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0));
v___x_1111_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_1073_, v_val_1087_, v___y_1108_, v___x_1109_, v___x_1110_);
lean_dec_ref(v___y_1108_);
lean_dec(v_val_1087_);
v_maskAcc_1097_ = v___x_1111_;
goto v___jp_1096_;
}
v___jp_1112_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_st_ref_get(v_val_1072_);
v___x_1114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_1113_, v_val_1092_);
lean_dec(v___x_1113_);
if (lean_obj_tag(v___x_1114_) == 1)
{
lean_object* v_val_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1147_; 
v_val_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1147_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_val_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1147_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_snd_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1145_; 
v_snd_1119_ = lean_ctor_get(v_val_1115_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_val_1115_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v_val_1115_, 0);
lean_dec(v_unused_1146_);
v___x_1121_ = v_val_1115_;
v_isShared_1122_ = v_isSharedCheck_1145_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_snd_1119_);
lean_dec(v_val_1115_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1145_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1123_ = lean_array_get_size(v_val_1087_);
v___x_1124_ = lean_array_get_size(v_snd_1119_);
v___x_1125_ = lean_nat_dec_eq(v___x_1123_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1126_ = l_Lean_Elab_Info_stx(v_info_1075_);
lean_dec_ref_known(v_info_1075_, 1);
v___x_1127_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2);
v___x_1128_ = l_Nat_reprFast(v___x_1124_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 3);
lean_ctor_set(v___x_1117_, 0, v___x_1128_);
v___x_1130_ = v___x_1117_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = l_Lean_MessageData_ofFormat(v___x_1130_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set_tag(v___x_1121_, 7);
lean_ctor_set(v___x_1121_, 1, v___x_1131_);
lean_ctor_set(v___x_1121_, 0, v___x_1127_);
v___x_1133_ = v___x_1121_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1134_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Nat_reprFast(v___x_1123_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 3);
lean_ctor_set(v___x_1089_, 0, v___x_1136_);
v___x_1138_ = v___x_1089_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = l_Lean_MessageData_ofFormat(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1135_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v___x_1126_, v___x_1140_, v___y_1077_, v___y_1078_);
lean_dec(v___x_1126_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_dec_ref_known(v___x_1141_, 1);
v___y_1108_ = v_snd_1119_;
goto v___jp_1107_;
}
else
{
lean_dec(v_snd_1119_);
lean_del_object(v___x_1094_);
lean_dec(v_val_1092_);
lean_dec(v_val_1087_);
lean_del_object(v___x_1084_);
lean_dec(v_stx_1081_);
return v___x_1141_;
}
}
}
}
}
else
{
lean_del_object(v___x_1121_);
lean_del_object(v___x_1117_);
lean_del_object(v___x_1089_);
lean_dec_ref_known(v_info_1075_, 1);
v___y_1108_ = v_snd_1119_;
goto v___jp_1107_;
}
}
}
}
else
{
lean_dec(v___x_1114_);
lean_del_object(v___x_1089_);
lean_dec_ref_known(v_info_1075_, 1);
v_maskAcc_1097_ = v_val_1087_;
goto v___jp_1096_;
}
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
lean_dec(v___x_1091_);
lean_dec(v_val_1087_);
lean_del_object(v___x_1084_);
lean_dec(v_stx_1081_);
lean_dec_ref_known(v_info_1075_, 1);
v___x_1162_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1162_);
v___x_1164_ = v___x_1089_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v___x_1086_);
lean_del_object(v___x_1084_);
lean_dec(v_stx_1081_);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_info_1075_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_info_1075_, 0);
lean_dec(v_unused_1175_);
v___x_1168_ = v_info_1075_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_dec(v_info_1075_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1170_ = lean_box(0);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_info_1075_);
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1071_ = stack[0].m_obj;
lean_object* v_val_1072_ = stack[1].m_obj;
uint8_t v___x_1073_ = stack[2].m_num;
lean_object* v_ci_1074_ = stack[3].m_obj;
lean_object* v_info_1075_ = stack[4].m_obj;
lean_object* v_x_1076_ = stack[5].m_obj;
lean_object* v___y_1077_ = stack[6].m_obj;
lean_object* v___y_1078_ = stack[7].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v___x_1071_, v_val_1072_, v___x_1073_, v_ci_1074_, v_info_1075_, v_x_1076_, v___y_1077_, v___y_1078_);
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(lean_object* v___x_1180_, lean_object* v_val_1181_, lean_object* v___x_1182_, lean_object* v_ci_1183_, lean_object* v_info_1184_, lean_object* v_x_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v___x_13846__boxed_1189_; lean_object* v_res_1190_; 
v___x_13846__boxed_1189_ = lean_unbox(v___x_1182_);
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v___x_1180_, v_val_1181_, v___x_13846__boxed_1189_, v_ci_1183_, v_info_1184_, v_x_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_x_1185_);
lean_dec_ref(v_ci_1183_);
lean_dec(v_val_1181_);
lean_dec(v___x_1180_);
return v_res_1190_;
}
}
lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(lean_object* v_postNode_1191_, lean_object* v_ci_1192_, lean_object* v_i_1193_, lean_object* v_cs_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
lean_inc(v___y_1197_);
lean_inc_ref(v___y_1196_);
v___x_1199_ = lean_apply_6(v_postNode_1191_, v_ci_1192_, v_i_1193_, v_cs_1194_, v___y_1196_, v___y_1197_, lean_box(0));
return v___x_1199_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_postNode_1191_ = stack[0].m_obj;
lean_object* v_ci_1192_ = stack[1].m_obj;
lean_object* v_i_1193_ = stack[2].m_obj;
lean_object* v_cs_1194_ = stack[3].m_obj;
lean_object* v_x_1195_ = stack[4].m_obj;
lean_object* v___y_1196_ = stack[5].m_obj;
lean_object* v___y_1197_ = stack[6].m_obj;
lean_object* v_res_1200_;
v_res_1200_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(v_postNode_1191_, v_ci_1192_, v_i_1193_, v_cs_1194_, v_x_1195_, v___y_1196_, v___y_1197_);
stack->m_obj
 = v_res_1200_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(lean_object* v_postNode_1201_, lean_object* v_ci_1202_, lean_object* v_i_1203_, lean_object* v_cs_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(v_postNode_1201_, v_ci_1202_, v_i_1203_, v_cs_1204_, v_x_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v_x_1205_);
return v_res_1209_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_instMonadEIO___redArg();
return v___x_1210_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(lean_object* v_msg_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_toApplicative_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1250_; 
v___x_1217_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0);
v___x_1218_ = l_StateRefT_x27_instMonad___redArg(v___x_1217_);
v_toApplicative_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1218_, 1);
lean_dec(v_unused_1251_);
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1250_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_toApplicative_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1250_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_toFunctor_1223_; lean_object* v_toSeq_1224_; lean_object* v_toSeqLeft_1225_; lean_object* v_toSeqRight_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1248_; 
v_toFunctor_1223_ = lean_ctor_get(v_toApplicative_1219_, 0);
v_toSeq_1224_ = lean_ctor_get(v_toApplicative_1219_, 2);
v_toSeqLeft_1225_ = lean_ctor_get(v_toApplicative_1219_, 3);
v_toSeqRight_1226_ = lean_ctor_get(v_toApplicative_1219_, 4);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_toApplicative_1219_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v_toApplicative_1219_, 1);
lean_dec(v_unused_1249_);
v___x_1228_ = v_toApplicative_1219_;
v_isShared_1229_ = v_isSharedCheck_1248_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_toSeqRight_1226_);
lean_inc(v_toSeqLeft_1225_);
lean_inc(v_toSeq_1224_);
lean_inc(v_toFunctor_1223_);
lean_dec(v_toApplicative_1219_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1248_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___x_1239_; 
v___f_1230_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1));
v___f_1231_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2));
lean_inc_ref(v_toFunctor_1223_);
v___f_1232_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1232_, 0, v_toFunctor_1223_);
v___f_1233_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1233_, 0, v_toFunctor_1223_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___f_1232_);
lean_ctor_set(v___x_1234_, 1, v___f_1233_);
v___f_1235_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1235_, 0, v_toSeqRight_1226_);
v___f_1236_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1236_, 0, v_toSeqLeft_1225_);
v___f_1237_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1237_, 0, v_toSeq_1224_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 4, v___f_1235_);
lean_ctor_set(v___x_1228_, 3, v___f_1236_);
lean_ctor_set(v___x_1228_, 2, v___f_1237_);
lean_ctor_set(v___x_1228_, 1, v___f_1230_);
lean_ctor_set(v___x_1228_, 0, v___x_1234_);
v___x_1239_ = v___x_1228_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___f_1230_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v___f_1237_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v___f_1236_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v___f_1235_);
v___x_1239_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1241_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___f_1231_);
lean_ctor_set(v___x_1221_, 0, v___x_1239_);
v___x_1241_ = v___x_1221_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___f_1231_);
v___x_1241_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_11903__overap_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_box(0);
v___x_1243_ = l_instInhabitedOfMonad___redArg(v___x_1241_, v___x_1242_);
v___x_11903__overap_1244_ = lean_panic_fn_borrowed(v___x_1243_, v_msg_1213_);
lean_dec(v___x_1243_);
lean_inc(v___y_1215_);
lean_inc_ref(v___y_1214_);
v___x_1245_ = lean_apply_3(v___x_11903__overap_1244_, v___y_1214_, v___y_1215_, lean_box(0));
return v___x_1245_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1213_ = stack[0].m_obj;
lean_object* v___y_1214_ = stack[1].m_obj;
lean_object* v___y_1215_ = stack[2].m_obj;
lean_object* v_res_1252_;
v_res_1252_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1213_, v___y_1214_, v___y_1215_);
stack->m_obj
 = v_res_1252_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(lean_object* v_msg_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1257_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2));
v___x_1262_ = lean_unsigned_to_nat(21u);
v___x_1263_ = lean_unsigned_to_nat(65u);
v___x_1264_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1));
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0));
v___x_1266_ = l_mkPanicMessageWithDecl(v___x_1265_, v___x_1264_, v___x_1263_, v___x_1262_, v___x_1261_);
return v___x_1266_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(lean_object* v_preNode_1267_, lean_object* v_postNode_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
switch(lean_obj_tag(v_x_1270_))
{
case 0:
{
lean_object* v_i_1274_; lean_object* v_t_1275_; lean_object* v___x_1276_; 
v_i_1274_ = lean_ctor_get(v_x_1270_, 0);
lean_inc_ref(v_i_1274_);
v_t_1275_ = lean_ctor_get(v_x_1270_, 1);
lean_inc_ref(v_t_1275_);
lean_dec_ref_known(v_x_1270_, 2);
v___x_1276_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1274_, v_x_1269_);
v_x_1269_ = v___x_1276_;
v_x_1270_ = v_t_1275_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1269_) == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref_known(v_x_1270_, 2);
lean_dec_ref(v_postNode_1268_);
lean_dec_ref(v_preNode_1267_);
v___x_1278_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3);
v___x_1279_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v___x_1278_, v___y_1271_, v___y_1272_);
return v___x_1279_;
}
else
{
lean_object* v_i_1280_; lean_object* v_children_1281_; lean_object* v_val_1282_; lean_object* v___x_1283_; 
v_i_1280_ = lean_ctor_get(v_x_1270_, 0);
lean_inc_ref_n(v_i_1280_, 2);
v_children_1281_ = lean_ctor_get(v_x_1270_, 1);
lean_inc_ref_n(v_children_1281_, 2);
lean_dec_ref_known(v_x_1270_, 2);
v_val_1282_ = lean_ctor_get(v_x_1269_, 0);
lean_inc_n(v_val_1282_, 2);
lean_inc_ref(v_preNode_1267_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
v___x_1283_ = lean_apply_6(v_preNode_1267_, v_val_1282_, v_i_1280_, v_children_1281_, v___y_1271_, v___y_1272_, lean_box(0));
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; uint8_t v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = lean_unbox(v_a_1284_);
lean_dec(v_a_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v_preNode_1267_);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_x_1269_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; 
v_unused_1311_ = lean_ctor_get(v_x_1269_, 0);
lean_dec(v_unused_1311_);
v___x_1287_ = v_x_1269_;
v_isShared_1288_ = v_isSharedCheck_1310_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v_x_1269_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1310_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_box(0);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
v___x_1290_ = lean_apply_7(v_postNode_1268_, v_val_1282_, v_i_1280_, v_children_1281_, v___x_1289_, v___y_1271_, v___y_1272_, lean_box(0));
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1301_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1301_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1301_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_a_1291_);
v___x_1296_ = v___x_1287_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1298_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1296_);
v___x_1298_ = v___x_1293_;
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
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_del_object(v___x_1287_);
v_a_1302_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1290_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1290_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1269_, v_i_1280_);
v___x_1313_ = l_Lean_PersistentArray_toList___redArg(v_children_1281_);
v___x_1314_ = lean_box(0);
lean_inc_ref(v_postNode_1268_);
v___x_1315_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1267_, v_postNode_1268_, v___x_1312_, v___x_1313_, v___x_1314_, v___y_1271_, v___y_1272_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1317_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
v___x_1317_ = lean_apply_7(v_postNode_1268_, v_val_1282_, v_i_1280_, v_children_1281_, v_a_1316_, v___y_1271_, v___y_1272_, lean_box(0));
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1326_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1326_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_a_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1322_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_a_1327_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1317_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1317_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v_val_1282_);
lean_dec_ref(v_children_1281_);
lean_dec_ref(v_i_1280_);
lean_dec_ref(v_postNode_1268_);
v_a_1335_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1315_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1315_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_val_1282_);
lean_dec_ref(v_children_1281_);
lean_dec_ref_known(v_x_1269_, 1);
lean_dec_ref(v_i_1280_);
lean_dec_ref(v_postNode_1268_);
lean_dec_ref(v_preNode_1267_);
v_a_1343_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1283_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1283_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
default: 
{
lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1358_; 
lean_dec(v_x_1269_);
lean_dec_ref(v_postNode_1268_);
lean_dec_ref(v_preNode_1267_);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_x_1270_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v_x_1270_, 0);
lean_dec(v_unused_1359_);
v___x_1352_ = v_x_1270_;
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
else
{
lean_dec(v_x_1270_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1358_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_box(0);
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1356_ = v___x_1352_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1267_ = stack[0].m_obj;
lean_object* v_postNode_1268_ = stack[1].m_obj;
lean_object* v_x_1269_ = stack[2].m_obj;
lean_object* v_x_1270_ = stack[3].m_obj;
lean_object* v___y_1271_ = stack[4].m_obj;
lean_object* v___y_1272_ = stack[5].m_obj;
lean_object* v_res_1360_;
v_res_1360_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1267_, v_postNode_1268_, v_x_1269_, v_x_1270_, v___y_1271_, v___y_1272_);
stack->m_obj
 = v_res_1360_;
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(lean_object* v_preNode_1361_, lean_object* v_postNode_1362_, lean_object* v___x_1363_, lean_object* v_x_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
if (lean_obj_tag(v_x_1364_) == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v___x_1363_);
lean_dec_ref(v_postNode_1362_);
lean_dec_ref(v_preNode_1361_);
v___x_1369_ = l_List_reverse___redArg(v_x_1365_);
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
else
{
lean_object* v_head_1371_; lean_object* v_tail_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1390_; 
v_head_1371_ = lean_ctor_get(v_x_1364_, 0);
v_tail_1372_ = lean_ctor_get(v_x_1364_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1374_ = v_x_1364_;
v_isShared_1375_ = v_isSharedCheck_1390_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_tail_1372_);
lean_inc(v_head_1371_);
lean_dec(v_x_1364_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1390_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; 
lean_inc(v___x_1363_);
lean_inc_ref(v_postNode_1362_);
lean_inc_ref(v_preNode_1361_);
v___x_1376_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1361_, v_postNode_1362_, v___x_1363_, v_head_1371_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 1, v_x_1365_);
lean_ctor_set(v___x_1374_, 0, v_a_1377_);
v___x_1379_ = v___x_1374_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1377_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_x_1365_);
v___x_1379_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
v_x_1364_ = v_tail_1372_;
v_x_1365_ = v___x_1379_;
goto _start;
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_del_object(v___x_1374_);
lean_dec(v_tail_1372_);
lean_dec(v_x_1365_);
lean_dec(v___x_1363_);
lean_dec_ref(v_postNode_1362_);
lean_dec_ref(v_preNode_1361_);
v_a_1382_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1376_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1376_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1361_ = stack[0].m_obj;
lean_object* v_postNode_1362_ = stack[1].m_obj;
lean_object* v___x_1363_ = stack[2].m_obj;
lean_object* v_x_1364_ = stack[3].m_obj;
lean_object* v_x_1365_ = stack[4].m_obj;
lean_object* v___y_1366_ = stack[5].m_obj;
lean_object* v___y_1367_ = stack[6].m_obj;
lean_object* v_res_1391_;
v_res_1391_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1361_, v_postNode_1362_, v___x_1363_, v_x_1364_, v_x_1365_, v___y_1366_, v___y_1367_);
stack->m_obj
 = v_res_1391_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(lean_object* v_preNode_1392_, lean_object* v_postNode_1393_, lean_object* v___x_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1392_, v_postNode_1393_, v___x_1394_, v_x_1395_, v_x_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(lean_object* v_preNode_1401_, lean_object* v_postNode_1402_, lean_object* v_x_1403_, lean_object* v_x_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1401_, v_postNode_1402_, v_x_1403_, v_x_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1408_;
}
}
lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object* v_preNode_1409_, lean_object* v_postNode_1410_, lean_object* v_ctx_x3f_1411_, lean_object* v_t_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___f_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___f_1416_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1416_, 0, v_postNode_1410_);
v___x_1417_ = lean_box(0);
v___x_1418_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1409_, v___f_1416_, v_ctx_x3f_1411_, v_t_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1418_, 0);
lean_dec(v_unused_1426_);
v___x_1420_ = v___x_1418_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_dec(v___x_1418_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1417_);
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1417_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1427_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1418_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1418_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1409_ = stack[0].m_obj;
lean_object* v_postNode_1410_ = stack[1].m_obj;
lean_object* v_ctx_x3f_1411_ = stack[2].m_obj;
lean_object* v_t_1412_ = stack[3].m_obj;
lean_object* v___y_1413_ = stack[4].m_obj;
lean_object* v___y_1414_ = stack[5].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v_preNode_1409_, v_postNode_1410_, v_ctx_x3f_1411_, v_t_1412_, v___y_1413_, v___y_1414_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object* v_preNode_1436_, lean_object* v_postNode_1437_, lean_object* v_ctx_x3f_1438_, lean_object* v_t_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v_preNode_1436_, v_postNode_1437_, v_ctx_x3f_1438_, v_t_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
return v_res_1443_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(uint8_t v___x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_box(v___x_1444_);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1444_ = stack[0].m_num;
lean_object* v_x_1445_ = stack[1].m_obj;
lean_object* v_x_1446_ = stack[2].m_obj;
lean_object* v_x_1447_ = stack[3].m_obj;
lean_object* v___y_1448_ = stack[4].m_obj;
lean_object* v___y_1449_ = stack[5].m_obj;
lean_object* v_res_1453_;
v_res_1453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v___x_1444_, v_x_1445_, v_x_1446_, v_x_1447_, v___y_1448_, v___y_1449_);
stack->m_obj
 = v_res_1453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object* v___x_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v___x_14836__boxed_1461_; lean_object* v_res_1462_; 
v___x_14836__boxed_1461_ = lean_unbox(v___x_1454_);
v_res_1462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v___x_14836__boxed_1461_, v_x_1455_, v_x_1456_, v_x_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec_ref(v_x_1457_);
lean_dec_ref(v_x_1456_);
lean_dec_ref(v_x_1455_);
return v_res_1462_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(uint8_t v___x_1463_, lean_object* v_val_1464_, lean_object* v_as_1465_, size_t v_sz_1466_, size_t v_i_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_usize_dec_lt(v_i_1467_, v_sz_1466_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec(v_val_1464_);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_b_1468_);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; lean_object* v___f_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___f_1478_; lean_object* v___x_1479_; lean_object* v_a_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1474_ = lean_box(v___x_1463_);
v___f_1475_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1475_, 0, v___x_1474_);
v___x_1476_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
v___x_1477_ = lean_box(v___x_1463_);
lean_inc(v_val_1464_);
v___f_1478_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1478_, 0, v___x_1476_);
lean_closure_set(v___f_1478_, 1, v_val_1464_);
lean_closure_set(v___f_1478_, 2, v___x_1477_);
v___x_1479_ = lean_box(0);
v_a_1480_ = lean_array_uget_borrowed(v_as_1465_, v_i_1467_);
v___x_1481_ = lean_box(0);
lean_inc(v_a_1480_);
v___x_1482_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v___f_1475_, v___f_1478_, v___x_1481_, v_a_1480_, v___y_1469_, v___y_1470_);
if (lean_obj_tag(v___x_1482_) == 0)
{
size_t v___x_1483_; size_t v___x_1484_; 
lean_dec_ref_known(v___x_1482_, 1);
v___x_1483_ = ((size_t)1ULL);
v___x_1484_ = lean_usize_add(v_i_1467_, v___x_1483_);
v_i_1467_ = v___x_1484_;
v_b_1468_ = v___x_1479_;
goto _start;
}
else
{
lean_dec(v_val_1464_);
return v___x_1482_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1463_ = stack[0].m_num;
lean_object* v_val_1464_ = stack[1].m_obj;
lean_object* v_as_1465_ = stack[2].m_obj;
size_t v_sz_1466_ = stack[3].m_num;
size_t v_i_1467_ = stack[4].m_num;
lean_object* v_b_1468_ = stack[5].m_obj;
lean_object* v___y_1469_ = stack[6].m_obj;
lean_object* v___y_1470_ = stack[7].m_obj;
lean_object* v_res_1486_;
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_1463_, v_val_1464_, v_as_1465_, v_sz_1466_, v_i_1467_, v_b_1468_, v___y_1469_, v___y_1470_);
stack->m_obj
 = v_res_1486_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object* v___x_1487_, lean_object* v_val_1488_, lean_object* v_as_1489_, lean_object* v_sz_1490_, lean_object* v_i_1491_, lean_object* v_b_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
uint8_t v___x_14877__boxed_1496_; size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v___x_14877__boxed_1496_ = lean_unbox(v___x_1487_);
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1490_);
lean_dec(v_sz_1490_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1491_);
lean_dec(v_i_1491_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_14877__boxed_1496_, v_val_1488_, v_as_1489_, v_sz_boxed_1497_, v_i_boxed_1498_, v_b_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec_ref(v_as_1489_);
return v_res_1499_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_unsigned_to_nat(16u);
v___x_1502_ = lean_mk_array(v___x_1501_, v___x_1500_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__0, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v___x_1503_);
return v___x_1505_;
}
}
lean_object* l_Lean_Linter_unusedSimpArgs___lam__0(lean_object* v_cmdStx_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1577_; 
v___x_1510_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_1507_, v___y_1508_);
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1577_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1577_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_1516_ = l_Lean_Linter_getLinterValue(v___x_1515_, v_a_1511_);
lean_dec(v_a_1511_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_box(0);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1517_);
v___x_1519_ = v___x_1513_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
else
{
uint8_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = 0;
v___x_1522_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1506_, v___x_1521_);
if (lean_obj_tag(v___x_1522_) == 1)
{
lean_object* v___x_1523_; lean_object* v_infoState_1524_; lean_object* v_trees_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; size_t v_sz_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
lean_dec_ref_known(v___x_1522_, 1);
lean_del_object(v___x_1513_);
v___x_1523_ = lean_st_ref_get(v___y_1508_);
v_infoState_1524_ = lean_ctor_get(v___x_1523_, 8);
lean_inc_ref(v_infoState_1524_);
lean_dec(v___x_1523_);
v_trees_1525_ = lean_ctor_get(v_infoState_1524_, 2);
lean_inc_ref(v_trees_1525_);
lean_dec_ref(v_infoState_1524_);
v___x_1526_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1525_);
lean_dec_ref(v_trees_1525_);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__1, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1);
v___x_1529_ = lean_st_mk_ref(v___x_1528_);
v___x_1530_ = lean_box(0);
v_sz_1531_ = lean_array_size(v___x_1526_);
v___x_1532_ = ((size_t)0ULL);
lean_inc(v___x_1529_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_1516_, v___x_1529_, v___x_1526_, v_sz_1531_, v___x_1532_, v___x_1530_, v___y_1507_, v___y_1508_);
lean_dec_ref(v___x_1526_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v___x_1534_; lean_object* v___y_1536_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1560_; lean_object* v_size_1566_; lean_object* v_buckets_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
lean_dec_ref_known(v___x_1533_, 1);
v___x_1534_ = lean_st_ref_get(v___x_1529_);
lean_dec(v___x_1529_);
v_size_1566_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_size_1566_);
v_buckets_1567_ = lean_ctor_get(v___x_1534_, 1);
lean_inc_ref(v_buckets_1567_);
lean_dec(v___x_1534_);
v___x_1568_ = lean_mk_empty_array_with_capacity(v_size_1566_);
lean_dec(v_size_1566_);
v___x_1569_ = lean_array_get_size(v_buckets_1567_);
v___x_1570_ = lean_nat_dec_lt(v___x_1527_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_dec_ref(v_buckets_1567_);
v___y_1560_ = v___x_1568_;
goto v___jp_1559_;
}
else
{
size_t v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_usize_of_nat(v___x_1569_);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_1567_, v___x_1532_, v___x_1571_, v___x_1568_);
lean_dec_ref(v_buckets_1567_);
v___y_1560_ = v___x_1572_;
goto v___jp_1559_;
}
v___jp_1535_:
{
size_t v_sz_1537_; lean_object* v___x_1538_; 
v_sz_1537_ = lean_array_size(v___y_1536_);
v___x_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___y_1536_, v_sz_1537_, v___x_1532_, v___x_1530_, v___y_1507_, v___y_1508_);
lean_dec_ref(v___y_1536_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; 
v_unused_1546_ = lean_ctor_get(v___x_1538_, 0);
lean_dec(v_unused_1546_);
v___x_1540_ = v___x_1538_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v___x_1538_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1530_);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1530_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
else
{
return v___x_1538_;
}
}
v___jp_1547_:
{
lean_object* v___x_1552_; 
v___x_1552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v___y_1549_, v___y_1548_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec(v___y_1549_);
v___y_1536_ = v___x_1552_;
goto v___jp_1535_;
}
v___jp_1553_:
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_nat_dec_le(v___y_1557_, v___y_1554_);
if (v___x_1558_ == 0)
{
lean_dec(v___y_1554_);
lean_inc(v___y_1557_);
v___y_1548_ = v___y_1555_;
v___y_1549_ = v___y_1556_;
v___y_1550_ = v___y_1557_;
v___y_1551_ = v___y_1557_;
goto v___jp_1547_;
}
else
{
v___y_1548_ = v___y_1555_;
v___y_1549_ = v___y_1556_;
v___y_1550_ = v___y_1557_;
v___y_1551_ = v___y_1554_;
goto v___jp_1547_;
}
}
v___jp_1559_:
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = lean_array_get_size(v___y_1560_);
v___x_1562_ = lean_nat_dec_eq(v___x_1561_, v___x_1527_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_sub(v___x_1561_, v___x_1563_);
v___x_1565_ = lean_nat_dec_le(v___x_1527_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_inc(v___x_1564_);
v___y_1554_ = v___x_1564_;
v___y_1555_ = v___y_1560_;
v___y_1556_ = v___x_1561_;
v___y_1557_ = v___x_1564_;
goto v___jp_1553_;
}
else
{
v___y_1554_ = v___x_1564_;
v___y_1555_ = v___y_1560_;
v___y_1556_ = v___x_1561_;
v___y_1557_ = v___x_1527_;
goto v___jp_1553_;
}
}
else
{
v___y_1536_ = v___y_1560_;
goto v___jp_1535_;
}
}
}
else
{
lean_dec(v___x_1529_);
return v___x_1533_;
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_dec(v___x_1522_);
v___x_1573_ = lean_box(0);
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___x_1573_);
v___x_1575_ = v___x_1513_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_unusedSimpArgs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmdStx_1506_ = stack[0].m_obj;
lean_object* v___y_1507_ = stack[1].m_obj;
lean_object* v___y_1508_ = stack[2].m_obj;
lean_object* v_res_1578_;
v_res_1578_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_1506_, v___y_1507_, v___y_1508_);
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___boxed(lean_object* v_cmdStx_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v_cmdStx_1579_);
return v_res_1583_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(lean_object* v_o_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_1595_, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_1595_ = stack[0].m_obj;
lean_object* v___y_1596_ = stack[1].m_obj;
lean_object* v___y_1597_ = stack[2].m_obj;
lean_object* v_res_1600_;
v_res_1600_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_1595_, v___y_1596_, v___y_1597_);
stack->m_obj
 = v_res_1600_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(lean_object* v_o_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object* v_00_u03b2_1606_, lean_object* v_m_1607_, lean_object* v_a_1608_, lean_object* v_b_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_1607_, v_a_1608_, v_b_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object* v_00_u03b2_1611_, lean_object* v_m_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_1612_, v_a_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object* v_00_u03b2_1615_, lean_object* v_m_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(v_00_u03b2_1615_, v_m_1616_, v_a_1617_);
lean_dec_ref(v_a_1617_);
lean_dec_ref(v_m_1616_);
return v_res_1618_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(lean_object* v_00_u03b1_1619_, lean_object* v_ref_1620_, lean_object* v_msg_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_1620_, v_msg_1621_, v___y_1622_, v___y_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1620_ = stack[1].m_obj;
lean_object* v_msg_1621_ = stack[2].m_obj;
lean_object* v___y_1622_ = stack[3].m_obj;
lean_object* v___y_1623_ = stack[4].m_obj;
lean_object* v_res_1626_;
v_res_1626_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(lean_box(0), v_ref_1620_, v_msg_1621_, v___y_1622_, v___y_1623_);
stack->m_obj
 = v_res_1626_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object* v_00_u03b1_1627_, lean_object* v_ref_1628_, lean_object* v_msg_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(v_00_u03b1_1627_, v_ref_1628_, v_msg_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v_ref_1628_);
return v_res_1633_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object* v_upperBound_1634_, lean_object* v_snd_1635_, lean_object* v_fst_1636_, lean_object* v_inst_1637_, lean_object* v_R_1638_, lean_object* v_a_1639_, lean_object* v_b_1640_, lean_object* v_c_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_1634_, v_snd_1635_, v_fst_1636_, v_a_1639_, v_b_1640_, v___y_1642_, v___y_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1634_ = stack[0].m_obj;
lean_object* v_snd_1635_ = stack[1].m_obj;
lean_object* v_fst_1636_ = stack[2].m_obj;
lean_object* v_a_1639_ = stack[5].m_obj;
lean_object* v_b_1640_ = stack[6].m_obj;
lean_object* v___y_1642_ = stack[8].m_obj;
lean_object* v___y_1643_ = stack[9].m_obj;
lean_object* v_res_1646_;
v_res_1646_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(v_upperBound_1634_, v_snd_1635_, v_fst_1636_, lean_box(0), lean_box(0), v_a_1639_, v_b_1640_, lean_box(0), v___y_1642_, v___y_1643_);
stack->m_obj
 = v_res_1646_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object* v_upperBound_1647_, lean_object* v_snd_1648_, lean_object* v_fst_1649_, lean_object* v_inst_1650_, lean_object* v_R_1651_, lean_object* v_a_1652_, lean_object* v_b_1653_, lean_object* v_c_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(v_upperBound_1647_, v_snd_1648_, v_fst_1649_, v_inst_1650_, v_R_1651_, v_a_1652_, v_b_1653_, v_c_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v_snd_1648_);
lean_dec(v_upperBound_1647_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object* v_n_1659_, lean_object* v_as_1660_, lean_object* v_lo_1661_, lean_object* v_hi_1662_, lean_object* v_w_1663_, lean_object* v_hlo_1664_, lean_object* v_hhi_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_1659_, v_as_1660_, v_lo_1661_, v_hi_1662_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object* v_n_1667_, lean_object* v_as_1668_, lean_object* v_lo_1669_, lean_object* v_hi_1670_, lean_object* v_w_1671_, lean_object* v_hlo_1672_, lean_object* v_hhi_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(v_n_1667_, v_as_1668_, v_lo_1669_, v_hi_1670_, v_w_1671_, v_hlo_1672_, v_hhi_1673_);
lean_dec(v_hi_1670_);
lean_dec(v_n_1667_);
return v_res_1674_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object* v_00_u03b2_1675_, lean_object* v_a_1676_, lean_object* v_x_1677_){
_start:
{
uint8_t v___x_1678_; 
v___x_1678_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1676_, v_x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1676_ = stack[1].m_obj;
lean_object* v_x_1677_ = stack[2].m_obj;
uint8_t v_res_1679_;
v_res_1679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_box(0), v_a_1676_, v_x_1677_);
stack->m_num = v_res_1679_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1680_, lean_object* v_a_1681_, lean_object* v_x_1682_){
_start:
{
uint8_t v_res_1683_; lean_object* v_r_1684_; 
v_res_1683_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_1680_, v_a_1681_, v_x_1682_);
lean_dec(v_x_1682_);
lean_dec_ref(v_a_1681_);
v_r_1684_ = lean_box(v_res_1683_);
return v_r_1684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(lean_object* v_00_u03b2_1685_, lean_object* v_data_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_data_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(lean_object* v_00_u03b2_1688_, lean_object* v_a_1689_, lean_object* v_b_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1689_, v_b_1690_, v_x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(lean_object* v_00_u03b2_1693_, lean_object* v_a_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_1694_, v_x_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1697_, lean_object* v_a_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(v_00_u03b2_1697_, v_a_1698_, v_x_1699_);
lean_dec(v_x_1699_);
lean_dec_ref(v_a_1698_);
return v_res_1700_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(lean_object* v_msgData_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_1701_, v___y_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1701_ = stack[0].m_obj;
lean_object* v___y_1702_ = stack[1].m_obj;
lean_object* v___y_1703_ = stack[2].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_1701_, v___y_1702_, v___y_1703_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(lean_object* v_msgData_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1711_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(lean_object* v_00_u03b1_1712_, lean_object* v_msg_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_1713_, v___y_1714_, v___y_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1713_ = stack[1].m_obj;
lean_object* v___y_1714_ = stack[2].m_obj;
lean_object* v___y_1715_ = stack[3].m_obj;
lean_object* v_res_1718_;
v_res_1718_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(lean_box(0), v_msg_1713_, v___y_1714_, v___y_1715_);
stack->m_obj
 = v_res_1718_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_msg_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(v_00_u03b1_1719_, v_msg_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1724_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_object* v_00_u03b1_1725_, lean_object* v_msg_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1726_, v___y_1727_, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1726_ = stack[1].m_obj;
lean_object* v___y_1727_ = stack[2].m_obj;
lean_object* v___y_1728_ = stack[3].m_obj;
lean_object* v_res_1731_;
v_res_1731_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_box(0), v_msg_1726_, v___y_1727_, v___y_1728_);
stack->m_obj
 = v_res_1731_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1732_, lean_object* v_msg_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(v_00_u03b1_1732_, v_msg_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1737_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_object* v_00_u03b1_1738_, lean_object* v_preNode_1739_, lean_object* v_postNode_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1739_, v_postNode_1740_, v_x_1741_, v_x_1742_, v___y_1743_, v___y_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1739_ = stack[1].m_obj;
lean_object* v_postNode_1740_ = stack[2].m_obj;
lean_object* v_x_1741_ = stack[3].m_obj;
lean_object* v_x_1742_ = stack[4].m_obj;
lean_object* v___y_1743_ = stack[5].m_obj;
lean_object* v___y_1744_ = stack[6].m_obj;
lean_object* v_res_1747_;
v_res_1747_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_box(0), v_preNode_1739_, v_postNode_1740_, v_x_1741_, v_x_1742_, v___y_1743_, v___y_1744_);
stack->m_obj
 = v_res_1747_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_preNode_1749_, lean_object* v_postNode_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(v_00_u03b1_1748_, v_preNode_1749_, v_postNode_1750_, v_x_1751_, v_x_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(lean_object* v_n_1757_, lean_object* v_lo_1758_, lean_object* v_hi_1759_, lean_object* v_hhi_1760_, lean_object* v_pivot_1761_, lean_object* v_as_1762_, lean_object* v_i_1763_, lean_object* v_k_1764_, lean_object* v_ilo_1765_, lean_object* v_ik_1766_, lean_object* v_w_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_1759_, v_pivot_1761_, v_as_1762_, v_i_1763_, v_k_1764_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(lean_object* v_n_1769_, lean_object* v_lo_1770_, lean_object* v_hi_1771_, lean_object* v_hhi_1772_, lean_object* v_pivot_1773_, lean_object* v_as_1774_, lean_object* v_i_1775_, lean_object* v_k_1776_, lean_object* v_ilo_1777_, lean_object* v_ik_1778_, lean_object* v_w_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(v_n_1769_, v_lo_1770_, v_hi_1771_, v_hhi_1772_, v_pivot_1773_, v_as_1774_, v_i_1775_, v_k_1776_, v_ilo_1777_, v_ik_1778_, v_w_1779_);
lean_dec_ref(v_pivot_1773_);
lean_dec(v_hi_1771_);
lean_dec(v_lo_1770_);
lean_dec(v_n_1769_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1781_, lean_object* v_i_1782_, lean_object* v_source_1783_, lean_object* v_target_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v_i_1782_, v_source_1783_, v_target_1784_);
return v___x_1785_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(lean_object* v_msgData_1786_, lean_object* v_macroStack_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_1786_, v_macroStack_1787_, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1786_ = stack[0].m_obj;
lean_object* v_macroStack_1787_ = stack[1].m_obj;
lean_object* v___y_1788_ = stack[2].m_obj;
lean_object* v___y_1789_ = stack[3].m_obj;
lean_object* v_res_1792_;
v_res_1792_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_1786_, v_macroStack_1787_, v___y_1788_, v___y_1789_);
stack->m_obj
 = v_res_1792_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_1793_, lean_object* v_macroStack_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_1793_, v_macroStack_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1798_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_object* v_00_u03b1_1799_, lean_object* v_preNode_1800_, lean_object* v_postNode_1801_, lean_object* v___x_1802_, lean_object* v_x_1803_, lean_object* v_x_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1800_, v_postNode_1801_, v___x_1802_, v_x_1803_, v_x_1804_, v___y_1805_, v___y_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1800_ = stack[1].m_obj;
lean_object* v_postNode_1801_ = stack[2].m_obj;
lean_object* v___x_1802_ = stack[3].m_obj;
lean_object* v_x_1803_ = stack[4].m_obj;
lean_object* v_x_1804_ = stack[5].m_obj;
lean_object* v___y_1805_ = stack[6].m_obj;
lean_object* v___y_1806_ = stack[7].m_obj;
lean_object* v_res_1809_;
v_res_1809_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_box(0), v_preNode_1800_, v_postNode_1801_, v___x_1802_, v_x_1803_, v_x_1804_, v___y_1805_, v___y_1806_);
stack->m_obj
 = v_res_1809_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(lean_object* v_00_u03b1_1810_, lean_object* v_preNode_1811_, lean_object* v_postNode_1812_, lean_object* v___x_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(v_00_u03b1_1810_, v_preNode_1811_, v_postNode_1812_, v___x_1813_, v_x_1814_, v_x_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_x_1821_, v_x_1822_);
return v___x_1823_;
}
}
lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = ((lean_object*)(l_Lean_Linter_unusedSimpArgs));
v___x_1826_ = l_Lean_Elab_Command_addLinter(v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1827_;
v_res_1827_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1827_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
return v_res_1829_;
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
