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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* v___x_47_; lean_object* v_toCold_48_; lean_object* v_env_49_; lean_object* v_options_50_; uint8_t v___x_51_; lean_object* v_env_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_47_ = lean_st_ref_get(v___y_45_);
v_toCold_48_ = lean_ctor_get(v___y_44_, 0);
v_env_49_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_env_49_);
lean_dec(v___x_47_);
v_options_50_ = lean_ctor_get(v_toCold_48_, 2);
v___x_51_ = 0;
v_env_52_ = l_Lean_Environment_setRecordingDeps(v_env_49_, v___x_51_);
v___x_53_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_54_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_50_);
v___x_55_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_55_, 0, v_env_52_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_54_);
lean_ctor_set(v___x_55_, 3, v_options_50_);
v___x_56_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v_msgData_43_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___boxed(lean_object* v_msgData_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msgData_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(lean_object* v_msg_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_ref_67_; lean_object* v___x_68_; lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_77_; 
v_ref_67_ = lean_ctor_get(v___y_64_, 2);
v___x_68_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msg_63_, v___y_64_, v___y_65_);
v_a_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_77_ == 0)
{
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_77_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_77_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
lean_inc(v_ref_67_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_ref_67_);
lean_ctor_set(v___x_73_, 1, v_a_69_);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 1);
lean_ctor_set(v___x_71_, 0, v___x_73_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg___boxed(lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 1)
{
lean_object* v_pre_93_; 
v_pre_93_ = lean_ctor_get(v_x_92_, 0);
switch(lean_obj_tag(v_pre_93_))
{
case 1:
{
lean_object* v_pre_94_; 
v_pre_94_ = lean_ctor_get(v_pre_93_, 0);
switch(lean_obj_tag(v_pre_94_))
{
case 0:
{
lean_object* v_str_95_; lean_object* v_str_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_str_95_ = lean_ctor_get(v_x_92_, 1);
v_str_96_ = lean_ctor_get(v_pre_93_, 1);
v___x_97_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_98_ = lean_string_dec_eq(v_str_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_100_ = lean_string_dec_eq(v_str_96_, v___x_99_);
if (v___x_100_ == 0)
{
return v___x_100_;
}
else
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_102_ = lean_string_dec_eq(v_str_95_, v___x_101_);
if (v___x_102_ == 0)
{
return v___x_102_;
}
else
{
return v_suppressElabErrors_91_;
}
}
}
else
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_104_ = lean_string_dec_eq(v_str_95_, v___x_103_);
if (v___x_104_ == 0)
{
return v___x_104_;
}
else
{
return v_suppressElabErrors_91_;
}
}
}
case 1:
{
lean_object* v_pre_105_; 
v_pre_105_ = lean_ctor_get(v_pre_94_, 0);
if (lean_obj_tag(v_pre_105_) == 0)
{
lean_object* v_str_106_; lean_object* v_str_107_; lean_object* v_str_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_str_106_ = lean_ctor_get(v_x_92_, 1);
v_str_107_ = lean_ctor_get(v_pre_93_, 1);
v_str_108_ = lean_ctor_get(v_pre_94_, 1);
v___x_109_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_110_ = lean_string_dec_eq(v_str_108_, v___x_109_);
if (v___x_110_ == 0)
{
return v___x_110_;
}
else
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_112_ = lean_string_dec_eq(v_str_107_, v___x_111_);
if (v___x_112_ == 0)
{
return v___x_112_;
}
else
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_114_ = lean_string_dec_eq(v_str_106_, v___x_113_);
if (v___x_114_ == 0)
{
return v___x_114_;
}
else
{
return v_suppressElabErrors_91_;
}
}
}
}
else
{
uint8_t v___x_115_; 
v___x_115_ = 0;
return v___x_115_;
}
}
default: 
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
}
case 0:
{
lean_object* v_str_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_str_117_ = lean_ctor_get(v_x_92_, 1);
v___x_118_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_119_ = lean_string_dec_eq(v_str_117_, v___x_118_);
if (v___x_119_ == 0)
{
return v___x_119_;
}
else
{
return v_suppressElabErrors_91_;
}
}
default: 
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
}
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_122_, lean_object* v_x_123_){
_start:
{
uint8_t v_suppressElabErrors_boxed_124_; uint8_t v_res_125_; lean_object* v_r_126_; 
v_suppressElabErrors_boxed_124_ = lean_unbox(v_suppressElabErrors_122_);
v_res_125_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_124_, v_x_123_);
lean_dec(v_x_123_);
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
uint8_t v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; uint8_t v___y_156_; lean_object* v_toCold_157_; lean_object* v___y_158_; lean_object* v___y_187_; lean_object* v___y_188_; uint8_t v___y_189_; uint8_t v___y_190_; uint8_t v___y_191_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_214_; uint8_t v___y_215_; lean_object* v___y_216_; uint8_t v___y_217_; lean_object* v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; uint8_t v___y_224_; uint8_t v___y_225_; uint8_t v___x_235_; uint8_t v___y_237_; uint8_t v___x_243_; 
v___x_235_ = 2;
v___x_243_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_235_);
if (v___x_243_ == 0)
{
v___y_237_ = v___x_243_;
goto v___jp_236_;
}
else
{
uint8_t v___x_244_; 
lean_inc_ref(v_msgData_143_);
v___x_244_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_143_);
if (v___x_244_ == 0)
{
v___y_237_ = v___x_244_;
goto v___jp_236_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
lean_dec_ref(v_msgData_143_);
v___x_245_ = lean_box(0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
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
lean_ctor_set(v___x_162_, 1, v___y_153_);
lean_inc_ref(v___y_152_);
lean_inc_ref(v___y_151_);
v___x_163_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_163_, 0, v___y_151_);
lean_ctor_set(v___x_163_, 1, v___y_155_);
lean_ctor_set(v___x_163_, 2, v___y_154_);
lean_ctor_set(v___x_163_, 3, v___y_152_);
lean_ctor_set(v___x_163_, 4, v___x_162_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*5, v___y_150_);
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*5 + 1, v___y_156_);
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
v_fileName_195_ = lean_ctor_get(v___y_193_, 0);
v_fileMap_196_ = lean_ctor_get(v___y_193_, 1);
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
v___x_203_ = l_Lean_FileMap_toPosition(v_fileMap_196_, v___y_192_);
lean_dec(v___y_192_);
v___x_204_ = l_Lean_FileMap_toPosition(v_fileMap_196_, v___y_194_);
lean_dec(v___y_194_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
v___x_206_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0));
if (v___y_190_ == 0)
{
lean_del_object(v___x_201_);
lean_dec_ref(v___y_187_);
v___y_150_ = v___y_189_;
v___y_151_ = v_fileName_195_;
v___y_152_ = v___x_206_;
v___y_153_ = v_a_199_;
v___y_154_ = v___x_205_;
v___y_155_ = v___x_203_;
v___y_156_ = v___y_191_;
v_toCold_157_ = v___y_188_;
v___y_158_ = v___y_147_;
goto v___jp_149_;
}
else
{
uint8_t v___x_207_; 
lean_inc(v_a_199_);
v___x_207_ = l_Lean_MessageData_hasTag(v___y_187_, v_a_199_);
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
v___y_150_ = v___y_189_;
v___y_151_ = v_fileName_195_;
v___y_152_ = v___x_206_;
v___y_153_ = v_a_199_;
v___y_154_ = v___x_205_;
v___y_155_ = v___x_203_;
v___y_156_ = v___y_191_;
v_toCold_157_ = v___y_188_;
v___y_158_ = v___y_147_;
goto v___jp_149_;
}
}
}
}
v___jp_213_:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Syntax_getTailPos_x3f(v___y_218_, v___y_217_);
lean_dec(v___y_218_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_inc(v___y_220_);
v___y_187_ = v___y_214_;
v___y_188_ = v___y_216_;
v___y_189_ = v___y_217_;
v___y_190_ = v___y_215_;
v___y_191_ = v___y_219_;
v___y_192_ = v___y_220_;
v___y_193_ = v___y_216_;
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
v___y_188_ = v___y_216_;
v___y_189_ = v___y_217_;
v___y_190_ = v___y_215_;
v___y_191_ = v___y_219_;
v___y_192_ = v___y_220_;
v___y_193_ = v___y_216_;
v___y_194_ = v_val_222_;
goto v___jp_186_;
}
}
v___jp_223_:
{
lean_object* v_toCold_226_; lean_object* v_ref_227_; uint8_t v_suppressElabErrors_228_; lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v_ref_231_; lean_object* v___x_232_; 
v_toCold_226_ = lean_ctor_get(v___y_146_, 0);
v_ref_227_ = lean_ctor_get(v___y_146_, 2);
v_suppressElabErrors_228_ = lean_ctor_get_uint8(v___y_146_, sizeof(void*)*3 + 2);
v___x_229_ = lean_box(v_suppressElabErrors_228_);
v___f_230_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_230_, 0, v___x_229_);
v_ref_231_ = l_Lean_replaceRef(v_ref_142_, v_ref_227_);
v___x_232_ = l_Lean_Syntax_getPos_x3f(v_ref_231_, v___y_224_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___y_214_ = v___f_230_;
v___y_215_ = v_suppressElabErrors_228_;
v___y_216_ = v_toCold_226_;
v___y_217_ = v___y_224_;
v___y_218_ = v_ref_231_;
v___y_219_ = v___y_225_;
v___y_220_ = v___x_233_;
goto v___jp_213_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_232_, 1);
v___y_214_ = v___f_230_;
v___y_215_ = v_suppressElabErrors_228_;
v___y_216_ = v_toCold_226_;
v___y_217_ = v___y_224_;
v___y_218_ = v_ref_231_;
v___y_219_ = v___y_225_;
v___y_220_ = v_val_234_;
goto v___jp_213_;
}
}
v___jp_236_:
{
uint8_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 1;
v___x_239_ = l_Lean_instBEqMessageSeverity_beq(v_severity_144_, v___x_238_);
if (v___x_239_ == 0)
{
v___y_224_ = v___y_237_;
v___y_225_ = v_severity_144_;
goto v___jp_223_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_146_);
v___x_241_ = l_Lean_warningAsError;
v___x_242_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v___x_240_, v___x_241_);
lean_dec_ref(v___x_240_);
if (v___x_242_ == 0)
{
v___y_224_ = v___y_237_;
v___y_225_ = v_severity_144_;
goto v___jp_223_;
}
else
{
v___y_224_ = v___y_237_;
v___y_225_ = v___x_235_;
goto v___jp_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_247_, lean_object* v_msgData_248_, lean_object* v_severity_249_, lean_object* v_isSilent_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
uint8_t v_severity_boxed_254_; uint8_t v_isSilent_boxed_255_; lean_object* v_res_256_; 
v_severity_boxed_254_ = lean_unbox(v_severity_249_);
v_isSilent_boxed_255_ = lean_unbox(v_isSilent_250_);
v_res_256_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_247_, v_msgData_248_, v_severity_boxed_254_, v_isSilent_boxed_255_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v_ref_247_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(lean_object* v_ref_257_, lean_object* v_msgData_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
uint8_t v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v___x_262_ = 1;
v___x_263_ = 0;
v___x_264_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_257_, v_msgData_258_, v___x_262_, v___x_263_, v___y_259_, v___y_260_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(lean_object* v_ref_265_, lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_265_, v_msgData_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v_ref_265_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2));
v___x_276_ = l_Lean_stringToMessageData(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(lean_object* v_linterOption_277_, lean_object* v_stx_278_, lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_name_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_301_; 
v_name_283_ = lean_ctor_get(v_linterOption_277_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_linterOption_277_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v_linterOption_277_, 1);
lean_dec(v_unused_302_);
v___x_285_ = v_linterOption_277_;
v_isShared_286_ = v_isSharedCheck_301_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_name_283_);
lean_dec(v_linterOption_277_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_301_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_287_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1);
lean_inc(v_name_283_);
v___x_288_ = l_Lean_MessageData_ofName(v_name_283_);
if (v_isShared_286_ == 0)
{
lean_ctor_set_tag(v___x_285_, 7);
lean_ctor_set(v___x_285_, 1, v___x_288_);
lean_ctor_set(v___x_285_, 0, v___x_287_);
v___x_290_ = v___x_285_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_288_);
v___x_290_ = v_reuseFailAlloc_300_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v_disable_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_291_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v_disable_293_ = l_Lean_MessageData_note(v___x_292_);
v___x_294_ = l_Lean_Linter_linterMessageTag;
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v_msg_279_);
lean_ctor_set(v___x_295_, 1, v_disable_293_);
v___x_296_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_297_, 0, v_name_283_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
lean_inc(v_stx_278_);
v___x_298_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_298_, 0, v_stx_278_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_stx_278_, v___x_298_, v___y_280_, v___y_281_);
lean_dec(v_stx_278_);
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(lean_object* v_linterOption_303_, lean_object* v_stx_304_, lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_303_, v_stx_304_, v_msg_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_309_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2));
v___x_315_ = l_Lean_stringToMessageData(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6));
v___x_322_ = l_Lean_MessageData_ofFormat(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13);
v___x_335_ = l_Lean_MessageData_note(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15));
v___x_338_ = l_Lean_stringToMessageData(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(lean_object* v_stx_342_, lean_object* v_i_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v_hint_350_; lean_object* v___y_351_; lean_object* v___y_352_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_simpArgs_358_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_356_ = lean_box(0);
v___x_357_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1));
v_simpArgs_358_ = l_Lean_Elab_Tactic_getSimpParams(v_stx_342_);
v___x_409_ = lean_array_get_size(v_simpArgs_358_);
v___x_410_ = lean_nat_dec_lt(v_i_343_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec_ref(v_simpArgs_358_);
v___x_411_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16);
v___x_412_ = l_Nat_reprFast(v_i_343_);
v___x_413_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
v___x_414_ = l_Lean_MessageData_ofFormat(v___x_413_);
v___x_415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_411_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
v___x_416_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = l_Lean_MessageData_ofSyntax(v_stx_342_);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v___x_419_, v_a_344_, v_a_345_);
return v___x_420_;
}
else
{
v___y_360_ = v_a_344_;
v___y_361_ = v_a_345_;
goto v___jp_359_;
}
v___jp_347_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___y_348_);
lean_ctor_set(v___x_354_, 1, v_hint_350_);
v___x_355_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_353_, v___y_349_, v___x_354_, v___y_351_, v___y_352_);
return v___x_355_;
}
v___jp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_argStx_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_msg_368_; lean_object* v_otherArgs_369_; lean_object* v___x_370_; 
v___x_362_ = lean_array_get_size(v_simpArgs_358_);
v___x_363_ = lean_unsigned_to_nat(0u);
v_argStx_364_ = lean_array_get(v___x_356_, v_simpArgs_358_, v_i_343_);
v___x_365_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3);
lean_inc(v_argStx_364_);
v___x_366_ = l_Lean_MessageData_ofSyntax(v_argStx_364_);
v___x_367_ = l_Lean_indentD(v___x_366_);
v_msg_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_368_, 0, v___x_365_);
lean_ctor_set(v_msg_368_, 1, v___x_367_);
v_otherArgs_369_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4));
v___x_370_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v___x_362_, v_i_343_, v_simpArgs_358_, v___x_363_, v_otherArgs_369_);
lean_dec_ref(v_simpArgs_358_);
lean_dec(v_i_343_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
lean_inc(v_stx_342_);
v___x_372_ = l_Lean_Elab_Tactic_setSimpParams(v_stx_342_, v_a_371_);
lean_dec(v_a_371_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_357_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = lean_box(0);
v___x_375_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
lean_ctor_set(v___x_375_, 2, v___x_374_);
lean_ctor_set(v___x_375_, 3, v___x_374_);
lean_ctor_set(v___x_375_, 4, v___x_374_);
lean_ctor_set(v___x_375_, 5, v___x_374_);
v___x_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_376_, 0, v_stx_342_);
v___x_377_ = 4;
v___x_378_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_378_, 0, v___x_375_);
lean_ctor_set(v___x_378_, 1, v___x_376_);
lean_ctor_set(v___x_378_, 2, v___x_374_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*3, v___x_377_);
v___x_379_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7);
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_mk_empty_array_with_capacity(v___x_380_);
v___x_382_ = lean_array_push(v___x_381_, v___x_378_);
v___x_383_ = 0;
v___x_384_ = l_Lean_MessageData_hint(v___x_379_, v___x_382_, v___x_374_, v___x_374_, v___x_383_, v___y_360_, v___y_361_);
lean_dec_ref(v___x_382_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
lean_inc(v_argStx_364_);
v___x_386_ = l_Lean_Syntax_getKind(v_argStx_364_);
v___x_387_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11));
v___x_388_ = lean_name_eq(v___x_386_, v___x_387_);
lean_dec(v___x_386_);
if (v___x_388_ == 0)
{
v___y_348_ = v_msg_368_;
v___y_349_ = v_argStx_364_;
v_hint_350_ = v_a_385_;
v___y_351_ = v___y_360_;
v___y_352_ = v___y_361_;
goto v___jp_347_;
}
else
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = l_Lean_Syntax_getArg(v_argStx_364_, v___x_380_);
v___x_390_ = l_Lean_Syntax_isNone(v___x_389_);
lean_dec(v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v_a_385_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___y_348_ = v_msg_368_;
v___y_349_ = v_argStx_364_;
v_hint_350_ = v___x_392_;
v___y_351_ = v___y_360_;
v___y_352_ = v___y_361_;
goto v___jp_347_;
}
else
{
v___y_348_ = v_msg_368_;
v___y_349_ = v_argStx_364_;
v_hint_350_ = v_a_385_;
v___y_351_ = v___y_360_;
v___y_352_ = v___y_361_;
goto v___jp_347_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref_known(v_msg_368_, 2);
lean_dec(v_argStx_364_);
v_a_393_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_384_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_384_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref_known(v_msg_368_, 2);
lean_dec(v_argStx_364_);
lean_dec(v_stx_342_);
v_a_401_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_370_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_370_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed(lean_object* v_stx_421_, lean_object* v_i_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(v_stx_421_, v_i_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(lean_object* v_upperBound_427_, lean_object* v_i_428_, lean_object* v_simpArgs_429_, lean_object* v_inst_430_, lean_object* v_R_431_, lean_object* v_a_432_, lean_object* v_b_433_, lean_object* v_c_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_427_, v_i_428_, v_simpArgs_429_, v_a_432_, v_b_433_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(lean_object* v_upperBound_439_, lean_object* v_i_440_, lean_object* v_simpArgs_441_, lean_object* v_inst_442_, lean_object* v_R_443_, lean_object* v_a_444_, lean_object* v_b_445_, lean_object* v_c_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_439_, v_i_440_, v_simpArgs_441_, v_inst_442_, v_R_443_, v_a_444_, v_b_445_, v_c_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec_ref(v_simpArgs_441_);
lean_dec(v_i_440_);
lean_dec(v_upperBound_439_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(lean_object* v_00_u03b1_451_, lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_452_, v___y_453_, v___y_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(lean_object* v_00_u03b1_457_, lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(v_00_u03b1_457_, v_msg_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object* v_upperBound_463_, lean_object* v_snd_464_, lean_object* v_fst_465_, lean_object* v_a_466_, lean_object* v_b_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_a_472_; uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_lt(v_a_466_, v_upperBound_463_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec(v_a_466_);
lean_dec(v_fst_465_);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v_b_467_);
return v___x_477_;
}
else
{
uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_478_ = 0;
v___x_479_ = lean_box(0);
v___x_480_ = lean_box(v___x_478_);
v___x_481_ = lean_array_get(v___x_480_, v_snd_464_, v_a_466_);
lean_dec(v___x_480_);
v___x_482_ = lean_unbox(v___x_481_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_inc(v_a_466_);
lean_inc(v_fst_465_);
v___x_483_ = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed), 5, 2);
lean_closure_set(v___x_483_, 0, v_fst_465_);
lean_closure_set(v___x_483_, 1, v_a_466_);
v___x_484_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_483_, v___y_468_, v___y_469_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_dec_ref_known(v___x_484_, 1);
v_a_472_ = v___x_479_;
goto v___jp_471_;
}
else
{
lean_dec(v_a_466_);
lean_dec(v_fst_465_);
return v___x_484_;
}
}
else
{
v_a_472_ = v___x_479_;
goto v___jp_471_;
}
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(1u);
v___x_474_ = lean_nat_add(v_a_466_, v___x_473_);
lean_dec(v_a_466_);
v_a_466_ = v___x_474_;
v_b_467_ = v_a_472_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object* v_upperBound_485_, lean_object* v_snd_486_, lean_object* v_fst_487_, lean_object* v_a_488_, lean_object* v_b_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_485_, v_snd_486_, v_fst_487_, v_a_488_, v_b_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec_ref(v_snd_486_);
lean_dec(v_upperBound_485_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(lean_object* v_as_494_, size_t v_sz_495_, size_t v_i_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = lean_usize_dec_lt(v_i_496_, v_sz_495_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v_b_497_);
return v___x_502_;
}
else
{
lean_object* v_a_503_; lean_object* v_snd_504_; lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v_a_503_ = lean_array_uget_borrowed(v_as_494_, v_i_496_);
v_snd_504_ = lean_ctor_get(v_a_503_, 1);
v_fst_505_ = lean_ctor_get(v_snd_504_, 0);
v_snd_506_ = lean_ctor_get(v_snd_504_, 1);
v___x_507_ = lean_box(0);
v___x_508_ = lean_array_get_size(v_snd_506_);
v___x_509_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_505_);
v___x_510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_508_, v_snd_506_, v_fst_505_, v___x_509_, v___x_507_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_510_) == 0)
{
size_t v___x_511_; size_t v___x_512_; 
lean_dec_ref_known(v___x_510_, 1);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_496_, v___x_511_);
v_i_496_ = v___x_512_;
v_b_497_ = v___x_507_;
goto _start;
}
else
{
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object* v_as_514_, lean_object* v_sz_515_, lean_object* v_i_516_, lean_object* v_b_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
size_t v_sz_boxed_521_; size_t v_i_boxed_522_; lean_object* v_res_523_; 
v_sz_boxed_521_ = lean_unbox_usize(v_sz_515_);
lean_dec(v_sz_515_);
v_i_boxed_522_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_514_, v_sz_boxed_521_, v_i_boxed_522_, v_b_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v_as_514_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(lean_object* v_hi_524_, lean_object* v_pivot_525_, lean_object* v_as_526_, lean_object* v_i_527_, lean_object* v_k_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = lean_nat_dec_lt(v_k_528_, v_hi_524_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
lean_dec(v_k_528_);
v___x_530_ = lean_array_fswap(v_as_526_, v_i_527_, v_hi_524_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_i_527_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
return v___x_531_;
}
else
{
lean_object* v___x_532_; lean_object* v_fst_533_; lean_object* v_fst_534_; lean_object* v_start_535_; lean_object* v_start_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_532_ = lean_array_fget_borrowed(v_as_526_, v_k_528_);
v_fst_533_ = lean_ctor_get(v___x_532_, 0);
v_fst_534_ = lean_ctor_get(v_pivot_525_, 0);
v_start_535_ = lean_ctor_get(v_fst_533_, 0);
v_start_536_ = lean_ctor_get(v_fst_534_, 0);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_start_535_, v___x_537_);
v___x_539_ = lean_nat_dec_le(v___x_538_, v_start_536_);
lean_dec(v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_nat_add(v_k_528_, v___x_537_);
lean_dec(v_k_528_);
v_k_528_ = v___x_540_;
goto _start;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_array_fswap(v_as_526_, v_i_527_, v_k_528_);
v___x_543_ = lean_nat_add(v_i_527_, v___x_537_);
lean_dec(v_i_527_);
v___x_544_ = lean_nat_add(v_k_528_, v___x_537_);
lean_dec(v_k_528_);
v_as_526_ = v___x_542_;
v_i_527_ = v___x_543_;
v_k_528_ = v___x_544_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg___boxed(lean_object* v_hi_546_, lean_object* v_pivot_547_, lean_object* v_as_548_, lean_object* v_i_549_, lean_object* v_k_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_546_, v_pivot_547_, v_as_548_, v_i_549_, v_k_550_);
lean_dec_ref(v_pivot_547_);
lean_dec(v_hi_546_);
return v_res_551_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(lean_object* v_x1_552_, lean_object* v_x2_553_){
_start:
{
lean_object* v_fst_554_; lean_object* v_fst_555_; lean_object* v_start_556_; lean_object* v_start_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_fst_554_ = lean_ctor_get(v_x1_552_, 0);
v_fst_555_ = lean_ctor_get(v_x2_553_, 0);
v_start_556_ = lean_ctor_get(v_fst_554_, 0);
v_start_557_ = lean_ctor_get(v_fst_555_, 0);
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_add(v_start_556_, v___x_558_);
v___x_560_ = lean_nat_dec_le(v___x_559_, v_start_557_);
lean_dec(v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0___boxed(lean_object* v_x1_561_, lean_object* v_x2_562_){
_start:
{
uint8_t v_res_563_; lean_object* v_r_564_; 
v_res_563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v_x1_561_, v_x2_562_);
lean_dec_ref(v_x2_562_);
lean_dec_ref(v_x1_561_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(lean_object* v_n_565_, lean_object* v_as_566_, lean_object* v_lo_567_, lean_object* v_hi_568_){
_start:
{
lean_object* v___y_570_; uint8_t v___x_580_; 
v___x_580_ = lean_nat_dec_lt(v_lo_567_, v_hi_568_);
if (v___x_580_ == 0)
{
lean_dec(v_lo_567_);
return v_as_566_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v_mid_583_; lean_object* v___y_585_; lean_object* v___y_591_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_581_ = lean_nat_add(v_lo_567_, v_hi_568_);
v___x_582_ = lean_unsigned_to_nat(1u);
v_mid_583_ = lean_nat_shiftr(v___x_581_, v___x_582_);
lean_dec(v___x_581_);
v___x_596_ = lean_array_fget_borrowed(v_as_566_, v_mid_583_);
v___x_597_ = lean_array_fget_borrowed(v_as_566_, v_lo_567_);
v___x_598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
v___y_591_ = v_as_566_;
goto v___jp_590_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_array_fswap(v_as_566_, v_lo_567_, v_mid_583_);
v___y_591_ = v___x_599_;
goto v___jp_590_;
}
v___jp_584_:
{
lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_586_ = lean_array_fget_borrowed(v___y_585_, v_mid_583_);
v___x_587_ = lean_array_fget_borrowed(v___y_585_, v_hi_568_);
v___x_588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_dec(v_mid_583_);
v___y_570_ = v___y_585_;
goto v___jp_569_;
}
else
{
lean_object* v___x_589_; 
v___x_589_ = lean_array_fswap(v___y_585_, v_mid_583_, v_hi_568_);
lean_dec(v_mid_583_);
v___y_570_ = v___x_589_;
goto v___jp_569_;
}
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = lean_array_fget_borrowed(v___y_591_, v_hi_568_);
v___x_593_ = lean_array_fget_borrowed(v___y_591_, v_lo_567_);
v___x_594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
v___y_585_ = v___y_591_;
goto v___jp_584_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = lean_array_fswap(v___y_591_, v_lo_567_, v_hi_568_);
v___y_585_ = v___x_595_;
goto v___jp_584_;
}
}
}
v___jp_569_:
{
lean_object* v_pivot_571_; lean_object* v___x_572_; lean_object* v_fst_573_; lean_object* v_snd_574_; uint8_t v___x_575_; 
v_pivot_571_ = lean_array_fget(v___y_570_, v_hi_568_);
lean_inc_n(v_lo_567_, 2);
v___x_572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_568_, v_pivot_571_, v___y_570_, v_lo_567_, v_lo_567_);
lean_dec(v_pivot_571_);
v_fst_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v___x_572_, 1);
lean_inc(v_snd_574_);
lean_dec_ref(v___x_572_);
v___x_575_ = lean_nat_dec_le(v_hi_568_, v_fst_573_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_565_, v_snd_574_, v_lo_567_, v_fst_573_);
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_add(v_fst_573_, v___x_577_);
lean_dec(v_fst_573_);
v_as_566_ = v___x_576_;
v_lo_567_ = v___x_578_;
goto _start;
}
else
{
lean_dec(v_fst_573_);
lean_dec(v_lo_567_);
return v_snd_574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___boxed(lean_object* v_n_600_, lean_object* v_as_601_, lean_object* v_lo_602_, lean_object* v_hi_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_600_, v_as_601_, v_lo_602_, v_hi_603_);
lean_dec(v_hi_603_);
lean_dec(v_n_600_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
return v_x_605_;
}
else
{
lean_object* v_key_607_; lean_object* v_value_608_; lean_object* v_tail_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_key_607_ = lean_ctor_get(v_x_606_, 0);
v_value_608_ = lean_ctor_get(v_x_606_, 1);
v_tail_609_ = lean_ctor_get(v_x_606_, 2);
lean_inc(v_value_608_);
lean_inc(v_key_607_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v_key_607_);
lean_ctor_set(v___x_610_, 1, v_value_608_);
v___x_611_ = lean_array_push(v_x_605_, v___x_610_);
v_x_605_ = v___x_611_;
v_x_606_ = v_tail_609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10___boxed(lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_x_613_, v_x_614_);
lean_dec(v_x_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(lean_object* v_as_616_, size_t v_i_617_, size_t v_stop_618_, lean_object* v_b_619_){
_start:
{
uint8_t v___x_620_; 
v___x_620_ = lean_usize_dec_eq(v_i_617_, v_stop_618_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; size_t v___x_623_; size_t v___x_624_; 
v___x_621_ = lean_array_uget_borrowed(v_as_616_, v_i_617_);
v___x_622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_b_619_, v___x_621_);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_617_, v___x_623_);
v_i_617_ = v___x_624_;
v_b_619_ = v___x_622_;
goto _start;
}
else
{
return v_b_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_, lean_object* v_b_629_){
_start:
{
size_t v_i_boxed_630_; size_t v_stop_boxed_631_; lean_object* v_res_632_; 
v_i_boxed_630_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_631_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_as_626_, v_i_boxed_630_, v_stop_boxed_631_, v_b_629_);
lean_dec_ref(v_as_626_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(lean_object* v_o_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_env_638_; lean_object* v___x_639_; lean_object* v_toEnvExtension_640_; lean_object* v_asyncMode_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v_merged_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
v___x_636_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_637_ = lean_st_ref_get(v___y_634_);
v_env_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_env_638_);
lean_dec(v___x_637_);
v___x_639_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_640_ = lean_ctor_get(v___x_639_, 0);
v_asyncMode_641_ = lean_ctor_get(v_toEnvExtension_640_, 2);
v___x_642_ = lean_box(0);
v___x_643_ = 0;
v___x_644_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_636_, v___x_639_, v_env_638_, v_asyncMode_641_, v___x_642_, v___x_643_);
v_merged_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v___x_644_, 1);
lean_dec(v_unused_654_);
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_merged_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v_merged_645_);
lean_ctor_set(v___x_647_, 0, v_o_633_);
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_o_633_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_merged_645_);
v___x_650_ = v_reuseFailAlloc_652_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(lean_object* v_o_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_655_, v___y_656_);
lean_dec(v___y_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_scopes_664_; lean_object* v___x_665_; lean_object* v_opts_666_; lean_object* v___x_667_; 
v___x_662_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_663_ = lean_st_ref_get(v___y_660_);
v_scopes_664_ = lean_ctor_get(v___x_663_, 2);
lean_inc(v_scopes_664_);
lean_dec(v___x_663_);
v___x_665_ = l_List_head_x21___redArg(v___x_662_, v_scopes_664_);
lean_dec(v_scopes_664_);
v_opts_666_ = lean_ctor_get(v___x_665_, 1);
lean_inc_ref(v_opts_666_);
lean_dec(v___x_665_);
v___x_667_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_opts_666_, v___y_660_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(lean_object* v_a_672_, lean_object* v_x_673_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
lean_object* v___x_674_; 
v___x_674_ = lean_box(0);
return v___x_674_;
}
else
{
lean_object* v_key_675_; lean_object* v_value_676_; lean_object* v_tail_677_; uint8_t v___x_678_; 
v_key_675_ = lean_ctor_get(v_x_673_, 0);
v_value_676_ = lean_ctor_get(v_x_673_, 1);
v_tail_677_ = lean_ctor_get(v_x_673_, 2);
v___x_678_ = l_Lean_Syntax_instBEqRange_beq(v_key_675_, v_a_672_);
if (v___x_678_ == 0)
{
v_x_673_ = v_tail_677_;
goto _start;
}
else
{
lean_object* v___x_680_; 
lean_inc(v_value_676_);
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v_value_676_);
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(lean_object* v_a_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_681_, v_x_682_);
lean_dec(v_x_682_);
lean_dec_ref(v_a_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object* v_m_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_buckets_686_; lean_object* v___x_687_; uint64_t v___x_688_; uint64_t v___x_689_; uint64_t v___x_690_; uint64_t v_fold_691_; uint64_t v___x_692_; uint64_t v___x_693_; uint64_t v___x_694_; size_t v___x_695_; size_t v___x_696_; size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_buckets_686_ = lean_ctor_get(v_m_684_, 1);
v___x_687_ = lean_array_get_size(v_buckets_686_);
v___x_688_ = l_Lean_Syntax_instHashableRange_hash(v_a_685_);
v___x_689_ = 32ULL;
v___x_690_ = lean_uint64_shift_right(v___x_688_, v___x_689_);
v_fold_691_ = lean_uint64_xor(v___x_688_, v___x_690_);
v___x_692_ = 16ULL;
v___x_693_ = lean_uint64_shift_right(v_fold_691_, v___x_692_);
v___x_694_ = lean_uint64_xor(v_fold_691_, v___x_693_);
v___x_695_ = lean_uint64_to_usize(v___x_694_);
v___x_696_ = lean_usize_of_nat(v___x_687_);
v___x_697_ = ((size_t)1ULL);
v___x_698_ = lean_usize_sub(v___x_696_, v___x_697_);
v___x_699_ = lean_usize_land(v___x_695_, v___x_698_);
v___x_700_ = lean_array_uget_borrowed(v_buckets_686_, v___x_699_);
v___x_701_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_685_, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object* v_m_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_702_, v_a_703_);
lean_dec_ref(v_a_703_);
lean_dec_ref(v_m_702_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(uint8_t v___x_705_, lean_object* v_as_706_, lean_object* v_bs_707_, lean_object* v_i_708_, lean_object* v_cs_709_){
_start:
{
uint8_t v___y_711_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_array_get_size(v_as_706_);
v___x_718_ = lean_nat_dec_lt(v_i_708_, v___x_717_);
if (v___x_718_ == 0)
{
lean_dec(v_i_708_);
return v_cs_709_;
}
else
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = lean_array_get_size(v_bs_707_);
v___x_720_ = lean_nat_dec_lt(v_i_708_, v___x_719_);
if (v___x_720_ == 0)
{
lean_dec(v_i_708_);
return v_cs_709_;
}
else
{
lean_object* v_a_721_; uint8_t v___x_722_; 
v_a_721_ = lean_array_fget_borrowed(v_as_706_, v_i_708_);
v___x_722_ = lean_unbox(v_a_721_);
if (v___x_722_ == 0)
{
lean_object* v_b_723_; uint8_t v___x_724_; 
v_b_723_ = lean_array_fget_borrowed(v_bs_707_, v_i_708_);
v___x_724_ = lean_unbox(v_b_723_);
v___y_711_ = v___x_724_;
goto v___jp_710_;
}
else
{
v___y_711_ = v___x_705_;
goto v___jp_710_;
}
}
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_i_708_, v___x_712_);
lean_dec(v_i_708_);
v___x_714_ = lean_box(v___y_711_);
v___x_715_ = lean_array_push(v_cs_709_, v___x_714_);
v_i_708_ = v___x_713_;
v_cs_709_ = v___x_715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object* v___x_725_, lean_object* v_as_726_, lean_object* v_bs_727_, lean_object* v_i_728_, lean_object* v_cs_729_){
_start:
{
uint8_t v___x_12862__boxed_730_; lean_object* v_res_731_; 
v___x_12862__boxed_730_ = lean_unbox(v___x_725_);
v_res_731_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_12862__boxed_730_, v_as_726_, v_bs_727_, v_i_728_, v_cs_729_);
lean_dec_ref(v_bs_727_);
lean_dec_ref(v_as_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(lean_object* v_msgData_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; lean_object* v_env_736_; uint8_t v___x_737_; lean_object* v_env_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_scopes_741_; lean_object* v___x_742_; lean_object* v_opts_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_735_ = lean_st_ref_get(v___y_733_);
v_env_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc_ref(v_env_736_);
lean_dec(v___x_735_);
v___x_737_ = 0;
v_env_738_ = l_Lean_Environment_setRecordingDeps(v_env_736_, v___x_737_);
v___x_739_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_740_ = lean_st_ref_get(v___y_733_);
v_scopes_741_ = lean_ctor_get(v___x_740_, 2);
lean_inc(v_scopes_741_);
lean_dec(v___x_740_);
v___x_742_ = l_List_head_x21___redArg(v___x_739_, v_scopes_741_);
lean_dec(v_scopes_741_);
v_opts_743_ = lean_ctor_get(v___x_742_, 1);
lean_inc_ref(v_opts_743_);
lean_dec(v___x_742_);
v___x_744_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_745_ = lean_unsigned_to_nat(32u);
v___x_746_ = lean_mk_empty_array_with_capacity(v___x_745_);
lean_dec_ref(v___x_746_);
v___x_747_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
v___x_748_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_748_, 0, v_env_738_);
lean_ctor_set(v___x_748_, 1, v___x_744_);
lean_ctor_set(v___x_748_, 2, v___x_747_);
lean_ctor_set(v___x_748_, 3, v_opts_743_);
v___x_749_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_msgData_732_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_751_, v___y_752_);
lean_dec(v___y_752_);
return v_res_754_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_box(1);
v___x_756_ = l_Lean_MessageData_ofFormat(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2));
v___x_761_ = l_Lean_MessageData_ofFormat(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
return v_x_762_;
}
else
{
lean_object* v_head_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_787_; 
v_head_764_ = lean_ctor_get(v_x_763_, 0);
v_tail_765_ = lean_ctor_get(v_x_763_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_763_);
if (v_isSharedCheck_787_ == 0)
{
v___x_767_ = v_x_763_;
v_isShared_768_ = v_isSharedCheck_787_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_inc(v_head_764_);
lean_dec(v_x_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_787_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_before_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_785_; 
v_before_769_ = lean_ctor_get(v_head_764_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v_head_764_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_head_764_, 1);
lean_dec(v_unused_786_);
v___x_771_ = v_head_764_;
v_isShared_772_ = v_isSharedCheck_785_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_before_769_);
lean_dec(v_head_764_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_785_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_772_ == 0)
{
lean_ctor_set_tag(v___x_771_, 7);
lean_ctor_set(v___x_771_, 1, v___x_773_);
lean_ctor_set(v___x_771_, 0, v_x_762_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_x_762_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_784_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3);
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 7);
lean_ctor_set(v___x_767_, 1, v___x_776_);
lean_ctor_set(v___x_767_, 0, v___x_775_);
v___x_778_ = v___x_767_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_783_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = l_Lean_MessageData_ofSyntax(v_before_769_);
v___x_780_ = l_Lean_indentD(v___x_779_);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_778_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v_x_762_ = v___x_781_;
v_x_763_ = v_tail_765_;
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
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1));
v___x_792_ = l_Lean_MessageData_ofFormat(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(lean_object* v_msgData_793_, lean_object* v_macroStack_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v_scopes_799_; lean_object* v___x_800_; lean_object* v_opts_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_797_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_798_ = lean_st_ref_get(v___y_795_);
v_scopes_799_ = lean_ctor_get(v___x_798_, 2);
lean_inc(v_scopes_799_);
lean_dec(v___x_798_);
v___x_800_ = l_List_head_x21___redArg(v___x_797_, v_scopes_799_);
lean_dec(v_scopes_799_);
v_opts_801_ = lean_ctor_get(v___x_800_, 1);
lean_inc_ref(v_opts_801_);
lean_dec(v___x_800_);
v___x_802_ = l_Lean_Elab_pp_macroStack;
v___x_803_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_801_, v___x_802_);
lean_dec_ref(v_opts_801_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v_macroStack_794_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_msgData_793_);
return v___x_804_;
}
else
{
if (lean_obj_tag(v_macroStack_794_) == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_msgData_793_);
return v___x_805_;
}
else
{
lean_object* v_head_806_; lean_object* v_after_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_822_; 
v_head_806_ = lean_ctor_get(v_macroStack_794_, 0);
lean_inc(v_head_806_);
v_after_807_ = lean_ctor_get(v_head_806_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_head_806_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_head_806_, 0);
lean_dec(v_unused_823_);
v___x_809_ = v_head_806_;
v_isShared_810_ = v_isSharedCheck_822_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_after_807_);
lean_dec(v_head_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_822_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_811_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 7);
lean_ctor_set(v___x_809_, 1, v___x_811_);
lean_ctor_set(v___x_809_, 0, v_msgData_793_);
v___x_813_ = v___x_809_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_msgData_793_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_811_);
v___x_813_ = v_reuseFailAlloc_821_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_msgData_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_814_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_MessageData_ofSyntax(v_after_807_);
v___x_817_ = l_Lean_indentD(v___x_816_);
v_msgData_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_818_, 0, v___x_815_);
lean_ctor_set(v_msgData_818_, 1, v___x_817_);
v___x_819_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(v_msgData_818_, v_macroStack_794_);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v_msgData_824_, lean_object* v_macroStack_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_824_, v_macroStack_825_, v___y_826_);
lean_dec(v___y_826_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(lean_object* v_msg_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Elab_Command_getRef___redArg(v___y_830_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v_macroStack_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v_macroStack_835_ = lean_ctor_get(v___y_830_, 4);
v___x_836_ = l_Lean_Elab_getBetterRef(v_a_834_, v_macroStack_835_);
lean_dec(v_a_834_);
v___x_837_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msg_829_, v___y_831_);
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
lean_inc(v_macroStack_835_);
v___x_839_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_a_838_, v_macroStack_835_, v___y_831_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_848_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_836_);
lean_ctor_set(v___x_844_, 1, v_a_840_);
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 1);
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v_msg_829_);
v_a_849_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_833_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_833_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg___boxed(lean_object* v_msg_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(lean_object* v_ref_862_, lean_object* v_msg_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Elab_Command_getRef___redArg(v___y_864_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v_fileName_869_; lean_object* v_fileMap_870_; lean_object* v_currRecDepth_871_; lean_object* v_cmdPos_872_; lean_object* v_macroStack_873_; lean_object* v_quotContext_x3f_874_; lean_object* v_currMacroScope_875_; lean_object* v_snap_x3f_876_; lean_object* v_cancelTk_x3f_877_; uint8_t v_suppressElabErrors_878_; uint8_t v_checkDeprecated_879_; lean_object* v_ref_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v_fileName_869_ = lean_ctor_get(v___y_864_, 0);
v_fileMap_870_ = lean_ctor_get(v___y_864_, 1);
v_currRecDepth_871_ = lean_ctor_get(v___y_864_, 2);
v_cmdPos_872_ = lean_ctor_get(v___y_864_, 3);
v_macroStack_873_ = lean_ctor_get(v___y_864_, 4);
v_quotContext_x3f_874_ = lean_ctor_get(v___y_864_, 5);
v_currMacroScope_875_ = lean_ctor_get(v___y_864_, 6);
v_snap_x3f_876_ = lean_ctor_get(v___y_864_, 8);
v_cancelTk_x3f_877_ = lean_ctor_get(v___y_864_, 9);
v_suppressElabErrors_878_ = lean_ctor_get_uint8(v___y_864_, sizeof(void*)*10);
v_checkDeprecated_879_ = lean_ctor_get_uint8(v___y_864_, sizeof(void*)*10 + 1);
v_ref_880_ = l_Lean_replaceRef(v_ref_862_, v_a_868_);
lean_dec(v_a_868_);
lean_inc(v_cancelTk_x3f_877_);
lean_inc(v_snap_x3f_876_);
lean_inc(v_currMacroScope_875_);
lean_inc(v_quotContext_x3f_874_);
lean_inc(v_macroStack_873_);
lean_inc(v_cmdPos_872_);
lean_inc(v_currRecDepth_871_);
lean_inc_ref(v_fileMap_870_);
lean_inc_ref(v_fileName_869_);
v___x_881_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_881_, 0, v_fileName_869_);
lean_ctor_set(v___x_881_, 1, v_fileMap_870_);
lean_ctor_set(v___x_881_, 2, v_currRecDepth_871_);
lean_ctor_set(v___x_881_, 3, v_cmdPos_872_);
lean_ctor_set(v___x_881_, 4, v_macroStack_873_);
lean_ctor_set(v___x_881_, 5, v_quotContext_x3f_874_);
lean_ctor_set(v___x_881_, 6, v_currMacroScope_875_);
lean_ctor_set(v___x_881_, 7, v_ref_880_);
lean_ctor_set(v___x_881_, 8, v_snap_x3f_876_);
lean_ctor_set(v___x_881_, 9, v_cancelTk_x3f_877_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*10, v_suppressElabErrors_878_);
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*10 + 1, v_checkDeprecated_879_);
v___x_882_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_863_, v___x_881_, v___y_865_);
lean_dec_ref_known(v___x_881_, 10);
return v___x_882_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_msg_863_);
v_a_883_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_867_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_867_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg___boxed(lean_object* v_ref_891_, lean_object* v_msg_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_891_, v_msg_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v_ref_891_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
return v_x_897_;
}
else
{
lean_object* v_key_899_; lean_object* v_value_900_; lean_object* v_tail_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_924_; 
v_key_899_ = lean_ctor_get(v_x_898_, 0);
v_value_900_ = lean_ctor_get(v_x_898_, 1);
v_tail_901_ = lean_ctor_get(v_x_898_, 2);
v_isSharedCheck_924_ = !lean_is_exclusive(v_x_898_);
if (v_isSharedCheck_924_ == 0)
{
v___x_903_ = v_x_898_;
v_isShared_904_ = v_isSharedCheck_924_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_tail_901_);
lean_inc(v_value_900_);
lean_inc(v_key_899_);
lean_dec(v_x_898_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_924_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; uint64_t v_fold_909_; uint64_t v___x_910_; uint64_t v___x_911_; uint64_t v___x_912_; size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_905_ = lean_array_get_size(v_x_897_);
v___x_906_ = l_Lean_Syntax_instHashableRange_hash(v_key_899_);
v___x_907_ = 32ULL;
v___x_908_ = lean_uint64_shift_right(v___x_906_, v___x_907_);
v_fold_909_ = lean_uint64_xor(v___x_906_, v___x_908_);
v___x_910_ = 16ULL;
v___x_911_ = lean_uint64_shift_right(v_fold_909_, v___x_910_);
v___x_912_ = lean_uint64_xor(v_fold_909_, v___x_911_);
v___x_913_ = lean_uint64_to_usize(v___x_912_);
v___x_914_ = lean_usize_of_nat(v___x_905_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_sub(v___x_914_, v___x_915_);
v___x_917_ = lean_usize_land(v___x_913_, v___x_916_);
v___x_918_ = lean_array_uget_borrowed(v_x_897_, v___x_917_);
lean_inc(v___x_918_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 2, v___x_918_);
v___x_920_ = v___x_903_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_key_899_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_value_900_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v___x_918_);
v___x_920_ = v_reuseFailAlloc_923_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; 
v___x_921_ = lean_array_uset(v_x_897_, v___x_917_, v___x_920_);
v_x_897_ = v___x_921_;
v_x_898_ = v_tail_901_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(lean_object* v_i_925_, lean_object* v_source_926_, lean_object* v_target_927_){
_start:
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = lean_array_get_size(v_source_926_);
v___x_929_ = lean_nat_dec_lt(v_i_925_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec_ref(v_source_926_);
lean_dec(v_i_925_);
return v_target_927_;
}
else
{
lean_object* v_es_930_; lean_object* v___x_931_; lean_object* v_source_932_; lean_object* v_target_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v_es_930_ = lean_array_fget(v_source_926_, v_i_925_);
v___x_931_ = lean_box(0);
v_source_932_ = lean_array_fset(v_source_926_, v_i_925_, v___x_931_);
v_target_933_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_target_927_, v_es_930_);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_i_925_, v___x_934_);
lean_dec(v_i_925_);
v_i_925_ = v___x_935_;
v_source_926_ = v_source_932_;
v_target_927_ = v_target_933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(lean_object* v_data_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v_nbuckets_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_938_ = lean_array_get_size(v_data_937_);
v___x_939_ = lean_unsigned_to_nat(2u);
v_nbuckets_940_ = lean_nat_mul(v___x_938_, v___x_939_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_box(0);
v___x_943_ = lean_mk_array(v_nbuckets_940_, v___x_942_);
v___x_944_ = lean_array_propagate_mark(v_data_937_, v___x_943_);
v___x_945_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v___x_941_, v_data_937_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object* v_a_946_, lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_947_) == 0)
{
uint8_t v___x_948_; 
v___x_948_ = 0;
return v___x_948_;
}
else
{
lean_object* v_key_949_; lean_object* v_tail_950_; uint8_t v___x_951_; 
v_key_949_ = lean_ctor_get(v_x_947_, 0);
v_tail_950_ = lean_ctor_get(v_x_947_, 2);
v___x_951_ = l_Lean_Syntax_instBEqRange_beq(v_key_949_, v_a_946_);
if (v___x_951_ == 0)
{
v_x_947_ = v_tail_950_;
goto _start;
}
else
{
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object* v_a_953_, lean_object* v_x_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_953_, v_x_954_);
lean_dec(v_x_954_);
lean_dec_ref(v_a_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(lean_object* v_a_957_, lean_object* v_b_958_, lean_object* v_x_959_){
_start:
{
if (lean_obj_tag(v_x_959_) == 0)
{
lean_dec(v_b_958_);
lean_dec_ref(v_a_957_);
return v_x_959_;
}
else
{
lean_object* v_key_960_; lean_object* v_value_961_; lean_object* v_tail_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_974_; 
v_key_960_ = lean_ctor_get(v_x_959_, 0);
v_value_961_ = lean_ctor_get(v_x_959_, 1);
v_tail_962_ = lean_ctor_get(v_x_959_, 2);
v_isSharedCheck_974_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_974_ == 0)
{
v___x_964_ = v_x_959_;
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_tail_962_);
lean_inc(v_value_961_);
lean_inc(v_key_960_);
lean_dec(v_x_959_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_974_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint8_t v___x_966_; 
v___x_966_ = l_Lean_Syntax_instBEqRange_beq(v_key_960_, v_a_957_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_957_, v_b_958_, v_tail_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 2, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_key_960_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_value_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
lean_object* v___x_972_; 
lean_dec(v_value_961_);
lean_dec(v_key_960_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_b_958_);
lean_ctor_set(v___x_964_, 0, v_a_957_);
v___x_972_ = v___x_964_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_957_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_b_958_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_tail_962_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object* v_m_975_, lean_object* v_a_976_, lean_object* v_b_977_){
_start:
{
lean_object* v_size_978_; lean_object* v_buckets_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1022_; 
v_size_978_ = lean_ctor_get(v_m_975_, 0);
v_buckets_979_ = lean_ctor_get(v_m_975_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_m_975_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_981_ = v_m_975_;
v_isShared_982_ = v_isSharedCheck_1022_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_buckets_979_);
lean_inc(v_size_978_);
lean_dec(v_m_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1022_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; uint64_t v___x_984_; uint64_t v___x_985_; uint64_t v___x_986_; uint64_t v_fold_987_; uint64_t v___x_988_; uint64_t v___x_989_; uint64_t v___x_990_; size_t v___x_991_; size_t v___x_992_; size_t v___x_993_; size_t v___x_994_; size_t v___x_995_; lean_object* v_bkt_996_; uint8_t v___x_997_; 
v___x_983_ = lean_array_get_size(v_buckets_979_);
v___x_984_ = l_Lean_Syntax_instHashableRange_hash(v_a_976_);
v___x_985_ = 32ULL;
v___x_986_ = lean_uint64_shift_right(v___x_984_, v___x_985_);
v_fold_987_ = lean_uint64_xor(v___x_984_, v___x_986_);
v___x_988_ = 16ULL;
v___x_989_ = lean_uint64_shift_right(v_fold_987_, v___x_988_);
v___x_990_ = lean_uint64_xor(v_fold_987_, v___x_989_);
v___x_991_ = lean_uint64_to_usize(v___x_990_);
v___x_992_ = lean_usize_of_nat(v___x_983_);
v___x_993_ = ((size_t)1ULL);
v___x_994_ = lean_usize_sub(v___x_992_, v___x_993_);
v___x_995_ = lean_usize_land(v___x_991_, v___x_994_);
v_bkt_996_ = lean_array_uget_borrowed(v_buckets_979_, v___x_995_);
v___x_997_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_976_, v_bkt_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v_size_x27_999_; lean_object* v___x_1000_; lean_object* v_buckets_x27_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_998_ = lean_unsigned_to_nat(1u);
v_size_x27_999_ = lean_nat_add(v_size_978_, v___x_998_);
lean_dec(v_size_978_);
lean_inc(v_bkt_996_);
v___x_1000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1000_, 0, v_a_976_);
lean_ctor_set(v___x_1000_, 1, v_b_977_);
lean_ctor_set(v___x_1000_, 2, v_bkt_996_);
v_buckets_x27_1001_ = lean_array_uset(v_buckets_979_, v___x_995_, v___x_1000_);
v___x_1002_ = lean_unsigned_to_nat(4u);
v___x_1003_ = lean_nat_mul(v_size_x27_999_, v___x_1002_);
v___x_1004_ = lean_unsigned_to_nat(3u);
v___x_1005_ = lean_nat_div(v___x_1003_, v___x_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_array_get_size(v_buckets_x27_1001_);
v___x_1007_ = lean_nat_dec_le(v___x_1005_, v___x_1006_);
lean_dec(v___x_1005_);
if (v___x_1007_ == 0)
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
v_val_1008_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_buckets_x27_1001_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v_val_1008_);
lean_ctor_set(v___x_981_, 0, v_size_x27_999_);
v___x_1010_ = v___x_981_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_size_x27_999_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_val_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v___x_1013_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v_buckets_x27_1001_);
lean_ctor_set(v___x_981_, 0, v_size_x27_999_);
v___x_1013_ = v___x_981_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_size_x27_999_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_buckets_x27_1001_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v___x_1015_; lean_object* v_buckets_x27_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_inc(v_bkt_996_);
v___x_1015_ = lean_box(0);
v_buckets_x27_1016_ = lean_array_uset(v_buckets_979_, v___x_995_, v___x_1015_);
v___x_1017_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_976_, v_b_977_, v_bkt_996_);
v___x_1018_ = lean_array_uset(v_buckets_x27_1016_, v___x_995_, v___x_1017_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v___x_1018_);
v___x_1020_ = v___x_981_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_size_978_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(lean_object* v___x_1043_, lean_object* v_val_1044_, uint8_t v___x_1045_, lean_object* v_ci_1046_, lean_object* v_info_1047_, lean_object* v_x_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
if (lean_obj_tag(v_info_1047_) == 10)
{
lean_object* v_i_1052_; lean_object* v_stx_1053_; lean_object* v_value_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1148_; 
v_i_1052_ = lean_ctor_get(v_info_1047_, 0);
lean_inc_ref(v_i_1052_);
v_stx_1053_ = lean_ctor_get(v_i_1052_, 0);
v_value_1054_ = lean_ctor_get(v_i_1052_, 1);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_i_1052_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1056_ = v_i_1052_;
v_isShared_1057_ = v_isSharedCheck_1148_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_value_1054_);
lean_inc(v_stx_1053_);
lean_dec(v_i_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1148_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; 
v___x_1058_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_1054_, v___x_1043_);
lean_dec(v_value_1054_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1138_; 
v_val_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1138_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1138_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Elab_Info_range_x3f(v_info_1047_);
if (lean_obj_tag(v___x_1063_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1133_; 
v_val_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1133_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1133_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_maskAcc_1069_; lean_object* v___y_1080_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6));
lean_inc(v_stx_1053_);
v___x_1121_ = l_Lean_Syntax_isOfKind(v_stx_1053_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8));
lean_inc(v_stx_1053_);
v___x_1123_ = l_Lean_Syntax_isOfKind(v_stx_1053_, v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1131_; 
lean_del_object(v___x_1066_);
lean_dec(v_val_1064_);
lean_del_object(v___x_1061_);
lean_dec(v_val_1059_);
lean_del_object(v___x_1056_);
lean_dec(v_stx_1053_);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_info_1047_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v_info_1047_, 0);
lean_dec(v_unused_1132_);
v___x_1125_ = v_info_1047_;
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v_info_1047_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_box(0);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
else
{
goto v___jp_1084_;
}
}
else
{
goto v___jp_1084_;
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_st_ref_take(v_val_1044_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v_maskAcc_1069_);
v___x_1072_ = v___x_1056_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_stx_1053_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_maskAcc_1069_);
v___x_1072_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_1070_, v_val_1064_, v___x_1072_);
v___x_1074_ = lean_st_ref_put(v_val_1044_, v___x_1073_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1074_);
v___x_1076_ = v___x_1066_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
v___jp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0));
v___x_1083_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_1045_, v_val_1059_, v___y_1080_, v___x_1081_, v___x_1082_);
lean_dec_ref(v___y_1080_);
lean_dec(v_val_1059_);
v_maskAcc_1069_ = v___x_1083_;
goto v___jp_1068_;
}
v___jp_1084_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_st_ref_get(v_val_1044_);
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_1085_, v_val_1064_);
lean_dec(v___x_1085_);
if (lean_obj_tag(v___x_1086_) == 1)
{
lean_object* v_val_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1119_; 
v_val_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1119_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_val_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1119_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_snd_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1117_; 
v_snd_1091_ = lean_ctor_get(v_val_1087_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_val_1087_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_val_1087_, 0);
lean_dec(v_unused_1118_);
v___x_1093_ = v_val_1087_;
v_isShared_1094_ = v_isSharedCheck_1117_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_snd_1091_);
lean_dec(v_val_1087_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1117_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1095_ = lean_array_get_size(v_val_1059_);
v___x_1096_ = lean_array_get_size(v_snd_1091_);
v___x_1097_ = lean_nat_dec_eq(v___x_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1098_ = l_Lean_Elab_Info_stx(v_info_1047_);
lean_dec_ref_known(v_info_1047_, 1);
v___x_1099_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2);
v___x_1100_ = l_Nat_reprFast(v___x_1096_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 3);
lean_ctor_set(v___x_1089_, 0, v___x_1100_);
v___x_1102_ = v___x_1089_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1103_ = l_Lean_MessageData_ofFormat(v___x_1102_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 7);
lean_ctor_set(v___x_1093_, 1, v___x_1103_);
lean_ctor_set(v___x_1093_, 0, v___x_1099_);
v___x_1105_ = v___x_1093_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1106_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = l_Nat_reprFast(v___x_1095_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 3);
lean_ctor_set(v___x_1061_, 0, v___x_1108_);
v___x_1110_ = v___x_1061_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = l_Lean_MessageData_ofFormat(v___x_1110_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1107_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v___x_1098_, v___x_1112_, v___y_1049_, v___y_1050_);
lean_dec(v___x_1098_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
v___y_1080_ = v_snd_1091_;
goto v___jp_1079_;
}
else
{
lean_dec(v_snd_1091_);
lean_del_object(v___x_1066_);
lean_dec(v_val_1064_);
lean_dec(v_val_1059_);
lean_del_object(v___x_1056_);
lean_dec(v_stx_1053_);
return v___x_1113_;
}
}
}
}
}
else
{
lean_del_object(v___x_1093_);
lean_del_object(v___x_1089_);
lean_del_object(v___x_1061_);
lean_dec_ref_known(v_info_1047_, 1);
v___y_1080_ = v_snd_1091_;
goto v___jp_1079_;
}
}
}
}
else
{
lean_dec(v___x_1086_);
lean_del_object(v___x_1061_);
lean_dec_ref_known(v_info_1047_, 1);
v_maskAcc_1069_ = v_val_1059_;
goto v___jp_1068_;
}
}
}
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
lean_dec(v___x_1063_);
lean_dec(v_val_1059_);
lean_del_object(v___x_1056_);
lean_dec(v_stx_1053_);
lean_dec_ref_known(v_info_1047_, 1);
v___x_1134_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1134_);
v___x_1136_ = v___x_1061_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v___x_1058_);
lean_del_object(v___x_1056_);
lean_dec(v_stx_1053_);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_info_1047_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_info_1047_, 0);
lean_dec(v_unused_1147_);
v___x_1140_ = v_info_1047_;
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
else
{
lean_dec(v_info_1047_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_box(0);
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1142_);
v___x_1144_ = v___x_1140_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec_ref(v_info_1047_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(lean_object* v___x_1151_, lean_object* v_val_1152_, lean_object* v___x_1153_, lean_object* v_ci_1154_, lean_object* v_info_1155_, lean_object* v_x_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
uint8_t v___x_13438__boxed_1160_; lean_object* v_res_1161_; 
v___x_13438__boxed_1160_ = lean_unbox(v___x_1153_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v___x_1151_, v_val_1152_, v___x_13438__boxed_1160_, v_ci_1154_, v_info_1155_, v_x_1156_, v___y_1157_, v___y_1158_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec_ref(v_x_1156_);
lean_dec_ref(v_ci_1154_);
lean_dec(v_val_1152_);
lean_dec(v___x_1151_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(lean_object* v_postNode_1162_, lean_object* v_ci_1163_, lean_object* v_i_1164_, lean_object* v_cs_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; 
lean_inc(v___y_1168_);
lean_inc_ref(v___y_1167_);
v___x_1170_ = lean_apply_6(v_postNode_1162_, v_ci_1163_, v_i_1164_, v_cs_1165_, v___y_1167_, v___y_1168_, lean_box(0));
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(lean_object* v_postNode_1171_, lean_object* v_ci_1172_, lean_object* v_i_1173_, lean_object* v_cs_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(v_postNode_1171_, v_ci_1172_, v_i_1173_, v_cs_1174_, v_x_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v_x_1175_);
return v_res_1179_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_instMonadEIO___redArg();
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(lean_object* v_msg_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_toApplicative_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1220_; 
v___x_1187_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0);
v___x_1188_ = l_StateRefT_x27_instMonad___redArg(v___x_1187_);
v_toApplicative_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1188_, 1);
lean_dec(v_unused_1221_);
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1220_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_toApplicative_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1220_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_toFunctor_1193_; lean_object* v_toSeq_1194_; lean_object* v_toSeqLeft_1195_; lean_object* v_toSeqRight_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1218_; 
v_toFunctor_1193_ = lean_ctor_get(v_toApplicative_1189_, 0);
v_toSeq_1194_ = lean_ctor_get(v_toApplicative_1189_, 2);
v_toSeqLeft_1195_ = lean_ctor_get(v_toApplicative_1189_, 3);
v_toSeqRight_1196_ = lean_ctor_get(v_toApplicative_1189_, 4);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_toApplicative_1189_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_toApplicative_1189_, 1);
lean_dec(v_unused_1219_);
v___x_1198_ = v_toApplicative_1189_;
v_isShared_1199_ = v_isSharedCheck_1218_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_toSeqRight_1196_);
lean_inc(v_toSeqLeft_1195_);
lean_inc(v_toSeq_1194_);
lean_inc(v_toFunctor_1193_);
lean_dec(v_toApplicative_1189_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1218_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1209_; 
v___f_1200_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1));
v___f_1201_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2));
lean_inc_ref(v_toFunctor_1193_);
v___f_1202_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1202_, 0, v_toFunctor_1193_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toFunctor_1193_);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___f_1202_);
lean_ctor_set(v___x_1204_, 1, v___f_1203_);
v___f_1205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1205_, 0, v_toSeqRight_1196_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toSeqLeft_1195_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toSeq_1194_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 4, v___f_1205_);
lean_ctor_set(v___x_1198_, 3, v___f_1206_);
lean_ctor_set(v___x_1198_, 2, v___f_1207_);
lean_ctor_set(v___x_1198_, 1, v___f_1200_);
lean_ctor_set(v___x_1198_, 0, v___x_1204_);
v___x_1209_ = v___x_1198_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___f_1200_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v___f_1207_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v___f_1206_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v___f_1205_);
v___x_1209_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___f_1201_);
lean_ctor_set(v___x_1191_, 0, v___x_1209_);
v___x_1211_ = v___x_1191_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___f_1201_);
v___x_1211_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_11904__overap_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = l_instInhabitedOfMonad___redArg(v___x_1211_, v___x_1212_);
v___x_11904__overap_1214_ = lean_panic_fn_borrowed(v___x_1213_, v_msg_1183_);
lean_dec(v___x_1213_);
lean_inc(v___y_1185_);
lean_inc_ref(v___y_1184_);
v___x_1215_ = lean_apply_3(v___x_11904__overap_1214_, v___y_1184_, v___y_1185_, lean_box(0));
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(lean_object* v_msg_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1226_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2));
v___x_1231_ = lean_unsigned_to_nat(21u);
v___x_1232_ = lean_unsigned_to_nat(65u);
v___x_1233_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1));
v___x_1234_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0));
v___x_1235_ = l_mkPanicMessageWithDecl(v___x_1234_, v___x_1233_, v___x_1232_, v___x_1231_, v___x_1230_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(lean_object* v_preNode_1236_, lean_object* v_postNode_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
switch(lean_obj_tag(v_x_1239_))
{
case 0:
{
lean_object* v_i_1243_; lean_object* v_t_1244_; lean_object* v___x_1245_; 
v_i_1243_ = lean_ctor_get(v_x_1239_, 0);
lean_inc_ref(v_i_1243_);
v_t_1244_ = lean_ctor_get(v_x_1239_, 1);
lean_inc_ref(v_t_1244_);
lean_dec_ref_known(v_x_1239_, 2);
v___x_1245_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1243_, v_x_1238_);
v_x_1238_ = v___x_1245_;
v_x_1239_ = v_t_1244_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1238_) == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec_ref_known(v_x_1239_, 2);
lean_dec_ref(v_postNode_1237_);
lean_dec_ref(v_preNode_1236_);
v___x_1247_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3);
v___x_1248_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v___x_1247_, v___y_1240_, v___y_1241_);
return v___x_1248_;
}
else
{
lean_object* v_i_1249_; lean_object* v_children_1250_; lean_object* v_val_1251_; lean_object* v___x_1252_; 
v_i_1249_ = lean_ctor_get(v_x_1239_, 0);
lean_inc_ref_n(v_i_1249_, 2);
v_children_1250_ = lean_ctor_get(v_x_1239_, 1);
lean_inc_ref_n(v_children_1250_, 2);
lean_dec_ref_known(v_x_1239_, 2);
v_val_1251_ = lean_ctor_get(v_x_1238_, 0);
lean_inc_n(v_val_1251_, 2);
lean_inc_ref(v_preNode_1236_);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
v___x_1252_ = lean_apply_6(v_preNode_1236_, v_val_1251_, v_i_1249_, v_children_1250_, v___y_1240_, v___y_1241_, lean_box(0));
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; uint8_t v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v___x_1254_ = lean_unbox(v_a_1253_);
lean_dec(v_a_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_preNode_1236_);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_x_1238_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v_x_1238_, 0);
lean_dec(v_unused_1280_);
v___x_1256_ = v_x_1238_;
v_isShared_1257_ = v_isSharedCheck_1279_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v_x_1238_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1279_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_box(0);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
v___x_1259_ = lean_apply_7(v_postNode_1237_, v_val_1251_, v_i_1249_, v_children_1250_, v___x_1258_, v___y_1240_, v___y_1241_, lean_box(0));
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1270_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1270_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1270_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v_a_1260_);
v___x_1265_ = v___x_1256_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1267_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1265_);
v___x_1267_ = v___x_1262_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_del_object(v___x_1256_);
v_a_1271_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1259_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1259_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1238_, v_i_1249_);
v___x_1282_ = l_Lean_PersistentArray_toList___redArg(v_children_1250_);
v___x_1283_ = lean_box(0);
lean_inc_ref(v_postNode_1237_);
v___x_1284_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1236_, v_postNode_1237_, v___x_1281_, v___x_1282_, v___x_1283_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
lean_inc(v___y_1241_);
lean_inc_ref(v___y_1240_);
v___x_1286_ = lean_apply_7(v_postNode_1237_, v_val_1251_, v_i_1249_, v_children_1250_, v_a_1285_, v___y_1240_, v___y_1241_, lean_box(0));
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_a_1287_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1291_);
v___x_1293_ = v___x_1289_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1286_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1286_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_val_1251_);
lean_dec_ref(v_children_1250_);
lean_dec_ref(v_i_1249_);
lean_dec_ref(v_postNode_1237_);
v_a_1304_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1284_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1284_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_val_1251_);
lean_dec_ref(v_children_1250_);
lean_dec_ref_known(v_x_1238_, 1);
lean_dec_ref(v_i_1249_);
lean_dec_ref(v_postNode_1237_);
lean_dec_ref(v_preNode_1236_);
v_a_1312_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1252_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1252_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
default: 
{
lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_x_1238_);
lean_dec_ref(v_postNode_1237_);
lean_dec_ref(v_preNode_1236_);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_x_1239_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_x_1239_, 0);
lean_dec(v_unused_1328_);
v___x_1321_ = v_x_1239_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v_x_1239_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_box(0);
if (v_isShared_1322_ == 0)
{
lean_ctor_set_tag(v___x_1321_, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(lean_object* v_preNode_1329_, lean_object* v_postNode_1330_, lean_object* v___x_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
if (lean_obj_tag(v_x_1332_) == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec(v___x_1331_);
lean_dec_ref(v_postNode_1330_);
lean_dec_ref(v_preNode_1329_);
v___x_1337_ = l_List_reverse___redArg(v_x_1333_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
else
{
lean_object* v_head_1339_; lean_object* v_tail_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1358_; 
v_head_1339_ = lean_ctor_get(v_x_1332_, 0);
v_tail_1340_ = lean_ctor_get(v_x_1332_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_x_1332_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1342_ = v_x_1332_;
v_isShared_1343_ = v_isSharedCheck_1358_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_tail_1340_);
lean_inc(v_head_1339_);
lean_dec(v_x_1332_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1358_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; 
lean_inc(v___x_1331_);
lean_inc_ref(v_postNode_1330_);
lean_inc_ref(v_preNode_1329_);
v___x_1344_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1329_, v_postNode_1330_, v___x_1331_, v_head_1339_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_x_1333_);
lean_ctor_set(v___x_1342_, 0, v_a_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1345_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_x_1333_);
v___x_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
v_x_1332_ = v_tail_1340_;
v_x_1333_ = v___x_1347_;
goto _start;
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_del_object(v___x_1342_);
lean_dec(v_tail_1340_);
lean_dec(v_x_1333_);
lean_dec(v___x_1331_);
lean_dec_ref(v_postNode_1330_);
lean_dec_ref(v_preNode_1329_);
v_a_1350_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1344_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1344_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(lean_object* v_preNode_1359_, lean_object* v_postNode_1360_, lean_object* v___x_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1359_, v_postNode_1360_, v___x_1361_, v_x_1362_, v_x_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(lean_object* v_preNode_1368_, lean_object* v_postNode_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1368_, v_postNode_1369_, v_x_1370_, v_x_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object* v_preNode_1376_, lean_object* v_postNode_1377_, lean_object* v_ctx_x3f_1378_, lean_object* v_t_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___f_1383_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1383_, 0, v_postNode_1377_);
v___x_1384_ = lean_box(0);
v___x_1385_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1376_, v___f_1383_, v_ctx_x3f_1378_, v_t_1379_, v___y_1380_, v___y_1381_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1393_);
v___x_1387_ = v___x_1385_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1385_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1384_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1384_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_a_1394_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1385_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1385_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object* v_preNode_1402_, lean_object* v_postNode_1403_, lean_object* v_ctx_x3f_1404_, lean_object* v_t_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v_preNode_1402_, v_postNode_1403_, v_ctx_x3f_1404_, v_t_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(uint8_t v___x_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = lean_box(v___x_1410_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object* v___x_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
uint8_t v___x_14087__boxed_1426_; lean_object* v_res_1427_; 
v___x_14087__boxed_1426_ = lean_unbox(v___x_1419_);
v_res_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v___x_14087__boxed_1426_, v_x_1420_, v_x_1421_, v_x_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec_ref(v_x_1422_);
lean_dec_ref(v_x_1421_);
lean_dec_ref(v_x_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(uint8_t v___x_1428_, lean_object* v_val_1429_, lean_object* v_as_1430_, size_t v_sz_1431_, size_t v_i_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_usize_dec_lt(v_i_1432_, v_sz_1431_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
lean_dec(v_val_1429_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v_b_1433_);
return v___x_1438_;
}
else
{
lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1439_ = lean_box(v___x_1428_);
v___f_1440_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1440_, 0, v___x_1439_);
v___x_1441_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
v___x_1442_ = lean_box(v___x_1428_);
lean_inc(v_val_1429_);
v___f_1443_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1443_, 0, v___x_1441_);
lean_closure_set(v___f_1443_, 1, v_val_1429_);
lean_closure_set(v___f_1443_, 2, v___x_1442_);
v___x_1444_ = lean_box(0);
v_a_1445_ = lean_array_uget_borrowed(v_as_1430_, v_i_1432_);
v___x_1446_ = lean_box(0);
lean_inc(v_a_1445_);
v___x_1447_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v___f_1440_, v___f_1443_, v___x_1446_, v_a_1445_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1447_) == 0)
{
size_t v___x_1448_; size_t v___x_1449_; 
lean_dec_ref_known(v___x_1447_, 1);
v___x_1448_ = ((size_t)1ULL);
v___x_1449_ = lean_usize_add(v_i_1432_, v___x_1448_);
v_i_1432_ = v___x_1449_;
v_b_1433_ = v___x_1444_;
goto _start;
}
else
{
lean_dec(v_val_1429_);
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object* v___x_1451_, lean_object* v_val_1452_, lean_object* v_as_1453_, lean_object* v_sz_1454_, lean_object* v_i_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___x_14112__boxed_1460_; size_t v_sz_boxed_1461_; size_t v_i_boxed_1462_; lean_object* v_res_1463_; 
v___x_14112__boxed_1460_ = lean_unbox(v___x_1451_);
v_sz_boxed_1461_ = lean_unbox_usize(v_sz_1454_);
lean_dec(v_sz_1454_);
v_i_boxed_1462_ = lean_unbox_usize(v_i_1455_);
lean_dec(v_i_1455_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_14112__boxed_1460_, v_val_1452_, v_as_1453_, v_sz_boxed_1461_, v_i_boxed_1462_, v_b_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec_ref(v_as_1453_);
return v_res_1463_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = lean_box(0);
v___x_1465_ = lean_unsigned_to_nat(16u);
v___x_1466_ = lean_mk_array(v___x_1465_, v___x_1464_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__0, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v___x_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0(lean_object* v_cmdStx_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1541_; 
v___x_1474_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_1471_, v___y_1472_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1541_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1541_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_1480_ = l_Lean_Linter_getLinterValue(v___x_1479_, v_a_1475_);
lean_dec(v_a_1475_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1481_ = lean_box(0);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1481_);
v___x_1483_ = v___x_1477_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
else
{
uint8_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = 0;
v___x_1486_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1470_, v___x_1485_);
if (lean_obj_tag(v___x_1486_) == 1)
{
lean_object* v___x_1487_; lean_object* v_infoState_1488_; lean_object* v_trees_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; size_t v_sz_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
lean_dec_ref_known(v___x_1486_, 1);
lean_del_object(v___x_1477_);
v___x_1487_ = lean_st_ref_get(v___y_1472_);
v_infoState_1488_ = lean_ctor_get(v___x_1487_, 8);
lean_inc_ref(v_infoState_1488_);
lean_dec(v___x_1487_);
v_trees_1489_ = lean_ctor_get(v_infoState_1488_, 2);
lean_inc_ref(v_trees_1489_);
lean_dec_ref(v_infoState_1488_);
v___x_1490_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1489_);
lean_dec_ref(v_trees_1489_);
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__1, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1);
v___x_1493_ = lean_st_mk_ref(v___x_1492_);
v___x_1494_ = lean_box(0);
v_sz_1495_ = lean_array_size(v___x_1490_);
v___x_1496_ = ((size_t)0ULL);
lean_inc(v___x_1493_);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_1480_, v___x_1493_, v___x_1490_, v_sz_1495_, v___x_1496_, v___x_1494_, v___y_1471_, v___y_1472_);
lean_dec_ref(v___x_1490_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; lean_object* v___y_1500_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1524_; lean_object* v_size_1530_; lean_object* v_buckets_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
lean_dec_ref_known(v___x_1497_, 1);
v___x_1498_ = lean_st_ref_get(v___x_1493_);
lean_dec(v___x_1493_);
v_size_1530_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_size_1530_);
v_buckets_1531_ = lean_ctor_get(v___x_1498_, 1);
lean_inc_ref(v_buckets_1531_);
lean_dec(v___x_1498_);
v___x_1532_ = lean_mk_empty_array_with_capacity(v_size_1530_);
lean_dec(v_size_1530_);
v___x_1533_ = lean_array_get_size(v_buckets_1531_);
v___x_1534_ = lean_nat_dec_lt(v___x_1491_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_dec_ref(v_buckets_1531_);
v___y_1524_ = v___x_1532_;
goto v___jp_1523_;
}
else
{
size_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_usize_of_nat(v___x_1533_);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_1531_, v___x_1496_, v___x_1535_, v___x_1532_);
lean_dec_ref(v_buckets_1531_);
v___y_1524_ = v___x_1536_;
goto v___jp_1523_;
}
v___jp_1499_:
{
size_t v_sz_1501_; lean_object* v___x_1502_; 
v_sz_1501_ = lean_array_size(v___y_1500_);
v___x_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___y_1500_, v_sz_1501_, v___x_1496_, v___x_1494_, v___y_1471_, v___y_1472_);
lean_dec_ref(v___y_1500_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v___x_1502_, 0);
lean_dec(v_unused_1510_);
v___x_1504_ = v___x_1502_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_dec(v___x_1502_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1494_);
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1494_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
else
{
return v___x_1502_;
}
}
v___jp_1511_:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v___y_1513_, v___y_1514_, v___y_1512_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec(v___y_1513_);
v___y_1500_ = v___x_1516_;
goto v___jp_1499_;
}
v___jp_1517_:
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_nat_dec_le(v___y_1521_, v___y_1518_);
if (v___x_1522_ == 0)
{
lean_dec(v___y_1518_);
lean_inc(v___y_1521_);
v___y_1512_ = v___y_1521_;
v___y_1513_ = v___y_1519_;
v___y_1514_ = v___y_1520_;
v___y_1515_ = v___y_1521_;
goto v___jp_1511_;
}
else
{
v___y_1512_ = v___y_1521_;
v___y_1513_ = v___y_1519_;
v___y_1514_ = v___y_1520_;
v___y_1515_ = v___y_1518_;
goto v___jp_1511_;
}
}
v___jp_1523_:
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = lean_array_get_size(v___y_1524_);
v___x_1526_ = lean_nat_dec_eq(v___x_1525_, v___x_1491_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_nat_sub(v___x_1525_, v___x_1527_);
v___x_1529_ = lean_nat_dec_le(v___x_1491_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_inc(v___x_1528_);
v___y_1518_ = v___x_1528_;
v___y_1519_ = v___x_1525_;
v___y_1520_ = v___y_1524_;
v___y_1521_ = v___x_1528_;
goto v___jp_1517_;
}
else
{
v___y_1518_ = v___x_1528_;
v___y_1519_ = v___x_1525_;
v___y_1520_ = v___y_1524_;
v___y_1521_ = v___x_1491_;
goto v___jp_1517_;
}
}
else
{
v___y_1500_ = v___y_1524_;
goto v___jp_1499_;
}
}
}
else
{
lean_dec(v___x_1493_);
return v___x_1497_;
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1539_; 
lean_dec(v___x_1486_);
v___x_1537_ = lean_box(0);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1537_);
v___x_1539_ = v___x_1477_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___boxed(lean_object* v_cmdStx_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v_cmdStx_1542_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(lean_object* v_o_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_1558_, v___y_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(lean_object* v_o_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object* v_00_u03b2_1568_, lean_object* v_m_1569_, lean_object* v_a_1570_, lean_object* v_b_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_1569_, v_a_1570_, v_b_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object* v_00_u03b2_1573_, lean_object* v_m_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_1574_, v_a_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object* v_00_u03b2_1577_, lean_object* v_m_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(v_00_u03b2_1577_, v_m_1578_, v_a_1579_);
lean_dec_ref(v_a_1579_);
lean_dec_ref(v_m_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(lean_object* v_00_u03b1_1581_, lean_object* v_ref_1582_, lean_object* v_msg_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_1582_, v_msg_1583_, v___y_1584_, v___y_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_ref_1589_, lean_object* v_msg_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(v_00_u03b1_1588_, v_ref_1589_, v_msg_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v_ref_1589_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object* v_upperBound_1595_, lean_object* v_snd_1596_, lean_object* v_fst_1597_, lean_object* v_inst_1598_, lean_object* v_R_1599_, lean_object* v_a_1600_, lean_object* v_b_1601_, lean_object* v_c_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_1595_, v_snd_1596_, v_fst_1597_, v_a_1600_, v_b_1601_, v___y_1603_, v___y_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object* v_upperBound_1607_, lean_object* v_snd_1608_, lean_object* v_fst_1609_, lean_object* v_inst_1610_, lean_object* v_R_1611_, lean_object* v_a_1612_, lean_object* v_b_1613_, lean_object* v_c_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(v_upperBound_1607_, v_snd_1608_, v_fst_1609_, v_inst_1610_, v_R_1611_, v_a_1612_, v_b_1613_, v_c_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec_ref(v_snd_1608_);
lean_dec(v_upperBound_1607_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object* v_n_1619_, lean_object* v_as_1620_, lean_object* v_lo_1621_, lean_object* v_hi_1622_, lean_object* v_w_1623_, lean_object* v_hlo_1624_, lean_object* v_hhi_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_1619_, v_as_1620_, v_lo_1621_, v_hi_1622_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object* v_n_1627_, lean_object* v_as_1628_, lean_object* v_lo_1629_, lean_object* v_hi_1630_, lean_object* v_w_1631_, lean_object* v_hlo_1632_, lean_object* v_hhi_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(v_n_1627_, v_as_1628_, v_lo_1629_, v_hi_1630_, v_w_1631_, v_hlo_1632_, v_hhi_1633_);
lean_dec(v_hi_1630_);
lean_dec(v_n_1627_);
return v_res_1634_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object* v_00_u03b2_1635_, lean_object* v_a_1636_, lean_object* v_x_1637_){
_start:
{
uint8_t v___x_1638_; 
v___x_1638_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1636_, v_x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1639_, lean_object* v_a_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_1639_, v_a_1640_, v_x_1641_);
lean_dec(v_x_1641_);
lean_dec_ref(v_a_1640_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(lean_object* v_00_u03b2_1644_, lean_object* v_data_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_data_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(lean_object* v_00_u03b2_1647_, lean_object* v_a_1648_, lean_object* v_b_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1648_, v_b_1649_, v_x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(lean_object* v_00_u03b2_1652_, lean_object* v_a_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_1653_, v_x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1656_, lean_object* v_a_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(v_00_u03b2_1656_, v_a_1657_, v_x_1658_);
lean_dec(v_x_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(lean_object* v_msgData_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_1660_, v___y_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(lean_object* v_msgData_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(lean_object* v_00_u03b1_1670_, lean_object* v_msg_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_1671_, v___y_1672_, v___y_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1676_, lean_object* v_msg_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(v_00_u03b1_1676_, v_msg_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_object* v_00_u03b1_1682_, lean_object* v_msg_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1683_, v___y_1684_, v___y_1685_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1688_, lean_object* v_msg_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(v_00_u03b1_1688_, v_msg_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_object* v_00_u03b1_1694_, lean_object* v_preNode_1695_, lean_object* v_postNode_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1695_, v_postNode_1696_, v_x_1697_, v_x_1698_, v___y_1699_, v___y_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_preNode_1704_, lean_object* v_postNode_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(v_00_u03b1_1703_, v_preNode_1704_, v_postNode_1705_, v_x_1706_, v_x_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(lean_object* v_n_1712_, lean_object* v_lo_1713_, lean_object* v_hi_1714_, lean_object* v_hhi_1715_, lean_object* v_pivot_1716_, lean_object* v_as_1717_, lean_object* v_i_1718_, lean_object* v_k_1719_, lean_object* v_ilo_1720_, lean_object* v_ik_1721_, lean_object* v_w_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_1714_, v_pivot_1716_, v_as_1717_, v_i_1718_, v_k_1719_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(lean_object* v_n_1724_, lean_object* v_lo_1725_, lean_object* v_hi_1726_, lean_object* v_hhi_1727_, lean_object* v_pivot_1728_, lean_object* v_as_1729_, lean_object* v_i_1730_, lean_object* v_k_1731_, lean_object* v_ilo_1732_, lean_object* v_ik_1733_, lean_object* v_w_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(v_n_1724_, v_lo_1725_, v_hi_1726_, v_hhi_1727_, v_pivot_1728_, v_as_1729_, v_i_1730_, v_k_1731_, v_ilo_1732_, v_ik_1733_, v_w_1734_);
lean_dec_ref(v_pivot_1728_);
lean_dec(v_hi_1726_);
lean_dec(v_lo_1725_);
lean_dec(v_n_1724_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1736_, lean_object* v_i_1737_, lean_object* v_source_1738_, lean_object* v_target_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v_i_1737_, v_source_1738_, v_target_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(lean_object* v_msgData_1741_, lean_object* v_macroStack_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_1741_, v_macroStack_1742_, v___y_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_1747_, lean_object* v_macroStack_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_1747_, v_macroStack_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_object* v_00_u03b1_1753_, lean_object* v_preNode_1754_, lean_object* v_postNode_1755_, lean_object* v___x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1754_, v_postNode_1755_, v___x_1756_, v_x_1757_, v_x_1758_, v___y_1759_, v___y_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(lean_object* v_00_u03b1_1763_, lean_object* v_preNode_1764_, lean_object* v_postNode_1765_, lean_object* v___x_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(v_00_u03b1_1763_, v_preNode_1764_, v_postNode_1765_, v___x_1766_, v_x_1767_, v_x_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1773_, lean_object* v_x_1774_, lean_object* v_x_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_x_1774_, v_x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_Linter_unusedSimpArgs));
v___x_1779_ = l_Lean_Elab_Command_addLinter(v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
return v_res_1781_;
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
