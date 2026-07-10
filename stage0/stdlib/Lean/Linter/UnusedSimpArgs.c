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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_linter_unusedSimpArgs;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_getSimpParams(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
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
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Simp argument mask size mismatch}: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " vs. "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpAll"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(5, 49, 55, 92, 153, 191, 153, 249)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__8_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__9_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_nat_dec_eq(v_a_4_, v_i_2_);
v___x_15_ = lean_bool_not(v___x_14_);
if (v___x_15_ == 0)
{
v_a_8_ = v_b_5_;
goto v___jp_7_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_array_fget_borrowed(v_simpArgs_3_, v_a_4_);
lean_inc(v___x_16_);
v___x_17_ = lean_array_push(v_b_5_, v___x_16_);
v_a_8_ = v___x_17_;
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
v___x_25_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__1);
v___x_29_ = lean_unsigned_to_nat(0u);
v___x_30_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_48_; lean_object* v_env_49_; lean_object* v_options_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_48_ = lean_st_ref_get(v___y_46_);
v_env_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc_ref(v_env_49_);
lean_dec(v___x_48_);
v_options_50_ = lean_ctor_get(v___y_45_, 2);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_52_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
lean_inc_ref(v_options_50_);
v___x_53_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_53_, 0, v_env_49_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
lean_ctor_set(v___x_53_, 2, v___x_52_);
lean_ctor_set(v___x_53_, 3, v_options_50_);
v___x_54_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_msgData_44_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___boxed(lean_object* v_msgData_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msgData_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(lean_object* v_msg_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_ref_65_; lean_object* v___x_66_; lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_ref_65_ = lean_ctor_get(v___y_62_, 5);
v___x_66_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v_msg_61_, v___y_62_, v___y_63_);
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_75_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
lean_inc(v_ref_65_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v_ref_65_);
lean_ctor_set(v___x_71_, 1, v_a_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 1);
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg___boxed(lean_object* v_msg_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_80_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_89_, uint8_t v_suppressElabErrors_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 1)
{
lean_object* v_pre_92_; 
v_pre_92_ = lean_ctor_get(v_x_91_, 0);
switch(lean_obj_tag(v_pre_92_))
{
case 1:
{
lean_object* v_pre_93_; 
v_pre_93_ = lean_ctor_get(v_pre_92_, 0);
switch(lean_obj_tag(v_pre_93_))
{
case 0:
{
lean_object* v_str_94_; lean_object* v_str_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_str_94_ = lean_ctor_get(v_x_91_, 1);
v_str_95_ = lean_ctor_get(v_pre_92_, 1);
v___x_96_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_97_ = lean_string_dec_eq(v_str_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_99_ = lean_string_dec_eq(v_str_95_, v___x_98_);
if (v___x_99_ == 0)
{
return v___y_89_;
}
else
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_101_ = lean_string_dec_eq(v_str_94_, v___x_100_);
if (v___x_101_ == 0)
{
return v___y_89_;
}
else
{
return v_suppressElabErrors_90_;
}
}
}
else
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_103_ = lean_string_dec_eq(v_str_94_, v___x_102_);
if (v___x_103_ == 0)
{
return v___y_89_;
}
else
{
return v_suppressElabErrors_90_;
}
}
}
case 1:
{
lean_object* v_pre_104_; 
v_pre_104_ = lean_ctor_get(v_pre_93_, 0);
if (lean_obj_tag(v_pre_104_) == 0)
{
lean_object* v_str_105_; lean_object* v_str_106_; lean_object* v_str_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_str_105_ = lean_ctor_get(v_x_91_, 1);
v_str_106_ = lean_ctor_get(v_pre_92_, 1);
v_str_107_ = lean_ctor_get(v_pre_93_, 1);
v___x_108_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_109_ = lean_string_dec_eq(v_str_107_, v___x_108_);
if (v___x_109_ == 0)
{
return v___y_89_;
}
else
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_111_ = lean_string_dec_eq(v_str_106_, v___x_110_);
if (v___x_111_ == 0)
{
return v___y_89_;
}
else
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_113_ = lean_string_dec_eq(v_str_105_, v___x_112_);
if (v___x_113_ == 0)
{
return v___y_89_;
}
else
{
return v_suppressElabErrors_90_;
}
}
}
}
else
{
return v___y_89_;
}
}
default: 
{
return v___y_89_;
}
}
}
case 0:
{
lean_object* v_str_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v_str_114_ = lean_ctor_get(v_x_91_, 1);
v___x_115_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_116_ = lean_string_dec_eq(v_str_114_, v___x_115_);
if (v___x_116_ == 0)
{
return v___y_89_;
}
else
{
return v_suppressElabErrors_90_;
}
}
default: 
{
return v___y_89_;
}
}
}
else
{
return v___y_89_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_117_, lean_object* v_suppressElabErrors_118_, lean_object* v_x_119_){
_start:
{
uint8_t v___y_4572__boxed_120_; uint8_t v_suppressElabErrors_boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v___y_4572__boxed_120_ = lean_unbox(v___y_117_);
v_suppressElabErrors_boxed_121_ = lean_unbox(v_suppressElabErrors_118_);
v_res_122_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v___y_4572__boxed_120_, v_suppressElabErrors_boxed_121_, v_x_119_);
lean_dec(v_x_119_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_124_, lean_object* v_opt_125_){
_start:
{
lean_object* v_name_126_; lean_object* v_defValue_127_; lean_object* v_map_128_; lean_object* v___x_129_; 
v_name_126_ = lean_ctor_get(v_opt_125_, 0);
v_defValue_127_ = lean_ctor_get(v_opt_125_, 1);
v_map_128_ = lean_ctor_get(v_opts_124_, 0);
v___x_129_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_128_, v_name_126_);
if (lean_obj_tag(v___x_129_) == 0)
{
uint8_t v___x_130_; 
v___x_130_ = lean_unbox(v_defValue_127_);
return v___x_130_;
}
else
{
lean_object* v_val_131_; 
v_val_131_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_val_131_);
lean_dec_ref_known(v___x_129_, 1);
if (lean_obj_tag(v_val_131_) == 1)
{
uint8_t v_v_132_; 
v_v_132_ = lean_ctor_get_uint8(v_val_131_, 0);
lean_dec_ref_known(v_val_131_, 0);
return v_v_132_;
}
else
{
uint8_t v___x_133_; 
lean_dec(v_val_131_);
v___x_133_ = lean_unbox(v_defValue_127_);
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_134_, lean_object* v_opt_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_134_, v_opt_135_);
lean_dec_ref(v_opt_135_);
lean_dec_ref(v_opts_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(lean_object* v_ref_139_, lean_object* v_msgData_140_, uint8_t v_severity_141_, uint8_t v_isSilent_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
uint8_t v___y_147_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; lean_object* v___y_151_; lean_object* v___y_152_; uint8_t v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___y_183_; uint8_t v___y_184_; uint8_t v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; uint8_t v___y_189_; lean_object* v___y_190_; lean_object* v___y_208_; uint8_t v___y_209_; lean_object* v___y_210_; uint8_t v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; uint8_t v___y_214_; lean_object* v___y_215_; lean_object* v___y_219_; uint8_t v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; uint8_t v___y_225_; uint8_t v___x_230_; lean_object* v___y_232_; uint8_t v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; uint8_t v___y_237_; uint8_t v___y_238_; uint8_t v___y_240_; uint8_t v___x_255_; 
v___x_230_ = 2;
v___x_255_ = l_Lean_instBEqMessageSeverity_beq(v_severity_141_, v___x_230_);
if (v___x_255_ == 0)
{
v___y_240_ = v___x_255_;
goto v___jp_239_;
}
else
{
uint8_t v___x_256_; 
lean_inc_ref(v_msgData_140_);
v___x_256_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_140_);
v___y_240_ = v___x_256_;
goto v___jp_239_;
}
v___jp_146_:
{
lean_object* v___x_156_; lean_object* v_currNamespace_157_; lean_object* v_openDecls_158_; lean_object* v_env_159_; lean_object* v_nextMacroScope_160_; lean_object* v_ngen_161_; lean_object* v_auxDeclNGen_162_; lean_object* v_traceState_163_; lean_object* v_cache_164_; lean_object* v_messages_165_; lean_object* v_infoState_166_; lean_object* v_snapshotTasks_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_181_; 
v___x_156_ = lean_st_ref_take(v___y_155_);
v_currNamespace_157_ = lean_ctor_get(v___y_154_, 6);
v_openDecls_158_ = lean_ctor_get(v___y_154_, 7);
v_env_159_ = lean_ctor_get(v___x_156_, 0);
v_nextMacroScope_160_ = lean_ctor_get(v___x_156_, 1);
v_ngen_161_ = lean_ctor_get(v___x_156_, 2);
v_auxDeclNGen_162_ = lean_ctor_get(v___x_156_, 3);
v_traceState_163_ = lean_ctor_get(v___x_156_, 4);
v_cache_164_ = lean_ctor_get(v___x_156_, 5);
v_messages_165_ = lean_ctor_get(v___x_156_, 6);
v_infoState_166_ = lean_ctor_get(v___x_156_, 7);
v_snapshotTasks_167_ = lean_ctor_get(v___x_156_, 8);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_181_ == 0)
{
v___x_169_ = v___x_156_;
v_isShared_170_ = v_isSharedCheck_181_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_snapshotTasks_167_);
lean_inc(v_infoState_166_);
lean_inc(v_messages_165_);
lean_inc(v_cache_164_);
lean_inc(v_traceState_163_);
lean_inc(v_auxDeclNGen_162_);
lean_inc(v_ngen_161_);
lean_inc(v_nextMacroScope_160_);
lean_inc(v_env_159_);
lean_dec(v___x_156_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_181_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
lean_inc(v_openDecls_158_);
lean_inc(v_currNamespace_157_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_currNamespace_157_);
lean_ctor_set(v___x_171_, 1, v_openDecls_158_);
v___x_172_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___y_148_);
lean_inc_ref(v___y_151_);
lean_inc_ref(v___y_150_);
v___x_173_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_173_, 0, v___y_150_);
lean_ctor_set(v___x_173_, 1, v___y_152_);
lean_ctor_set(v___x_173_, 2, v___y_149_);
lean_ctor_set(v___x_173_, 3, v___y_151_);
lean_ctor_set(v___x_173_, 4, v___x_172_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*5, v___y_147_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*5 + 1, v___y_153_);
lean_ctor_set_uint8(v___x_173_, sizeof(void*)*5 + 2, v_isSilent_142_);
v___x_174_ = l_Lean_MessageLog_add(v___x_173_, v_messages_165_);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 6, v___x_174_);
v___x_176_ = v___x_169_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_env_159_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_nextMacroScope_160_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v_ngen_161_);
lean_ctor_set(v_reuseFailAlloc_180_, 3, v_auxDeclNGen_162_);
lean_ctor_set(v_reuseFailAlloc_180_, 4, v_traceState_163_);
lean_ctor_set(v_reuseFailAlloc_180_, 5, v_cache_164_);
lean_ctor_set(v_reuseFailAlloc_180_, 6, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_180_, 7, v_infoState_166_);
lean_ctor_set(v_reuseFailAlloc_180_, 8, v_snapshotTasks_167_);
v___x_176_ = v_reuseFailAlloc_180_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_st_ref_set(v___y_155_, v___x_176_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
}
}
v___jp_182_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_206_; 
v___x_191_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_140_);
v___x_192_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v___x_191_, v___y_143_, v___y_144_);
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_206_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_206_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_206_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
lean_inc_ref_n(v___y_187_, 2);
v___x_197_ = l_Lean_FileMap_toPosition(v___y_187_, v___y_188_);
lean_dec(v___y_188_);
v___x_198_ = l_Lean_FileMap_toPosition(v___y_187_, v___y_190_);
lean_dec(v___y_190_);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
v___x_200_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0));
if (v___y_184_ == 0)
{
lean_del_object(v___x_195_);
lean_dec_ref(v___y_183_);
v___y_147_ = v___y_185_;
v___y_148_ = v_a_193_;
v___y_149_ = v___x_199_;
v___y_150_ = v___y_186_;
v___y_151_ = v___x_200_;
v___y_152_ = v___x_197_;
v___y_153_ = v___y_189_;
v___y_154_ = v___y_143_;
v___y_155_ = v___y_144_;
goto v___jp_146_;
}
else
{
uint8_t v___x_201_; 
lean_inc(v_a_193_);
v___x_201_ = l_Lean_MessageData_hasTag(v___y_183_, v_a_193_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec_ref_known(v___x_199_, 1);
lean_dec_ref(v___x_197_);
lean_dec(v_a_193_);
v___x_202_ = lean_box(0);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_202_);
v___x_204_ = v___x_195_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
else
{
lean_del_object(v___x_195_);
v___y_147_ = v___y_185_;
v___y_148_ = v_a_193_;
v___y_149_ = v___x_199_;
v___y_150_ = v___y_186_;
v___y_151_ = v___x_200_;
v___y_152_ = v___x_197_;
v___y_153_ = v___y_189_;
v___y_154_ = v___y_143_;
v___y_155_ = v___y_144_;
goto v___jp_146_;
}
}
}
}
v___jp_207_:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Syntax_getTailPos_x3f(v___y_210_, v___y_211_);
lean_dec(v___y_210_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_inc(v___y_215_);
v___y_183_ = v___y_208_;
v___y_184_ = v___y_209_;
v___y_185_ = v___y_211_;
v___y_186_ = v___y_212_;
v___y_187_ = v___y_213_;
v___y_188_ = v___y_215_;
v___y_189_ = v___y_214_;
v___y_190_ = v___y_215_;
goto v___jp_182_;
}
else
{
lean_object* v_val_217_; 
v_val_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v___x_216_, 1);
v___y_183_ = v___y_208_;
v___y_184_ = v___y_209_;
v___y_185_ = v___y_211_;
v___y_186_ = v___y_212_;
v___y_187_ = v___y_213_;
v___y_188_ = v___y_215_;
v___y_189_ = v___y_214_;
v___y_190_ = v_val_217_;
goto v___jp_182_;
}
}
v___jp_218_:
{
lean_object* v_ref_226_; lean_object* v___x_227_; 
v_ref_226_ = l_Lean_replaceRef(v_ref_139_, v___y_224_);
v___x_227_ = l_Lean_Syntax_getPos_x3f(v_ref_226_, v___y_221_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___y_208_ = v___y_219_;
v___y_209_ = v___y_220_;
v___y_210_ = v_ref_226_;
v___y_211_ = v___y_221_;
v___y_212_ = v___y_222_;
v___y_213_ = v___y_223_;
v___y_214_ = v___y_225_;
v___y_215_ = v___x_228_;
goto v___jp_207_;
}
else
{
lean_object* v_val_229_; 
v_val_229_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v___x_227_, 1);
v___y_208_ = v___y_219_;
v___y_209_ = v___y_220_;
v___y_210_ = v_ref_226_;
v___y_211_ = v___y_221_;
v___y_212_ = v___y_222_;
v___y_213_ = v___y_223_;
v___y_214_ = v___y_225_;
v___y_215_ = v_val_229_;
goto v___jp_207_;
}
}
v___jp_231_:
{
if (v___y_238_ == 0)
{
v___y_219_ = v___y_232_;
v___y_220_ = v___y_233_;
v___y_221_ = v___y_237_;
v___y_222_ = v___y_234_;
v___y_223_ = v___y_235_;
v___y_224_ = v___y_236_;
v___y_225_ = v_severity_141_;
goto v___jp_218_;
}
else
{
v___y_219_ = v___y_232_;
v___y_220_ = v___y_233_;
v___y_221_ = v___y_237_;
v___y_222_ = v___y_234_;
v___y_223_ = v___y_235_;
v___y_224_ = v___y_236_;
v___y_225_ = v___x_230_;
goto v___jp_218_;
}
}
v___jp_239_:
{
if (v___y_240_ == 0)
{
lean_object* v_fileName_241_; lean_object* v_fileMap_242_; lean_object* v_options_243_; lean_object* v_ref_244_; uint8_t v_suppressElabErrors_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___f_248_; uint8_t v___x_249_; uint8_t v___x_250_; 
v_fileName_241_ = lean_ctor_get(v___y_143_, 0);
v_fileMap_242_ = lean_ctor_get(v___y_143_, 1);
v_options_243_ = lean_ctor_get(v___y_143_, 2);
v_ref_244_ = lean_ctor_get(v___y_143_, 5);
v_suppressElabErrors_245_ = lean_ctor_get_uint8(v___y_143_, sizeof(void*)*14 + 1);
v___x_246_ = lean_box(v___y_240_);
v___x_247_ = lean_box(v_suppressElabErrors_245_);
v___f_248_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_248_, 0, v___x_246_);
lean_closure_set(v___f_248_, 1, v___x_247_);
v___x_249_ = 1;
v___x_250_ = l_Lean_instBEqMessageSeverity_beq(v_severity_141_, v___x_249_);
if (v___x_250_ == 0)
{
v___y_232_ = v___f_248_;
v___y_233_ = v_suppressElabErrors_245_;
v___y_234_ = v_fileName_241_;
v___y_235_ = v_fileMap_242_;
v___y_236_ = v_ref_244_;
v___y_237_ = v___y_240_;
v___y_238_ = v___x_250_;
goto v___jp_231_;
}
else
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = l_Lean_warningAsError;
v___x_252_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_options_243_, v___x_251_);
v___y_232_ = v___f_248_;
v___y_233_ = v_suppressElabErrors_245_;
v___y_234_ = v_fileName_241_;
v___y_235_ = v_fileMap_242_;
v___y_236_ = v_ref_244_;
v___y_237_ = v___y_240_;
v___y_238_ = v___x_252_;
goto v___jp_231_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref(v_msgData_140_);
v___x_253_ = lean_box(0);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_257_, lean_object* v_msgData_258_, lean_object* v_severity_259_, lean_object* v_isSilent_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
uint8_t v_severity_boxed_264_; uint8_t v_isSilent_boxed_265_; lean_object* v_res_266_; 
v_severity_boxed_264_ = lean_unbox(v_severity_259_);
v_isSilent_boxed_265_ = lean_unbox(v_isSilent_260_);
v_res_266_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_257_, v_msgData_258_, v_severity_boxed_264_, v_isSilent_boxed_265_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v_ref_257_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(lean_object* v_ref_267_, lean_object* v_msgData_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
uint8_t v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = 1;
v___x_273_ = 0;
v___x_274_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_267_, v_msgData_268_, v___x_272_, v___x_273_, v___y_269_, v___y_270_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(lean_object* v_ref_275_, lean_object* v_msgData_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_275_, v_msgData_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v_ref_275_);
return v_res_280_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0));
v___x_283_ = l_Lean_stringToMessageData(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2));
v___x_286_ = l_Lean_stringToMessageData(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(lean_object* v_linterOption_287_, lean_object* v_stx_288_, lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_name_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_311_; 
v_name_293_ = lean_ctor_get(v_linterOption_287_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_linterOption_287_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v_linterOption_287_, 1);
lean_dec(v_unused_312_);
v___x_295_ = v_linterOption_287_;
v_isShared_296_ = v_isSharedCheck_311_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_name_293_);
lean_dec(v_linterOption_287_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_311_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_297_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1);
lean_inc(v_name_293_);
v___x_298_ = l_Lean_MessageData_ofName(v_name_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 7);
lean_ctor_set(v___x_295_, 1, v___x_298_);
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_300_ = v___x_295_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_310_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_disable_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_301_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3);
v___x_302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
v_disable_303_ = l_Lean_MessageData_note(v___x_302_);
v___x_304_ = l_Lean_Linter_linterMessageTag;
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v_msg_289_);
lean_ctor_set(v___x_305_, 1, v_disable_303_);
v___x_306_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_307_, 0, v_name_293_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
lean_inc(v_stx_288_);
v___x_308_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_308_, 0, v_stx_288_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_stx_288_, v___x_308_, v___y_290_, v___y_291_);
lean_dec(v_stx_288_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(lean_object* v_linterOption_313_, lean_object* v_stx_314_, lean_object* v_msg_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_313_, v_stx_314_, v_msg_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_319_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4));
v___x_329_ = l_Lean_MessageData_ofFormat(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6));
v___x_332_ = l_Lean_stringToMessageData(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12));
v___x_343_ = l_Lean_stringToMessageData(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13);
v___x_345_ = l_Lean_MessageData_note(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15));
v___x_348_ = l_Lean_stringToMessageData(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(lean_object* v_stx_352_, lean_object* v_i_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v_hint_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_simpArgs_368_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_366_ = lean_box(0);
v___x_367_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1));
v_simpArgs_368_ = l_Lean_Elab_Tactic_getSimpParams(v_stx_352_);
v___x_420_ = lean_array_get_size(v_simpArgs_368_);
v___x_421_ = lean_nat_dec_lt(v_i_353_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v_simpArgs_368_);
v___x_422_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16);
v___x_423_ = l_Nat_reprFast(v_i_353_);
v___x_424_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
v___x_425_ = l_Lean_MessageData_ofFormat(v___x_424_);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_422_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_MessageData_ofSyntax(v_stx_352_);
v___x_430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_428_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v___x_430_, v_a_354_, v_a_355_);
return v___x_431_;
}
else
{
v___y_370_ = v_a_354_;
v___y_371_ = v_a_355_;
goto v___jp_369_;
}
v___jp_357_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___y_359_);
lean_ctor_set(v___x_364_, 1, v_hint_360_);
v___x_365_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_363_, v___y_358_, v___x_364_, v___y_361_, v___y_362_);
return v___x_365_;
}
v___jp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_argStx_374_; lean_object* v_otherArgs_375_; lean_object* v___x_376_; 
v___x_372_ = lean_array_get_size(v_simpArgs_368_);
v___x_373_ = lean_unsigned_to_nat(0u);
v_argStx_374_ = lean_array_get(v___x_366_, v_simpArgs_368_, v_i_353_);
v_otherArgs_375_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2));
v___x_376_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v___x_372_, v_i_353_, v_simpArgs_368_, v___x_373_, v_otherArgs_375_);
lean_dec_ref(v_simpArgs_368_);
lean_dec(v_i_353_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
lean_inc(v_a_377_);
lean_dec_ref_known(v___x_376_, 1);
lean_inc(v_stx_352_);
v___x_378_ = l_Lean_Elab_Tactic_setSimpParams(v_stx_352_, v_a_377_);
lean_dec(v_a_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_367_);
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
lean_ctor_set(v___x_382_, 0, v_stx_352_);
v___x_383_ = 4;
v___x_384_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_384_, 0, v___x_381_);
lean_ctor_set(v___x_384_, 1, v___x_382_);
lean_ctor_set(v___x_384_, 2, v___x_380_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*3, v___x_383_);
v___x_385_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__5);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_mk_empty_array_with_capacity(v___x_386_);
v___x_388_ = lean_array_push(v___x_387_, v___x_384_);
v___x_389_ = 0;
v___x_390_ = l_Lean_MessageData_hint(v___x_385_, v___x_388_, v___x_380_, v___x_380_, v___x_389_, v___y_370_, v___y_371_);
lean_dec_ref(v___x_388_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_msg_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7);
lean_inc_n(v_argStx_374_, 2);
v___x_393_ = l_Lean_MessageData_ofSyntax(v_argStx_374_);
v___x_394_ = l_Lean_indentD(v___x_393_);
v_msg_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_395_, 0, v___x_392_);
lean_ctor_set(v_msg_395_, 1, v___x_394_);
v___x_396_ = l_Lean_Syntax_getKind(v_argStx_374_);
v___x_397_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11));
v___x_398_ = lean_name_eq(v___x_396_, v___x_397_);
lean_dec(v___x_396_);
if (v___x_398_ == 0)
{
v___y_358_ = v_argStx_374_;
v___y_359_ = v_msg_395_;
v_hint_360_ = v_a_391_;
v___y_361_ = v___y_370_;
v___y_362_ = v___y_371_;
goto v___jp_357_;
}
else
{
lean_object* v___x_399_; uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_399_ = l_Lean_Syntax_getArg(v_argStx_374_, v___x_386_);
v___x_400_ = l_Lean_Syntax_isNone(v___x_399_);
lean_dec(v___x_399_);
v___x_401_ = lean_bool_not(v___x_400_);
if (v___x_401_ == 0)
{
v___y_358_ = v_argStx_374_;
v___y_359_ = v_msg_395_;
v_hint_360_ = v_a_391_;
v___y_361_ = v___y_370_;
v___y_362_ = v___y_371_;
goto v___jp_357_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v_a_391_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___y_358_ = v_argStx_374_;
v___y_359_ = v_msg_395_;
v_hint_360_ = v___x_403_;
v___y_361_ = v___y_370_;
v___y_362_ = v___y_371_;
goto v___jp_357_;
}
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_argStx_374_);
v_a_404_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_390_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_390_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_argStx_374_);
lean_dec(v_stx_352_);
v_a_412_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_376_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_376_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed(lean_object* v_stx_432_, lean_object* v_i_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(v_stx_432_, v_i_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(lean_object* v_upperBound_438_, lean_object* v_i_439_, lean_object* v_simpArgs_440_, lean_object* v_inst_441_, lean_object* v_R_442_, lean_object* v_a_443_, lean_object* v_b_444_, lean_object* v_c_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_438_, v_i_439_, v_simpArgs_440_, v_a_443_, v_b_444_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(lean_object* v_upperBound_450_, lean_object* v_i_451_, lean_object* v_simpArgs_452_, lean_object* v_inst_453_, lean_object* v_R_454_, lean_object* v_a_455_, lean_object* v_b_456_, lean_object* v_c_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_450_, v_i_451_, v_simpArgs_452_, v_inst_453_, v_R_454_, v_a_455_, v_b_456_, v_c_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec_ref(v_simpArgs_452_);
lean_dec(v_i_451_);
lean_dec(v_upperBound_450_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(lean_object* v_00_u03b1_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_463_, v___y_464_, v___y_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(lean_object* v_00_u03b1_468_, lean_object* v_msg_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(v_00_u03b1_468_, v_msg_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object* v_upperBound_474_, lean_object* v_snd_475_, lean_object* v_fst_476_, lean_object* v_a_477_, lean_object* v_b_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_a_483_; uint8_t v___x_487_; 
v___x_487_ = lean_nat_dec_lt(v_a_477_, v_upperBound_474_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec(v_a_477_);
lean_dec(v_fst_476_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v_b_478_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_489_ = lean_box(0);
v___x_490_ = 0;
v___x_491_ = lean_box(v___x_490_);
v___x_492_ = lean_array_get(v___x_491_, v_snd_475_, v_a_477_);
lean_dec(v___x_491_);
v___x_493_ = lean_unbox(v___x_492_);
lean_dec(v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_inc(v_a_477_);
lean_inc(v_fst_476_);
v___x_494_ = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed), 5, 2);
lean_closure_set(v___x_494_, 0, v_fst_476_);
lean_closure_set(v___x_494_, 1, v_a_477_);
v___x_495_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_494_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_dec_ref_known(v___x_495_, 1);
v_a_483_ = v___x_489_;
goto v___jp_482_;
}
else
{
lean_dec(v_a_477_);
lean_dec(v_fst_476_);
return v___x_495_;
}
}
else
{
v_a_483_ = v___x_489_;
goto v___jp_482_;
}
}
v___jp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_a_477_, v___x_484_);
lean_dec(v_a_477_);
v_a_477_ = v___x_485_;
v_b_478_ = v_a_483_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object* v_upperBound_496_, lean_object* v_snd_497_, lean_object* v_fst_498_, lean_object* v_a_499_, lean_object* v_b_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_496_, v_snd_497_, v_fst_498_, v_a_499_, v_b_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec_ref(v_snd_497_);
lean_dec(v_upperBound_496_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(lean_object* v_as_505_, size_t v_sz_506_, size_t v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v_b_508_);
return v___x_513_;
}
else
{
lean_object* v_a_514_; lean_object* v_snd_515_; lean_object* v_fst_516_; lean_object* v_snd_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_a_514_ = lean_array_uget_borrowed(v_as_505_, v_i_507_);
v_snd_515_ = lean_ctor_get(v_a_514_, 1);
v_fst_516_ = lean_ctor_get(v_snd_515_, 0);
v_snd_517_ = lean_ctor_get(v_snd_515_, 1);
v___x_518_ = lean_box(0);
v___x_519_ = lean_array_get_size(v_snd_517_);
v___x_520_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_516_);
v___x_521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_519_, v_snd_517_, v_fst_516_, v___x_520_, v___x_518_, v___y_509_, v___y_510_);
if (lean_obj_tag(v___x_521_) == 0)
{
size_t v___x_522_; size_t v___x_523_; 
lean_dec_ref_known(v___x_521_, 1);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_add(v_i_507_, v___x_522_);
v_i_507_ = v___x_523_;
v_b_508_ = v___x_518_;
goto _start;
}
else
{
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object* v_as_525_, lean_object* v_sz_526_, lean_object* v_i_527_, lean_object* v_b_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
size_t v_sz_boxed_532_; size_t v_i_boxed_533_; lean_object* v_res_534_; 
v_sz_boxed_532_ = lean_unbox_usize(v_sz_526_);
lean_dec(v_sz_526_);
v_i_boxed_533_ = lean_unbox_usize(v_i_527_);
lean_dec(v_i_527_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_525_, v_sz_boxed_532_, v_i_boxed_533_, v_b_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v_as_525_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(lean_object* v_hi_535_, lean_object* v_pivot_536_, lean_object* v_as_537_, lean_object* v_i_538_, lean_object* v_k_539_){
_start:
{
uint8_t v___x_540_; 
v___x_540_ = lean_nat_dec_lt(v_k_539_, v_hi_535_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec(v_k_539_);
v___x_541_ = lean_array_fswap(v_as_537_, v_i_538_, v_hi_535_);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_i_538_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v_fst_544_; lean_object* v_fst_545_; lean_object* v_start_546_; lean_object* v_start_547_; uint8_t v___x_548_; 
v___x_543_ = lean_array_fget_borrowed(v_as_537_, v_k_539_);
v_fst_544_ = lean_ctor_get(v___x_543_, 0);
v_fst_545_ = lean_ctor_get(v_pivot_536_, 0);
v_start_546_ = lean_ctor_get(v_fst_544_, 0);
v_start_547_ = lean_ctor_get(v_fst_545_, 0);
v___x_548_ = lean_nat_dec_lt(v_start_546_, v_start_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_k_539_, v___x_549_);
lean_dec(v_k_539_);
v_k_539_ = v___x_550_;
goto _start;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = lean_array_fswap(v_as_537_, v_i_538_, v_k_539_);
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_add(v_i_538_, v___x_553_);
lean_dec(v_i_538_);
v___x_555_ = lean_nat_add(v_k_539_, v___x_553_);
lean_dec(v_k_539_);
v_as_537_ = v___x_552_;
v_i_538_ = v___x_554_;
v_k_539_ = v___x_555_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg___boxed(lean_object* v_hi_557_, lean_object* v_pivot_558_, lean_object* v_as_559_, lean_object* v_i_560_, lean_object* v_k_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_557_, v_pivot_558_, v_as_559_, v_i_560_, v_k_561_);
lean_dec_ref(v_pivot_558_);
lean_dec(v_hi_557_);
return v_res_562_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(lean_object* v_x1_563_, lean_object* v_x2_564_){
_start:
{
lean_object* v_fst_565_; lean_object* v_fst_566_; lean_object* v_start_567_; lean_object* v_start_568_; uint8_t v___x_569_; 
v_fst_565_ = lean_ctor_get(v_x1_563_, 0);
v_fst_566_ = lean_ctor_get(v_x2_564_, 0);
v_start_567_ = lean_ctor_get(v_fst_565_, 0);
v_start_568_ = lean_ctor_get(v_fst_566_, 0);
v___x_569_ = lean_nat_dec_lt(v_start_567_, v_start_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0___boxed(lean_object* v_x1_570_, lean_object* v_x2_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v_x1_570_, v_x2_571_);
lean_dec_ref(v_x2_571_);
lean_dec_ref(v_x1_570_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(lean_object* v_n_574_, lean_object* v_as_575_, lean_object* v_lo_576_, lean_object* v_hi_577_){
_start:
{
lean_object* v___y_579_; uint8_t v___x_589_; 
v___x_589_ = lean_nat_dec_lt(v_lo_576_, v_hi_577_);
if (v___x_589_ == 0)
{
lean_dec(v_lo_576_);
return v_as_575_;
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_mid_592_; lean_object* v___y_594_; lean_object* v___y_600_; lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_590_ = lean_nat_add(v_lo_576_, v_hi_577_);
v___x_591_ = lean_unsigned_to_nat(1u);
v_mid_592_ = lean_nat_shiftr(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
v___x_605_ = lean_array_fget_borrowed(v_as_575_, v_mid_592_);
v___x_606_ = lean_array_fget_borrowed(v_as_575_, v_lo_576_);
v___x_607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
v___y_600_ = v_as_575_;
goto v___jp_599_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_array_fswap(v_as_575_, v_lo_576_, v_mid_592_);
v___y_600_ = v___x_608_;
goto v___jp_599_;
}
v___jp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_array_fget_borrowed(v___y_594_, v_mid_592_);
v___x_596_ = lean_array_fget_borrowed(v___y_594_, v_hi_577_);
v___x_597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_dec(v_mid_592_);
v___y_579_ = v___y_594_;
goto v___jp_578_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = lean_array_fswap(v___y_594_, v_mid_592_, v_hi_577_);
lean_dec(v_mid_592_);
v___y_579_ = v___x_598_;
goto v___jp_578_;
}
}
v___jp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_array_fget_borrowed(v___y_600_, v_hi_577_);
v___x_602_ = lean_array_fget_borrowed(v___y_600_, v_lo_576_);
v___x_603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
v___y_594_ = v___y_600_;
goto v___jp_593_;
}
else
{
lean_object* v___x_604_; 
v___x_604_ = lean_array_fswap(v___y_600_, v_lo_576_, v_hi_577_);
v___y_594_ = v___x_604_;
goto v___jp_593_;
}
}
}
v___jp_578_:
{
lean_object* v_pivot_580_; lean_object* v___x_581_; lean_object* v_fst_582_; lean_object* v_snd_583_; uint8_t v___x_584_; 
v_pivot_580_ = lean_array_fget(v___y_579_, v_hi_577_);
lean_inc_n(v_lo_576_, 2);
v___x_581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_577_, v_pivot_580_, v___y_579_, v_lo_576_, v_lo_576_);
lean_dec(v_pivot_580_);
v_fst_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_fst_582_);
v_snd_583_ = lean_ctor_get(v___x_581_, 1);
lean_inc(v_snd_583_);
lean_dec_ref(v___x_581_);
v___x_584_ = lean_nat_dec_le(v_hi_577_, v_fst_582_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_574_, v_snd_583_, v_lo_576_, v_fst_582_);
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_fst_582_, v___x_586_);
lean_dec(v_fst_582_);
v_as_575_ = v___x_585_;
v_lo_576_ = v___x_587_;
goto _start;
}
else
{
lean_dec(v_fst_582_);
lean_dec(v_lo_576_);
return v_snd_583_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___boxed(lean_object* v_n_609_, lean_object* v_as_610_, lean_object* v_lo_611_, lean_object* v_hi_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_609_, v_as_610_, v_lo_611_, v_hi_612_);
lean_dec(v_hi_612_);
lean_dec(v_n_609_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
return v_x_614_;
}
else
{
lean_object* v_key_616_; lean_object* v_value_617_; lean_object* v_tail_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_key_616_ = lean_ctor_get(v_x_615_, 0);
v_value_617_ = lean_ctor_get(v_x_615_, 1);
v_tail_618_ = lean_ctor_get(v_x_615_, 2);
lean_inc(v_value_617_);
lean_inc(v_key_616_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v_key_616_);
lean_ctor_set(v___x_619_, 1, v_value_617_);
v___x_620_ = lean_array_push(v_x_614_, v___x_619_);
v_x_614_ = v___x_620_;
v_x_615_ = v_tail_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10___boxed(lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_x_622_, v_x_623_);
lean_dec(v_x_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(lean_object* v_as_625_, size_t v_i_626_, size_t v_stop_627_, lean_object* v_b_628_){
_start:
{
uint8_t v___x_629_; 
v___x_629_ = lean_usize_dec_eq(v_i_626_, v_stop_627_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; size_t v___x_632_; size_t v___x_633_; 
v___x_630_ = lean_array_uget_borrowed(v_as_625_, v_i_626_);
v___x_631_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_unusedSimpArgs_spec__10(v_b_628_, v___x_630_);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_i_626_, v___x_632_);
v_i_626_ = v___x_633_;
v_b_628_ = v___x_631_;
goto _start;
}
else
{
return v_b_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(lean_object* v_as_635_, lean_object* v_i_636_, lean_object* v_stop_637_, lean_object* v_b_638_){
_start:
{
size_t v_i_boxed_639_; size_t v_stop_boxed_640_; lean_object* v_res_641_; 
v_i_boxed_639_ = lean_unbox_usize(v_i_636_);
lean_dec(v_i_636_);
v_stop_boxed_640_ = lean_unbox_usize(v_stop_637_);
lean_dec(v_stop_637_);
v_res_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_as_635_, v_i_boxed_639_, v_stop_boxed_640_, v_b_638_);
lean_dec_ref(v_as_635_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(lean_object* v_o_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_env_646_; lean_object* v___x_647_; lean_object* v_toEnvExtension_648_; lean_object* v_asyncMode_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v_merged_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v___x_645_ = lean_st_ref_get(v___y_643_);
v_env_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_645_);
v___x_647_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_648_ = lean_ctor_get(v___x_647_, 0);
v_asyncMode_649_ = lean_ctor_get(v_toEnvExtension_648_, 2);
v___x_650_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_651_ = lean_box(0);
v___x_652_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_650_, v___x_647_, v_env_646_, v_asyncMode_649_, v___x_651_);
v_merged_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v___x_652_, 1);
lean_dec(v_unused_662_);
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_merged_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v_merged_653_);
lean_ctor_set(v___x_655_, 0, v_o_642_);
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_o_642_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_merged_653_);
v___x_658_ = v_reuseFailAlloc_660_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(lean_object* v_o_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_663_, v___y_664_);
lean_dec(v___y_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v_scopes_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_opts_674_; lean_object* v___x_675_; 
v___x_670_ = lean_st_ref_get(v___y_668_);
v_scopes_671_ = lean_ctor_get(v___x_670_, 2);
lean_inc(v_scopes_671_);
lean_dec(v___x_670_);
v___x_672_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_673_ = l_List_head_x21___redArg(v___x_672_, v_scopes_671_);
lean_dec(v_scopes_671_);
v_opts_674_ = lean_ctor_get(v___x_673_, 1);
lean_inc_ref(v_opts_674_);
lean_dec(v___x_673_);
v___x_675_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_opts_674_, v___y_668_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(uint8_t v___x_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_box(v___x_680_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(lean_object* v___x_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
uint8_t v___x_13511__boxed_696_; lean_object* v_res_697_; 
v___x_13511__boxed_696_ = lean_unbox(v___x_689_);
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v___x_13511__boxed_696_, v_x_690_, v_x_691_, v_x_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec_ref(v_x_692_);
lean_dec_ref(v_x_691_);
lean_dec_ref(v_x_690_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(lean_object* v_postNode_698_, lean_object* v_ci_699_, lean_object* v_i_700_, lean_object* v_cs_701_, lean_object* v_x_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; 
lean_inc(v___y_704_);
lean_inc_ref(v___y_703_);
v___x_706_ = lean_apply_6(v_postNode_698_, v_ci_699_, v_i_700_, v_cs_701_, v___y_703_, v___y_704_, lean_box(0));
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(lean_object* v_postNode_707_, lean_object* v_ci_708_, lean_object* v_i_709_, lean_object* v_cs_710_, lean_object* v_x_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(v_postNode_707_, v_ci_708_, v_i_709_, v_cs_710_, v_x_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v_x_711_);
return v_res_715_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_instMonadEIO(lean_box(0));
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v_toApplicative_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_756_; 
v___x_723_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0);
v___x_724_ = l_StateRefT_x27_instMonad___redArg(v___x_723_);
v_toApplicative_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v___x_724_, 1);
lean_dec(v_unused_757_);
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_756_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_toApplicative_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_756_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_toFunctor_729_; lean_object* v_toSeq_730_; lean_object* v_toSeqLeft_731_; lean_object* v_toSeqRight_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_754_; 
v_toFunctor_729_ = lean_ctor_get(v_toApplicative_725_, 0);
v_toSeq_730_ = lean_ctor_get(v_toApplicative_725_, 2);
v_toSeqLeft_731_ = lean_ctor_get(v_toApplicative_725_, 3);
v_toSeqRight_732_ = lean_ctor_get(v_toApplicative_725_, 4);
v_isSharedCheck_754_ = !lean_is_exclusive(v_toApplicative_725_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_toApplicative_725_, 1);
lean_dec(v_unused_755_);
v___x_734_ = v_toApplicative_725_;
v_isShared_735_ = v_isSharedCheck_754_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_toSeqRight_732_);
lean_inc(v_toSeqLeft_731_);
lean_inc(v_toSeq_730_);
lean_inc(v_toFunctor_729_);
lean_dec(v_toApplicative_725_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_754_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___f_743_; lean_object* v___x_745_; 
v___f_736_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1));
v___f_737_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2));
lean_inc_ref(v_toFunctor_729_);
v___f_738_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_738_, 0, v_toFunctor_729_);
v___f_739_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_739_, 0, v_toFunctor_729_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___f_738_);
lean_ctor_set(v___x_740_, 1, v___f_739_);
v___f_741_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_741_, 0, v_toSeqRight_732_);
v___f_742_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_742_, 0, v_toSeqLeft_731_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_743_, 0, v_toSeq_730_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 4, v___f_741_);
lean_ctor_set(v___x_734_, 3, v___f_742_);
lean_ctor_set(v___x_734_, 2, v___f_743_);
lean_ctor_set(v___x_734_, 1, v___f_736_);
lean_ctor_set(v___x_734_, 0, v___x_740_);
v___x_745_ = v___x_734_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_740_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___f_736_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v___f_743_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v___f_742_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v___f_741_);
v___x_745_ = v_reuseFailAlloc_753_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_747_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v___f_737_);
lean_ctor_set(v___x_727_, 0, v___x_745_);
v___x_747_ = v___x_727_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___f_737_);
v___x_747_ = v_reuseFailAlloc_752_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_12632__overap_750_; lean_object* v___x_751_; 
v___x_748_ = lean_box(0);
v___x_749_ = l_instInhabitedOfMonad___redArg(v___x_747_, v___x_748_);
v___x_12632__overap_750_ = lean_panic_fn_borrowed(v___x_749_, v_msg_719_);
lean_dec(v___x_749_);
lean_inc(v___y_721_);
lean_inc_ref(v___y_720_);
v___x_751_ = lean_apply_3(v___x_12632__overap_750_, v___y_720_, v___y_721_, lean_box(0));
return v___x_751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_762_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_766_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2));
v___x_767_ = lean_unsigned_to_nat(21u);
v___x_768_ = lean_unsigned_to_nat(65u);
v___x_769_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1));
v___x_770_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0));
v___x_771_ = l_mkPanicMessageWithDecl(v___x_770_, v___x_769_, v___x_768_, v___x_767_, v___x_766_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(lean_object* v_preNode_772_, lean_object* v_postNode_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
switch(lean_obj_tag(v_x_775_))
{
case 0:
{
lean_object* v_i_779_; lean_object* v_t_780_; lean_object* v___x_781_; 
v_i_779_ = lean_ctor_get(v_x_775_, 0);
lean_inc_ref(v_i_779_);
v_t_780_ = lean_ctor_get(v_x_775_, 1);
lean_inc_ref(v_t_780_);
lean_dec_ref_known(v_x_775_, 2);
v___x_781_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_779_, v_x_774_);
v_x_774_ = v___x_781_;
v_x_775_ = v_t_780_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref_known(v_x_775_, 2);
lean_dec_ref(v_postNode_773_);
lean_dec_ref(v_preNode_772_);
v___x_783_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3);
v___x_784_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v___x_783_, v___y_776_, v___y_777_);
return v___x_784_;
}
else
{
lean_object* v_i_785_; lean_object* v_children_786_; lean_object* v_val_787_; lean_object* v___x_788_; 
v_i_785_ = lean_ctor_get(v_x_775_, 0);
lean_inc_ref_n(v_i_785_, 2);
v_children_786_ = lean_ctor_get(v_x_775_, 1);
lean_inc_ref_n(v_children_786_, 2);
lean_dec_ref_known(v_x_775_, 2);
v_val_787_ = lean_ctor_get(v_x_774_, 0);
lean_inc_n(v_val_787_, 2);
lean_inc_ref(v_preNode_772_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
v___x_788_ = lean_apply_6(v_preNode_772_, v_val_787_, v_i_785_, v_children_786_, v___y_776_, v___y_777_, lean_box(0));
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; uint8_t v___x_790_; uint8_t v___x_791_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = lean_unbox(v_a_789_);
lean_dec(v_a_789_);
v___x_791_ = lean_bool_not(v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_792_ = l_Lean_Elab_Info_updateContext_x3f(v_x_774_, v_i_785_);
v___x_793_ = l_Lean_PersistentArray_toList___redArg(v_children_786_);
v___x_794_ = lean_box(0);
lean_inc_ref(v_postNode_773_);
v___x_795_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_772_, v_postNode_773_, v___x_792_, v___x_793_, v___x_794_, v___y_776_, v___y_777_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
v___x_797_ = lean_apply_7(v_postNode_773_, v_val_787_, v_i_785_, v_children_786_, v_a_796_, v___y_776_, v___y_777_, lean_box(0));
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v_a_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_802_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
v_a_807_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_797_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
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
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_val_787_);
lean_dec_ref(v_children_786_);
lean_dec_ref(v_i_785_);
lean_dec_ref(v_postNode_773_);
v_a_815_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_795_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_795_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_preNode_772_);
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_774_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v_x_774_, 0);
lean_dec(v_unused_848_);
v___x_824_ = v_x_774_;
v_isShared_825_ = v_isSharedCheck_847_;
goto v_resetjp_823_;
}
else
{
lean_dec(v_x_774_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_847_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_box(0);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
v___x_827_ = lean_apply_7(v_postNode_773_, v_val_787_, v_i_785_, v_children_786_, v___x_826_, v___y_776_, v___y_777_, lean_box(0));
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_838_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_838_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_838_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_838_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_a_828_);
v___x_833_ = v___x_824_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_837_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_833_);
v___x_835_ = v___x_830_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_del_object(v___x_824_);
v_a_839_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_827_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_827_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec(v_val_787_);
lean_dec_ref(v_children_786_);
lean_dec_ref_known(v_x_774_, 1);
lean_dec_ref(v_i_785_);
lean_dec_ref(v_postNode_773_);
lean_dec_ref(v_preNode_772_);
v_a_849_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_788_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_788_);
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
default: 
{
lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_864_; 
lean_dec(v_x_774_);
lean_dec_ref(v_postNode_773_);
lean_dec_ref(v_preNode_772_);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x_775_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v_x_775_, 0);
lean_dec(v_unused_865_);
v___x_858_ = v_x_775_;
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
else
{
lean_dec(v_x_775_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = lean_box(0);
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 0);
lean_ctor_set(v___x_858_, 0, v___x_860_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(lean_object* v_preNode_866_, lean_object* v_postNode_867_, lean_object* v___x_868_, lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
if (lean_obj_tag(v_x_869_) == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v___x_868_);
lean_dec_ref(v_postNode_867_);
lean_dec_ref(v_preNode_866_);
v___x_874_ = l_List_reverse___redArg(v_x_870_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
else
{
lean_object* v_head_876_; lean_object* v_tail_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_895_; 
v_head_876_ = lean_ctor_get(v_x_869_, 0);
v_tail_877_ = lean_ctor_get(v_x_869_, 1);
v_isSharedCheck_895_ = !lean_is_exclusive(v_x_869_);
if (v_isSharedCheck_895_ == 0)
{
v___x_879_ = v_x_869_;
v_isShared_880_ = v_isSharedCheck_895_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_tail_877_);
lean_inc(v_head_876_);
lean_dec(v_x_869_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_895_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; 
lean_inc(v___x_868_);
lean_inc_ref(v_postNode_867_);
lean_inc_ref(v_preNode_866_);
v___x_881_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_866_, v_postNode_867_, v___x_868_, v_head_876_, v___y_871_, v___y_872_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v_x_870_);
lean_ctor_set(v___x_879_, 0, v_a_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_882_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_x_870_);
v___x_884_ = v_reuseFailAlloc_886_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v_x_869_ = v_tail_877_;
v_x_870_ = v___x_884_;
goto _start;
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_del_object(v___x_879_);
lean_dec(v_tail_877_);
lean_dec(v_x_870_);
lean_dec(v___x_868_);
lean_dec_ref(v_postNode_867_);
lean_dec_ref(v_preNode_866_);
v_a_887_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_881_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_881_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(lean_object* v_preNode_896_, lean_object* v_postNode_897_, lean_object* v___x_898_, lean_object* v_x_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_896_, v_postNode_897_, v___x_898_, v_x_899_, v_x_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(lean_object* v_preNode_905_, lean_object* v_postNode_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_905_, v_postNode_906_, v_x_907_, v_x_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object* v_preNode_913_, lean_object* v_postNode_914_, lean_object* v_ctx_x3f_915_, lean_object* v_t_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___f_920_; lean_object* v___x_921_; 
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(v___f_920_, 0, v_postNode_914_);
v___x_921_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_913_, v___f_920_, v_ctx_x3f_915_, v_t_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_929_; 
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v___x_921_, 0);
lean_dec(v_unused_930_);
v___x_923_ = v___x_921_;
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
else
{
lean_dec(v___x_921_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_box(0);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_925_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_921_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_921_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object* v_preNode_939_, lean_object* v_postNode_940_, lean_object* v_ctx_x3f_941_, lean_object* v_t_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v_preNode_939_, v_postNode_940_, v_ctx_x3f_941_, v_t_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(lean_object* v_a_947_, lean_object* v_x_948_){
_start:
{
if (lean_obj_tag(v_x_948_) == 0)
{
lean_object* v___x_949_; 
v___x_949_ = lean_box(0);
return v___x_949_;
}
else
{
lean_object* v_key_950_; lean_object* v_value_951_; lean_object* v_tail_952_; uint8_t v___x_953_; 
v_key_950_ = lean_ctor_get(v_x_948_, 0);
v_value_951_ = lean_ctor_get(v_x_948_, 1);
v_tail_952_ = lean_ctor_get(v_x_948_, 2);
v___x_953_ = l_Lean_Syntax_instBEqRange_beq(v_key_950_, v_a_947_);
if (v___x_953_ == 0)
{
v_x_948_ = v_tail_952_;
goto _start;
}
else
{
lean_object* v___x_955_; 
lean_inc(v_value_951_);
v___x_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_955_, 0, v_value_951_);
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(lean_object* v_a_956_, lean_object* v_x_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_956_, v_x_957_);
lean_dec(v_x_957_);
lean_dec_ref(v_a_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object* v_m_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_buckets_961_; lean_object* v___x_962_; uint64_t v___x_963_; uint64_t v___x_964_; uint64_t v___x_965_; uint64_t v_fold_966_; uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_buckets_961_ = lean_ctor_get(v_m_959_, 1);
v___x_962_ = lean_array_get_size(v_buckets_961_);
v___x_963_ = l_Lean_Syntax_instHashableRange_hash(v_a_960_);
v___x_964_ = 32ULL;
v___x_965_ = lean_uint64_shift_right(v___x_963_, v___x_964_);
v_fold_966_ = lean_uint64_xor(v___x_963_, v___x_965_);
v___x_967_ = 16ULL;
v___x_968_ = lean_uint64_shift_right(v_fold_966_, v___x_967_);
v___x_969_ = lean_uint64_xor(v_fold_966_, v___x_968_);
v___x_970_ = lean_uint64_to_usize(v___x_969_);
v___x_971_ = lean_usize_of_nat(v___x_962_);
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_sub(v___x_971_, v___x_972_);
v___x_974_ = lean_usize_land(v___x_970_, v___x_973_);
v___x_975_ = lean_array_uget_borrowed(v_buckets_961_, v___x_974_);
v___x_976_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_960_, v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object* v_m_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_977_, v_a_978_);
lean_dec_ref(v_a_978_);
lean_dec_ref(v_m_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(lean_object* v_as_980_, lean_object* v_bs_981_, lean_object* v_i_982_, lean_object* v_cs_983_){
_start:
{
uint8_t v___y_985_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_array_get_size(v_as_980_);
v___x_992_ = lean_nat_dec_lt(v_i_982_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec(v_i_982_);
return v_cs_983_;
}
else
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = lean_array_get_size(v_bs_981_);
v___x_994_ = lean_nat_dec_lt(v_i_982_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v_i_982_);
return v_cs_983_;
}
else
{
lean_object* v_a_995_; uint8_t v___x_996_; 
v_a_995_ = lean_array_fget_borrowed(v_as_980_, v_i_982_);
v___x_996_ = lean_unbox(v_a_995_);
if (v___x_996_ == 0)
{
lean_object* v_b_997_; uint8_t v___x_998_; 
v_b_997_ = lean_array_fget_borrowed(v_bs_981_, v_i_982_);
v___x_998_ = lean_unbox(v_b_997_);
v___y_985_ = v___x_998_;
goto v___jp_984_;
}
else
{
uint8_t v___x_999_; 
v___x_999_ = lean_unbox(v_a_995_);
v___y_985_ = v___x_999_;
goto v___jp_984_;
}
}
}
v___jp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_nat_add(v_i_982_, v___x_986_);
lean_dec(v_i_982_);
v___x_988_ = lean_box(v___y_985_);
v___x_989_ = lean_array_push(v_cs_983_, v___x_988_);
v_i_982_ = v___x_987_;
v_cs_983_ = v___x_989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object* v_as_1000_, lean_object* v_bs_1001_, lean_object* v_i_1002_, lean_object* v_cs_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v_as_1000_, v_bs_1001_, v_i_1002_, v_cs_1003_);
lean_dec_ref(v_bs_1001_);
lean_dec_ref(v_as_1000_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(lean_object* v_msgData_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v_env_1009_; lean_object* v___x_1010_; lean_object* v_scopes_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_opts_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1008_ = lean_st_ref_get(v___y_1006_);
v_env_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_env_1009_);
lean_dec(v___x_1008_);
v___x_1010_ = lean_st_ref_get(v___y_1006_);
v_scopes_1011_ = lean_ctor_get(v___x_1010_, 2);
lean_inc(v_scopes_1011_);
lean_dec(v___x_1010_);
v___x_1012_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1013_ = l_List_head_x21___redArg(v___x_1012_, v_scopes_1011_);
lean_dec(v_scopes_1011_);
v_opts_1014_ = lean_ctor_get(v___x_1013_, 1);
lean_inc_ref(v_opts_1014_);
lean_dec(v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_1016_ = lean_unsigned_to_nat(32u);
v___x_1017_ = lean_mk_empty_array_with_capacity(v___x_1016_);
lean_dec_ref(v___x_1017_);
v___x_1018_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
v___x_1019_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1019_, 0, v_env_1009_);
lean_ctor_set(v___x_1019_, 1, v___x_1015_);
lean_ctor_set(v___x_1019_, 2, v___x_1018_);
lean_ctor_set(v___x_1019_, 3, v_opts_1014_);
v___x_1020_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_msgData_1005_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_1022_, v___y_1023_);
lean_dec(v___y_1023_);
return v_res_1025_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_box(1);
v___x_1027_ = l_Lean_MessageData_ofFormat(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2));
v___x_1032_ = l_Lean_MessageData_ofFormat(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(lean_object* v_x_1033_, lean_object* v_x_1034_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
return v_x_1033_;
}
else
{
lean_object* v_head_1035_; lean_object* v_tail_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1058_; 
v_head_1035_ = lean_ctor_get(v_x_1034_, 0);
v_tail_1036_ = lean_ctor_get(v_x_1034_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1038_ = v_x_1034_;
v_isShared_1039_ = v_isSharedCheck_1058_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_tail_1036_);
lean_inc(v_head_1035_);
lean_dec(v_x_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1058_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_before_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1056_; 
v_before_1040_ = lean_ctor_get(v_head_1035_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_head_1035_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v_head_1035_, 1);
lean_dec(v_unused_1057_);
v___x_1042_ = v_head_1035_;
v_isShared_1043_ = v_isSharedCheck_1056_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_before_1040_);
lean_dec(v_head_1035_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1056_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_1043_ == 0)
{
lean_ctor_set_tag(v___x_1042_, 7);
lean_ctor_set(v___x_1042_, 1, v___x_1044_);
lean_ctor_set(v___x_1042_, 0, v_x_1033_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_x_1033_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1047_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3);
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 7);
lean_ctor_set(v___x_1038_, 1, v___x_1047_);
lean_ctor_set(v___x_1038_, 0, v___x_1046_);
v___x_1049_ = v___x_1038_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = l_Lean_MessageData_ofSyntax(v_before_1040_);
v___x_1051_ = l_Lean_indentD(v___x_1050_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1049_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v_x_1033_ = v___x_1052_;
v_x_1034_ = v_tail_1036_;
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
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1));
v___x_1063_ = l_Lean_MessageData_ofFormat(v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(lean_object* v_msgData_1064_, lean_object* v_macroStack_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v_scopes_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_opts_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1068_ = lean_st_ref_get(v___y_1066_);
v_scopes_1069_ = lean_ctor_get(v___x_1068_, 2);
lean_inc(v_scopes_1069_);
lean_dec(v___x_1068_);
v___x_1070_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1071_ = l_List_head_x21___redArg(v___x_1070_, v_scopes_1069_);
lean_dec(v_scopes_1069_);
v_opts_1072_ = lean_ctor_get(v___x_1071_, 1);
lean_inc_ref(v_opts_1072_);
lean_dec(v___x_1071_);
v___x_1073_ = l_Lean_Elab_pp_macroStack;
v___x_1074_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_1072_, v___x_1073_);
lean_dec_ref(v_opts_1072_);
v___x_1075_ = lean_bool_not(v___x_1074_);
if (v___x_1075_ == 0)
{
if (lean_obj_tag(v_macroStack_1065_) == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v_msgData_1064_);
return v___x_1076_;
}
else
{
lean_object* v_head_1077_; lean_object* v_after_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1093_; 
v_head_1077_ = lean_ctor_get(v_macroStack_1065_, 0);
lean_inc(v_head_1077_);
v_after_1078_ = lean_ctor_get(v_head_1077_, 1);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_head_1077_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v_head_1077_, 0);
lean_dec(v_unused_1094_);
v___x_1080_ = v_head_1077_;
v_isShared_1081_ = v_isSharedCheck_1093_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_after_1078_);
lean_dec(v_head_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1093_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 7);
lean_ctor_set(v___x_1080_, 1, v___x_1082_);
lean_ctor_set(v___x_1080_, 0, v_msgData_1064_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_msgData_1064_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_msgData_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1085_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_MessageData_ofSyntax(v_after_1078_);
v___x_1088_ = l_Lean_indentD(v___x_1087_);
v_msgData_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1089_, 0, v___x_1086_);
lean_ctor_set(v_msgData_1089_, 1, v___x_1088_);
v___x_1090_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(v_msgData_1089_, v_macroStack_1065_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
}
else
{
lean_object* v___x_1095_; 
lean_dec(v_macroStack_1065_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_msgData_1064_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v_msgData_1096_, lean_object* v_macroStack_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_1096_, v_macroStack_1097_, v___y_1098_);
lean_dec(v___y_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(lean_object* v_msg_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_Elab_Command_getRef___redArg(v___y_1102_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_macroStack_1107_; lean_object* v___x_1108_; lean_object* v_a_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1120_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_macroStack_1107_ = lean_ctor_get(v___y_1102_, 4);
v___x_1108_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msg_1101_, v___y_1103_);
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref(v___x_1108_);
v___x_1110_ = l_Lean_Elab_getBetterRef(v_a_1106_, v_macroStack_1107_);
lean_dec(v_a_1106_);
lean_inc(v_macroStack_1107_);
v___x_1111_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_a_1109_, v_macroStack_1107_, v___y_1103_);
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1110_);
lean_ctor_set(v___x_1116_, 1, v_a_1112_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set_tag(v___x_1114_, 1);
lean_ctor_set(v___x_1114_, 0, v___x_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v_msg_1101_);
v_a_1121_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1105_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1105_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg___boxed(lean_object* v_msg_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(lean_object* v_ref_1134_, lean_object* v_msg_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_Elab_Command_getRef___redArg(v___y_1136_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v_fileName_1141_; lean_object* v_fileMap_1142_; lean_object* v_currRecDepth_1143_; lean_object* v_cmdPos_1144_; lean_object* v_macroStack_1145_; lean_object* v_quotContext_x3f_1146_; lean_object* v_currMacroScope_1147_; lean_object* v_snap_x3f_1148_; lean_object* v_cancelTk_x3f_1149_; uint8_t v_suppressElabErrors_1150_; lean_object* v_ref_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v_fileName_1141_ = lean_ctor_get(v___y_1136_, 0);
v_fileMap_1142_ = lean_ctor_get(v___y_1136_, 1);
v_currRecDepth_1143_ = lean_ctor_get(v___y_1136_, 2);
v_cmdPos_1144_ = lean_ctor_get(v___y_1136_, 3);
v_macroStack_1145_ = lean_ctor_get(v___y_1136_, 4);
v_quotContext_x3f_1146_ = lean_ctor_get(v___y_1136_, 5);
v_currMacroScope_1147_ = lean_ctor_get(v___y_1136_, 6);
v_snap_x3f_1148_ = lean_ctor_get(v___y_1136_, 8);
v_cancelTk_x3f_1149_ = lean_ctor_get(v___y_1136_, 9);
v_suppressElabErrors_1150_ = lean_ctor_get_uint8(v___y_1136_, sizeof(void*)*10);
v_ref_1151_ = l_Lean_replaceRef(v_ref_1134_, v_a_1140_);
lean_dec(v_a_1140_);
lean_inc(v_cancelTk_x3f_1149_);
lean_inc(v_snap_x3f_1148_);
lean_inc(v_currMacroScope_1147_);
lean_inc(v_quotContext_x3f_1146_);
lean_inc(v_macroStack_1145_);
lean_inc(v_cmdPos_1144_);
lean_inc(v_currRecDepth_1143_);
lean_inc_ref(v_fileMap_1142_);
lean_inc_ref(v_fileName_1141_);
v___x_1152_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1152_, 0, v_fileName_1141_);
lean_ctor_set(v___x_1152_, 1, v_fileMap_1142_);
lean_ctor_set(v___x_1152_, 2, v_currRecDepth_1143_);
lean_ctor_set(v___x_1152_, 3, v_cmdPos_1144_);
lean_ctor_set(v___x_1152_, 4, v_macroStack_1145_);
lean_ctor_set(v___x_1152_, 5, v_quotContext_x3f_1146_);
lean_ctor_set(v___x_1152_, 6, v_currMacroScope_1147_);
lean_ctor_set(v___x_1152_, 7, v_ref_1151_);
lean_ctor_set(v___x_1152_, 8, v_snap_x3f_1148_);
lean_ctor_set(v___x_1152_, 9, v_cancelTk_x3f_1149_);
lean_ctor_set_uint8(v___x_1152_, sizeof(void*)*10, v_suppressElabErrors_1150_);
v___x_1153_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_1135_, v___x_1152_, v___y_1137_);
lean_dec_ref_known(v___x_1152_, 10);
return v___x_1153_;
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v_msg_1135_);
v_a_1154_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1139_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1139_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg___boxed(lean_object* v_ref_1162_, lean_object* v_msg_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_1162_, v_msg_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v_ref_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
return v_x_1168_;
}
else
{
lean_object* v_key_1170_; lean_object* v_value_1171_; lean_object* v_tail_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1195_; 
v_key_1170_ = lean_ctor_get(v_x_1169_, 0);
v_value_1171_ = lean_ctor_get(v_x_1169_, 1);
v_tail_1172_ = lean_ctor_get(v_x_1169_, 2);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1174_ = v_x_1169_;
v_isShared_1175_ = v_isSharedCheck_1195_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_tail_1172_);
lean_inc(v_value_1171_);
lean_inc(v_key_1170_);
lean_dec(v_x_1169_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1195_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; uint64_t v_fold_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1176_ = lean_array_get_size(v_x_1168_);
v___x_1177_ = l_Lean_Syntax_instHashableRange_hash(v_key_1170_);
v___x_1178_ = 32ULL;
v___x_1179_ = lean_uint64_shift_right(v___x_1177_, v___x_1178_);
v_fold_1180_ = lean_uint64_xor(v___x_1177_, v___x_1179_);
v___x_1181_ = 16ULL;
v___x_1182_ = lean_uint64_shift_right(v_fold_1180_, v___x_1181_);
v___x_1183_ = lean_uint64_xor(v_fold_1180_, v___x_1182_);
v___x_1184_ = lean_uint64_to_usize(v___x_1183_);
v___x_1185_ = lean_usize_of_nat(v___x_1176_);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_sub(v___x_1185_, v___x_1186_);
v___x_1188_ = lean_usize_land(v___x_1184_, v___x_1187_);
v___x_1189_ = lean_array_uget_borrowed(v_x_1168_, v___x_1188_);
lean_inc(v___x_1189_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 2, v___x_1189_);
v___x_1191_ = v___x_1174_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_key_1170_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_value_1171_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_array_uset(v_x_1168_, v___x_1188_, v___x_1191_);
v_x_1168_ = v___x_1192_;
v_x_1169_ = v_tail_1172_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1196_, lean_object* v_source_1197_, lean_object* v_target_1198_){
_start:
{
lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = lean_array_get_size(v_source_1197_);
v___x_1200_ = lean_nat_dec_lt(v_i_1196_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec_ref(v_source_1197_);
lean_dec(v_i_1196_);
return v_target_1198_;
}
else
{
lean_object* v_es_1201_; lean_object* v___x_1202_; lean_object* v_source_1203_; lean_object* v_target_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_es_1201_ = lean_array_fget(v_source_1197_, v_i_1196_);
v___x_1202_ = lean_box(0);
v_source_1203_ = lean_array_fset(v_source_1197_, v_i_1196_, v___x_1202_);
v_target_1204_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_target_1198_, v_es_1201_);
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_nat_add(v_i_1196_, v___x_1205_);
lean_dec(v_i_1196_);
v_i_1196_ = v___x_1206_;
v_source_1197_ = v_source_1203_;
v_target_1198_ = v_target_1204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(lean_object* v_data_1208_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_nbuckets_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1209_ = lean_array_get_size(v_data_1208_);
v___x_1210_ = lean_unsigned_to_nat(2u);
v_nbuckets_1211_ = lean_nat_mul(v___x_1209_, v___x_1210_);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_mk_array(v_nbuckets_1211_, v___x_1213_);
v___x_1215_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v___x_1212_, v_data_1208_, v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object* v_a_1216_, lean_object* v_x_1217_){
_start:
{
if (lean_obj_tag(v_x_1217_) == 0)
{
uint8_t v___x_1218_; 
v___x_1218_ = 0;
return v___x_1218_;
}
else
{
lean_object* v_key_1219_; lean_object* v_tail_1220_; uint8_t v___x_1221_; 
v_key_1219_ = lean_ctor_get(v_x_1217_, 0);
v_tail_1220_ = lean_ctor_get(v_x_1217_, 2);
v___x_1221_ = l_Lean_Syntax_instBEqRange_beq(v_key_1219_, v_a_1216_);
if (v___x_1221_ == 0)
{
v_x_1217_ = v_tail_1220_;
goto _start;
}
else
{
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object* v_a_1223_, lean_object* v_x_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1223_, v_x_1224_);
lean_dec(v_x_1224_);
lean_dec_ref(v_a_1223_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(lean_object* v_a_1227_, lean_object* v_b_1228_, lean_object* v_x_1229_){
_start:
{
if (lean_obj_tag(v_x_1229_) == 0)
{
lean_dec(v_b_1228_);
lean_dec_ref(v_a_1227_);
return v_x_1229_;
}
else
{
lean_object* v_key_1230_; lean_object* v_value_1231_; lean_object* v_tail_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1244_; 
v_key_1230_ = lean_ctor_get(v_x_1229_, 0);
v_value_1231_ = lean_ctor_get(v_x_1229_, 1);
v_tail_1232_ = lean_ctor_get(v_x_1229_, 2);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_x_1229_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1234_ = v_x_1229_;
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_tail_1232_);
lean_inc(v_value_1231_);
lean_inc(v_key_1230_);
lean_dec(v_x_1229_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1244_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
uint8_t v___x_1236_; 
v___x_1236_ = l_Lean_Syntax_instBEqRange_beq(v_key_1230_, v_a_1227_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1227_, v_b_1228_, v_tail_1232_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 2, v___x_1237_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_key_1230_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_value_1231_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
else
{
lean_object* v___x_1242_; 
lean_dec(v_value_1231_);
lean_dec(v_key_1230_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v_b_1228_);
lean_ctor_set(v___x_1234_, 0, v_a_1227_);
v___x_1242_ = v___x_1234_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1227_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_b_1228_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_tail_1232_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object* v_m_1245_, lean_object* v_a_1246_, lean_object* v_b_1247_){
_start:
{
lean_object* v_size_1248_; lean_object* v_buckets_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1292_; 
v_size_1248_ = lean_ctor_get(v_m_1245_, 0);
v_buckets_1249_ = lean_ctor_get(v_m_1245_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_m_1245_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1251_ = v_m_1245_;
v_isShared_1252_ = v_isSharedCheck_1292_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_buckets_1249_);
lean_inc(v_size_1248_);
lean_dec(v_m_1245_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1292_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; uint64_t v___x_1254_; uint64_t v___x_1255_; uint64_t v___x_1256_; uint64_t v_fold_1257_; uint64_t v___x_1258_; uint64_t v___x_1259_; uint64_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; lean_object* v_bkt_1266_; uint8_t v___x_1267_; 
v___x_1253_ = lean_array_get_size(v_buckets_1249_);
v___x_1254_ = l_Lean_Syntax_instHashableRange_hash(v_a_1246_);
v___x_1255_ = 32ULL;
v___x_1256_ = lean_uint64_shift_right(v___x_1254_, v___x_1255_);
v_fold_1257_ = lean_uint64_xor(v___x_1254_, v___x_1256_);
v___x_1258_ = 16ULL;
v___x_1259_ = lean_uint64_shift_right(v_fold_1257_, v___x_1258_);
v___x_1260_ = lean_uint64_xor(v_fold_1257_, v___x_1259_);
v___x_1261_ = lean_uint64_to_usize(v___x_1260_);
v___x_1262_ = lean_usize_of_nat(v___x_1253_);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_sub(v___x_1262_, v___x_1263_);
v___x_1265_ = lean_usize_land(v___x_1261_, v___x_1264_);
v_bkt_1266_ = lean_array_uget_borrowed(v_buckets_1249_, v___x_1265_);
v___x_1267_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1246_, v_bkt_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v_size_x27_1269_; lean_object* v___x_1270_; lean_object* v_buckets_x27_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1268_ = lean_unsigned_to_nat(1u);
v_size_x27_1269_ = lean_nat_add(v_size_1248_, v___x_1268_);
lean_dec(v_size_1248_);
lean_inc(v_bkt_1266_);
v___x_1270_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1270_, 0, v_a_1246_);
lean_ctor_set(v___x_1270_, 1, v_b_1247_);
lean_ctor_set(v___x_1270_, 2, v_bkt_1266_);
v_buckets_x27_1271_ = lean_array_uset(v_buckets_1249_, v___x_1265_, v___x_1270_);
v___x_1272_ = lean_unsigned_to_nat(4u);
v___x_1273_ = lean_nat_mul(v_size_x27_1269_, v___x_1272_);
v___x_1274_ = lean_unsigned_to_nat(3u);
v___x_1275_ = lean_nat_div(v___x_1273_, v___x_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_array_get_size(v_buckets_x27_1271_);
v___x_1277_ = lean_nat_dec_le(v___x_1275_, v___x_1276_);
lean_dec(v___x_1275_);
if (v___x_1277_ == 0)
{
lean_object* v_val_1278_; lean_object* v___x_1280_; 
v_val_1278_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_buckets_x27_1271_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_val_1278_);
lean_ctor_set(v___x_1251_, 0, v_size_x27_1269_);
v___x_1280_ = v___x_1251_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_size_x27_1269_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_val_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
else
{
lean_object* v___x_1283_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_buckets_x27_1271_);
lean_ctor_set(v___x_1251_, 0, v_size_x27_1269_);
v___x_1283_ = v___x_1251_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_size_x27_1269_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_buckets_x27_1271_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v_buckets_x27_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_inc(v_bkt_1266_);
v___x_1285_ = lean_box(0);
v_buckets_x27_1286_ = lean_array_uset(v_buckets_1249_, v___x_1265_, v___x_1285_);
v___x_1287_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1246_, v_b_1247_, v_bkt_1266_);
v___x_1288_ = lean_array_uset(v_buckets_x27_1286_, v___x_1265_, v___x_1287_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1288_);
v___x_1290_ = v___x_1251_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_size_1248_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__1));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__3));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(lean_object* v_val_1313_, lean_object* v_ci_1314_, lean_object* v_info_1315_, lean_object* v_x_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
if (lean_obj_tag(v_info_1315_) == 10)
{
lean_object* v_i_1320_; lean_object* v_stx_1321_; lean_object* v_value_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1417_; 
v_i_1320_ = lean_ctor_get(v_info_1315_, 0);
lean_inc_ref(v_i_1320_);
v_stx_1321_ = lean_ctor_get(v_i_1320_, 0);
v_value_1322_ = lean_ctor_get(v_i_1320_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_i_1320_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1324_ = v_i_1320_;
v_isShared_1325_ = v_isSharedCheck_1417_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_value_1322_);
lean_inc(v_stx_1321_);
lean_dec(v_i_1320_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1417_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
v___x_1327_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_1322_, v___x_1326_);
lean_dec(v_value_1322_);
if (lean_obj_tag(v___x_1327_) == 1)
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1407_; 
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1407_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1407_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Elab_Info_range_x3f(v_info_1315_);
if (lean_obj_tag(v___x_1332_) == 1)
{
lean_object* v_val_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1402_; 
v_val_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1402_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_val_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1402_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_maskAcc_1338_; lean_object* v___y_1349_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__6));
lean_inc(v_stx_1321_);
v___x_1390_ = l_Lean_Syntax_isOfKind(v_stx_1321_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__8));
lean_inc(v_stx_1321_);
v___x_1392_ = l_Lean_Syntax_isOfKind(v_stx_1321_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1400_; 
lean_del_object(v___x_1335_);
lean_dec(v_val_1333_);
lean_del_object(v___x_1330_);
lean_dec(v_val_1328_);
lean_del_object(v___x_1324_);
lean_dec(v_stx_1321_);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_info_1315_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v_info_1315_, 0);
lean_dec(v_unused_1401_);
v___x_1394_ = v_info_1315_;
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v_info_1315_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1400_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = lean_box(0);
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1396_);
v___x_1398_ = v___x_1394_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
else
{
goto v___jp_1353_;
}
}
else
{
goto v___jp_1353_;
}
v___jp_1337_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_st_ref_take(v_val_1313_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v_maskAcc_1338_);
v___x_1341_ = v___x_1324_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_stx_1321_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_maskAcc_1338_);
v___x_1341_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1342_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_1339_, v_val_1333_, v___x_1341_);
v___x_1343_ = lean_st_ref_set(v_val_1313_, v___x_1342_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1343_);
v___x_1345_ = v___x_1335_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
v___jp_1348_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__0));
v___x_1352_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v_val_1328_, v___y_1349_, v___x_1350_, v___x_1351_);
lean_dec_ref(v___y_1349_);
lean_dec(v_val_1328_);
v_maskAcc_1338_ = v___x_1352_;
goto v___jp_1337_;
}
v___jp_1353_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_st_ref_get(v_val_1313_);
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_1354_, v_val_1333_);
lean_dec(v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 1)
{
lean_object* v_val_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1388_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1388_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_val_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1388_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_snd_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1386_; 
v_snd_1360_ = lean_ctor_get(v_val_1356_, 1);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_val_1356_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v_val_1356_, 0);
lean_dec(v_unused_1387_);
v___x_1362_ = v_val_1356_;
v_isShared_1363_ = v_isSharedCheck_1386_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_snd_1360_);
lean_dec(v_val_1356_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1386_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1364_ = lean_array_get_size(v_val_1328_);
v___x_1365_ = lean_array_get_size(v_snd_1360_);
v___x_1366_ = lean_nat_dec_eq(v___x_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1367_ = l_Lean_Elab_Info_stx(v_info_1315_);
lean_dec_ref_known(v_info_1315_, 1);
v___x_1368_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__2);
v___x_1369_ = l_Nat_reprFast(v___x_1365_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set_tag(v___x_1358_, 3);
lean_ctor_set(v___x_1358_, 0, v___x_1369_);
v___x_1371_ = v___x_1358_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = l_Lean_MessageData_ofFormat(v___x_1371_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set_tag(v___x_1362_, 7);
lean_ctor_set(v___x_1362_, 1, v___x_1372_);
lean_ctor_set(v___x_1362_, 0, v___x_1368_);
v___x_1374_ = v___x_1362_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1375_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___closed__4);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Nat_reprFast(v___x_1364_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 3);
lean_ctor_set(v___x_1330_, 0, v___x_1377_);
v___x_1379_ = v___x_1330_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = l_Lean_MessageData_ofFormat(v___x_1379_);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1376_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v___x_1367_, v___x_1381_, v___y_1317_, v___y_1318_);
lean_dec(v___x_1367_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_dec_ref_known(v___x_1382_, 1);
v___y_1349_ = v_snd_1360_;
goto v___jp_1348_;
}
else
{
lean_dec(v_snd_1360_);
lean_del_object(v___x_1335_);
lean_dec(v_val_1333_);
lean_dec(v_val_1328_);
lean_del_object(v___x_1324_);
lean_dec(v_stx_1321_);
return v___x_1382_;
}
}
}
}
}
else
{
lean_del_object(v___x_1362_);
lean_del_object(v___x_1358_);
lean_del_object(v___x_1330_);
lean_dec_ref_known(v_info_1315_, 1);
v___y_1349_ = v_snd_1360_;
goto v___jp_1348_;
}
}
}
}
else
{
lean_dec(v___x_1355_);
lean_del_object(v___x_1330_);
lean_dec_ref_known(v_info_1315_, 1);
v_maskAcc_1338_ = v_val_1328_;
goto v___jp_1337_;
}
}
}
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
lean_dec(v___x_1332_);
lean_dec(v_val_1328_);
lean_del_object(v___x_1324_);
lean_dec(v_stx_1321_);
lean_dec_ref_known(v_info_1315_, 1);
v___x_1403_ = lean_box(0);
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1403_);
v___x_1405_ = v___x_1330_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v___x_1327_);
lean_del_object(v___x_1324_);
lean_dec(v_stx_1321_);
v_isSharedCheck_1415_ = !lean_is_exclusive(v_info_1315_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v_info_1315_, 0);
lean_dec(v_unused_1416_);
v___x_1409_ = v_info_1315_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_info_1315_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = lean_box(0);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref(v_info_1315_);
v___x_1418_ = lean_box(0);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object* v_val_1420_, lean_object* v_ci_1421_, lean_object* v_info_1422_, lean_object* v_x_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v_val_1420_, v_ci_1421_, v_info_1422_, v_x_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec_ref(v_x_1423_);
lean_dec_ref(v_ci_1421_);
lean_dec(v_val_1420_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(lean_object* v_val_1428_, lean_object* v_as_1429_, size_t v_sz_1430_, size_t v_i_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_usize_dec_lt(v_i_1431_, v_sz_1430_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_dec(v_val_1428_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_b_1432_);
return v___x_1437_;
}
else
{
lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v_a_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_inc(v_val_1428_);
v___f_1438_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1438_, 0, v_val_1428_);
v___x_1439_ = lean_box(v___x_1436_);
v___f_1440_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1440_, 0, v___x_1439_);
v_a_1441_ = lean_array_uget_borrowed(v_as_1429_, v_i_1431_);
v___x_1442_ = lean_box(0);
lean_inc(v_a_1441_);
v___x_1443_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v___f_1440_, v___f_1438_, v___x_1442_, v_a_1441_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v___x_1444_; size_t v___x_1445_; size_t v___x_1446_; 
lean_dec_ref_known(v___x_1443_, 1);
v___x_1444_ = lean_box(0);
v___x_1445_ = ((size_t)1ULL);
v___x_1446_ = lean_usize_add(v_i_1431_, v___x_1445_);
v_i_1431_ = v___x_1446_;
v_b_1432_ = v___x_1444_;
goto _start;
}
else
{
lean_dec(v_val_1428_);
return v___x_1443_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object* v_val_1448_, lean_object* v_as_1449_, lean_object* v_sz_1450_, lean_object* v_i_1451_, lean_object* v_b_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
size_t v_sz_boxed_1456_; size_t v_i_boxed_1457_; lean_object* v_res_1458_; 
v_sz_boxed_1456_ = lean_unbox_usize(v_sz_1450_);
lean_dec(v_sz_1450_);
v_i_boxed_1457_ = lean_unbox_usize(v_i_1451_);
lean_dec(v_i_1451_);
v_res_1458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v_val_1448_, v_as_1449_, v_sz_boxed_1456_, v_i_boxed_1457_, v_b_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec_ref(v_as_1449_);
return v_res_1458_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_unsigned_to_nat(16u);
v___x_1461_ = lean_mk_array(v___x_1460_, v___x_1459_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__0, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
lean_ctor_set(v___x_1464_, 1, v___x_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0(lean_object* v_cmdStx_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1539_; 
v___x_1469_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_1466_, v___y_1467_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1539_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1539_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; uint8_t v___x_1475_; uint8_t v___x_1476_; 
v___x_1474_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_1475_ = l_Lean_Linter_getLinterValue(v___x_1474_, v_a_1470_);
lean_dec(v_a_1470_);
v___x_1476_ = lean_bool_not(v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1465_, v___x_1476_);
if (lean_obj_tag(v___x_1477_) == 1)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_infoState_1482_; lean_object* v_trees_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; size_t v_sz_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
lean_dec_ref_known(v___x_1477_, 1);
lean_del_object(v___x_1472_);
v___x_1478_ = lean_st_ref_get(v___y_1467_);
v___x_1479_ = lean_unsigned_to_nat(0u);
v___x_1480_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__1, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1);
v___x_1481_ = lean_st_mk_ref(v___x_1480_);
v_infoState_1482_ = lean_ctor_get(v___x_1478_, 8);
lean_inc_ref(v_infoState_1482_);
lean_dec(v___x_1478_);
v_trees_1483_ = lean_ctor_get(v_infoState_1482_, 2);
lean_inc_ref(v_trees_1483_);
lean_dec_ref(v_infoState_1482_);
v___x_1484_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1483_);
lean_dec_ref(v_trees_1483_);
v___x_1485_ = lean_box(0);
v_sz_1486_ = lean_array_size(v___x_1484_);
v___x_1487_ = ((size_t)0ULL);
lean_inc(v___x_1481_);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_1481_, v___x_1484_, v_sz_1486_, v___x_1487_, v___x_1485_, v___y_1466_, v___y_1467_);
lean_dec_ref(v___x_1484_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1489_; lean_object* v___y_1491_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1515_; lean_object* v_size_1521_; lean_object* v_buckets_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
lean_dec_ref_known(v___x_1488_, 1);
v___x_1489_ = lean_st_ref_get(v___x_1481_);
lean_dec(v___x_1481_);
v_size_1521_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_size_1521_);
v_buckets_1522_ = lean_ctor_get(v___x_1489_, 1);
lean_inc_ref(v_buckets_1522_);
lean_dec(v___x_1489_);
v___x_1523_ = lean_mk_empty_array_with_capacity(v_size_1521_);
lean_dec(v_size_1521_);
v___x_1524_ = lean_array_get_size(v_buckets_1522_);
v___x_1525_ = lean_nat_dec_lt(v___x_1479_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_dec_ref(v_buckets_1522_);
v___y_1515_ = v___x_1523_;
goto v___jp_1514_;
}
else
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_nat_dec_le(v___x_1524_, v___x_1524_);
if (v___x_1526_ == 0)
{
if (v___x_1525_ == 0)
{
lean_dec_ref(v_buckets_1522_);
v___y_1515_ = v___x_1523_;
goto v___jp_1514_;
}
else
{
size_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = lean_usize_of_nat(v___x_1524_);
v___x_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_1522_, v___x_1487_, v___x_1527_, v___x_1523_);
lean_dec_ref(v_buckets_1522_);
v___y_1515_ = v___x_1528_;
goto v___jp_1514_;
}
}
else
{
size_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_usize_of_nat(v___x_1524_);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_1522_, v___x_1487_, v___x_1529_, v___x_1523_);
lean_dec_ref(v_buckets_1522_);
v___y_1515_ = v___x_1530_;
goto v___jp_1514_;
}
}
v___jp_1490_:
{
size_t v_sz_1492_; lean_object* v___x_1493_; 
v_sz_1492_ = lean_array_size(v___y_1491_);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___y_1491_, v_sz_1492_, v___x_1487_, v___x_1485_, v___y_1466_, v___y_1467_);
lean_dec_ref(v___y_1491_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v___x_1493_, 0);
lean_dec(v_unused_1501_);
v___x_1495_ = v___x_1493_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v___x_1493_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1485_);
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1485_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
else
{
return v___x_1493_;
}
}
v___jp_1502_:
{
lean_object* v___x_1507_; 
v___x_1507_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v___y_1505_, v___y_1504_, v___y_1503_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec(v___y_1505_);
v___y_1491_ = v___x_1507_;
goto v___jp_1490_;
}
v___jp_1508_:
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_nat_dec_le(v___y_1512_, v___y_1509_);
if (v___x_1513_ == 0)
{
lean_dec(v___y_1509_);
lean_inc(v___y_1512_);
v___y_1503_ = v___y_1512_;
v___y_1504_ = v___y_1511_;
v___y_1505_ = v___y_1510_;
v___y_1506_ = v___y_1512_;
goto v___jp_1502_;
}
else
{
v___y_1503_ = v___y_1512_;
v___y_1504_ = v___y_1511_;
v___y_1505_ = v___y_1510_;
v___y_1506_ = v___y_1509_;
goto v___jp_1502_;
}
}
v___jp_1514_:
{
lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1516_ = lean_array_get_size(v___y_1515_);
v___x_1517_ = lean_nat_dec_eq(v___x_1516_, v___x_1479_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = lean_nat_sub(v___x_1516_, v___x_1518_);
v___x_1520_ = lean_nat_dec_le(v___x_1479_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_inc(v___x_1519_);
v___y_1509_ = v___x_1519_;
v___y_1510_ = v___x_1516_;
v___y_1511_ = v___y_1515_;
v___y_1512_ = v___x_1519_;
goto v___jp_1508_;
}
else
{
v___y_1509_ = v___x_1519_;
v___y_1510_ = v___x_1516_;
v___y_1511_ = v___y_1515_;
v___y_1512_ = v___x_1479_;
goto v___jp_1508_;
}
}
else
{
v___y_1491_ = v___y_1515_;
goto v___jp_1490_;
}
}
}
else
{
lean_dec(v___x_1481_);
return v___x_1488_;
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
lean_dec(v___x_1477_);
v___x_1531_ = lean_box(0);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1531_);
v___x_1533_ = v___x_1472_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = lean_box(0);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1535_);
v___x_1537_ = v___x_1472_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___boxed(lean_object* v_cmdStx_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_cmdStx_1540_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(lean_object* v_o_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_1556_, v___y_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(lean_object* v_o_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object* v_00_u03b2_1566_, lean_object* v_m_1567_, lean_object* v_a_1568_, lean_object* v_b_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_1567_, v_a_1568_, v_b_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object* v_00_u03b2_1571_, lean_object* v_m_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_1572_, v_a_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object* v_00_u03b2_1575_, lean_object* v_m_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(v_00_u03b2_1575_, v_m_1576_, v_a_1577_);
lean_dec_ref(v_a_1577_);
lean_dec_ref(v_m_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(lean_object* v_00_u03b1_1579_, lean_object* v_ref_1580_, lean_object* v_msg_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_1580_, v_msg_1581_, v___y_1582_, v___y_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object* v_00_u03b1_1586_, lean_object* v_ref_1587_, lean_object* v_msg_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(v_00_u03b1_1586_, v_ref_1587_, v_msg_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v_ref_1587_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object* v_upperBound_1593_, lean_object* v_snd_1594_, lean_object* v_fst_1595_, lean_object* v_inst_1596_, lean_object* v_R_1597_, lean_object* v_a_1598_, lean_object* v_b_1599_, lean_object* v_c_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_1593_, v_snd_1594_, v_fst_1595_, v_a_1598_, v_b_1599_, v___y_1601_, v___y_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object* v_upperBound_1605_, lean_object* v_snd_1606_, lean_object* v_fst_1607_, lean_object* v_inst_1608_, lean_object* v_R_1609_, lean_object* v_a_1610_, lean_object* v_b_1611_, lean_object* v_c_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(v_upperBound_1605_, v_snd_1606_, v_fst_1607_, v_inst_1608_, v_R_1609_, v_a_1610_, v_b_1611_, v_c_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v_snd_1606_);
lean_dec(v_upperBound_1605_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object* v_n_1617_, lean_object* v_as_1618_, lean_object* v_lo_1619_, lean_object* v_hi_1620_, lean_object* v_w_1621_, lean_object* v_hlo_1622_, lean_object* v_hhi_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_1617_, v_as_1618_, v_lo_1619_, v_hi_1620_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object* v_n_1625_, lean_object* v_as_1626_, lean_object* v_lo_1627_, lean_object* v_hi_1628_, lean_object* v_w_1629_, lean_object* v_hlo_1630_, lean_object* v_hhi_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(v_n_1625_, v_as_1626_, v_lo_1627_, v_hi_1628_, v_w_1629_, v_hlo_1630_, v_hhi_1631_);
lean_dec(v_hi_1628_);
lean_dec(v_n_1625_);
return v_res_1632_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object* v_00_u03b2_1633_, lean_object* v_a_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_a_1638_, lean_object* v_x_1639_){
_start:
{
uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_res_1640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_1637_, v_a_1638_, v_x_1639_);
lean_dec(v_x_1639_);
lean_dec_ref(v_a_1638_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(lean_object* v_00_u03b2_1642_, lean_object* v_data_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_data_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(lean_object* v_00_u03b2_1645_, lean_object* v_a_1646_, lean_object* v_b_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1646_, v_b_1647_, v_x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(lean_object* v_00_u03b2_1650_, lean_object* v_a_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_1651_, v_x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1654_, lean_object* v_a_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(v_00_u03b2_1654_, v_a_1655_, v_x_1656_);
lean_dec(v_x_1656_);
lean_dec_ref(v_a_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(lean_object* v_msgData_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_1658_, v___y_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(lean_object* v_msgData_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(lean_object* v_00_u03b1_1668_, lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_1669_, v___y_1670_, v___y_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1674_, lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(v_00_u03b1_1674_, v_msg_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_object* v_00_u03b1_1680_, lean_object* v_msg_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1681_, v___y_1682_, v___y_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1686_, lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(v_00_u03b1_1686_, v_msg_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_object* v_00_u03b1_1692_, lean_object* v_preNode_1693_, lean_object* v_postNode_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1693_, v_postNode_1694_, v_x_1695_, v_x_1696_, v___y_1697_, v___y_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_preNode_1702_, lean_object* v_postNode_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(v_00_u03b1_1701_, v_preNode_1702_, v_postNode_1703_, v_x_1704_, v_x_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(lean_object* v_n_1710_, lean_object* v_lo_1711_, lean_object* v_hi_1712_, lean_object* v_hhi_1713_, lean_object* v_pivot_1714_, lean_object* v_as_1715_, lean_object* v_i_1716_, lean_object* v_k_1717_, lean_object* v_ilo_1718_, lean_object* v_ik_1719_, lean_object* v_w_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_1712_, v_pivot_1714_, v_as_1715_, v_i_1716_, v_k_1717_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(lean_object* v_n_1722_, lean_object* v_lo_1723_, lean_object* v_hi_1724_, lean_object* v_hhi_1725_, lean_object* v_pivot_1726_, lean_object* v_as_1727_, lean_object* v_i_1728_, lean_object* v_k_1729_, lean_object* v_ilo_1730_, lean_object* v_ik_1731_, lean_object* v_w_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(v_n_1722_, v_lo_1723_, v_hi_1724_, v_hhi_1725_, v_pivot_1726_, v_as_1727_, v_i_1728_, v_k_1729_, v_ilo_1730_, v_ik_1731_, v_w_1732_);
lean_dec_ref(v_pivot_1726_);
lean_dec(v_hi_1724_);
lean_dec(v_lo_1723_);
lean_dec(v_n_1722_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1734_, lean_object* v_i_1735_, lean_object* v_source_1736_, lean_object* v_target_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v_i_1735_, v_source_1736_, v_target_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(lean_object* v_msgData_1739_, lean_object* v_macroStack_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_1739_, v_macroStack_1740_, v___y_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_1745_, lean_object* v_macroStack_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_1745_, v_macroStack_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_object* v_00_u03b1_1751_, lean_object* v_preNode_1752_, lean_object* v_postNode_1753_, lean_object* v___x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1752_, v_postNode_1753_, v___x_1754_, v_x_1755_, v_x_1756_, v___y_1757_, v___y_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_preNode_1762_, lean_object* v_postNode_1763_, lean_object* v___x_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(v_00_u03b1_1761_, v_preNode_1762_, v_postNode_1763_, v___x_1764_, v_x_1765_, v_x_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1771_, lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_x_1772_, v_x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_Linter_unusedSimpArgs));
v___x_1777_ = l_Lean_Elab_Command_addLinter(v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
return v_res_1779_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_UnusedSimpArgs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
