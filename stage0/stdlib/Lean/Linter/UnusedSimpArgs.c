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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_88_, uint8_t v___y_89_, lean_object* v_x_90_){
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
return v___x_98_;
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_100_ = lean_string_dec_eq(v_str_93_, v___x_99_);
if (v___x_100_ == 0)
{
return v___x_100_;
}
else
{
return v_suppressElabErrors_88_;
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
return v___x_102_;
}
else
{
return v_suppressElabErrors_88_;
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
return v___x_108_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_110_ = lean_string_dec_eq(v_str_105_, v___x_109_);
if (v___x_110_ == 0)
{
return v___x_110_;
}
else
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_112_ = lean_string_dec_eq(v_str_104_, v___x_111_);
if (v___x_112_ == 0)
{
return v___x_112_;
}
else
{
return v_suppressElabErrors_88_;
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
lean_object* v_str_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v_str_113_ = lean_ctor_get(v_x_90_, 1);
v___x_114_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_115_ = lean_string_dec_eq(v_str_113_, v___x_114_);
if (v___x_115_ == 0)
{
return v___x_115_;
}
else
{
return v_suppressElabErrors_88_;
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
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_116_, lean_object* v___y_117_, lean_object* v_x_118_){
_start:
{
uint8_t v_suppressElabErrors_boxed_119_; uint8_t v___y_4716__boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v_suppressElabErrors_boxed_119_ = lean_unbox(v_suppressElabErrors_116_);
v___y_4716__boxed_120_ = lean_unbox(v___y_117_);
v_res_121_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_119_, v___y_4716__boxed_120_, v_x_118_);
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
lean_object* v___y_146_; lean_object* v___y_147_; uint8_t v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; uint8_t v___y_151_; lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_182_; uint8_t v___y_183_; lean_object* v___y_184_; uint8_t v___y_185_; lean_object* v___y_186_; uint8_t v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_207_; uint8_t v___y_208_; lean_object* v___y_209_; uint8_t v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; uint8_t v___y_213_; lean_object* v___y_214_; lean_object* v___y_218_; uint8_t v___y_219_; lean_object* v___y_220_; uint8_t v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; uint8_t v___y_224_; uint8_t v___x_229_; uint8_t v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; uint8_t v___y_236_; uint8_t v___y_237_; uint8_t v___y_239_; uint8_t v___x_254_; 
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
lean_ctor_set(v___x_171_, 1, v___y_146_);
lean_inc_ref(v___y_150_);
lean_inc_ref(v___y_147_);
v___x_172_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_172_, 0, v___y_147_);
lean_ctor_set(v___x_172_, 1, v___y_152_);
lean_ctor_set(v___x_172_, 2, v___y_149_);
lean_ctor_set(v___x_172_, 3, v___y_150_);
lean_ctor_set(v___x_172_, 4, v___x_171_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*5, v___y_148_);
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
lean_inc_ref_n(v___y_188_, 2);
v___x_196_ = l_Lean_FileMap_toPosition(v___y_188_, v___y_186_);
lean_dec(v___y_186_);
v___x_197_ = l_Lean_FileMap_toPosition(v___y_188_, v___y_189_);
lean_dec(v___y_189_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
v___x_199_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0));
if (v___y_183_ == 0)
{
lean_del_object(v___x_194_);
lean_dec_ref(v___y_182_);
v___y_146_ = v_a_192_;
v___y_147_ = v___y_184_;
v___y_148_ = v___y_185_;
v___y_149_ = v___x_198_;
v___y_150_ = v___x_199_;
v___y_151_ = v___y_187_;
v___y_152_ = v___x_196_;
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
v___y_146_ = v_a_192_;
v___y_147_ = v___y_184_;
v___y_148_ = v___y_185_;
v___y_149_ = v___x_198_;
v___y_150_ = v___x_199_;
v___y_151_ = v___y_187_;
v___y_152_ = v___x_196_;
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
v___x_215_ = l_Lean_Syntax_getTailPos_x3f(v___y_211_, v___y_210_);
lean_dec(v___y_211_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_inc(v___y_214_);
v___y_182_ = v___y_207_;
v___y_183_ = v___y_208_;
v___y_184_ = v___y_209_;
v___y_185_ = v___y_210_;
v___y_186_ = v___y_214_;
v___y_187_ = v___y_213_;
v___y_188_ = v___y_212_;
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
v___y_183_ = v___y_208_;
v___y_184_ = v___y_209_;
v___y_185_ = v___y_210_;
v___y_186_ = v___y_214_;
v___y_187_ = v___y_213_;
v___y_188_ = v___y_212_;
v___y_189_ = v_val_216_;
goto v___jp_181_;
}
}
v___jp_217_:
{
lean_object* v_ref_225_; lean_object* v___x_226_; 
v_ref_225_ = l_Lean_replaceRef(v_ref_138_, v___y_222_);
v___x_226_ = l_Lean_Syntax_getPos_x3f(v_ref_225_, v___y_221_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___y_207_ = v___y_218_;
v___y_208_ = v___y_219_;
v___y_209_ = v___y_220_;
v___y_210_ = v___y_221_;
v___y_211_ = v_ref_225_;
v___y_212_ = v___y_223_;
v___y_213_ = v___y_224_;
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
v___y_208_ = v___y_219_;
v___y_209_ = v___y_220_;
v___y_210_ = v___y_221_;
v___y_211_ = v_ref_225_;
v___y_212_ = v___y_223_;
v___y_213_ = v___y_224_;
v___y_214_ = v_val_228_;
goto v___jp_206_;
}
}
v___jp_230_:
{
if (v___y_237_ == 0)
{
v___y_218_ = v___y_233_;
v___y_219_ = v___y_231_;
v___y_220_ = v___y_232_;
v___y_221_ = v___y_236_;
v___y_222_ = v___y_234_;
v___y_223_ = v___y_235_;
v___y_224_ = v_severity_140_;
goto v___jp_217_;
}
else
{
v___y_218_ = v___y_233_;
v___y_219_ = v___y_231_;
v___y_220_ = v___y_232_;
v___y_221_ = v___y_236_;
v___y_222_ = v___y_234_;
v___y_223_ = v___y_235_;
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
v___x_245_ = lean_box(v_suppressElabErrors_244_);
v___x_246_ = lean_box(v___y_239_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_247_, 0, v___x_245_);
lean_closure_set(v___f_247_, 1, v___x_246_);
v___x_248_ = 1;
v___x_249_ = l_Lean_instBEqMessageSeverity_beq(v_severity_140_, v___x_248_);
if (v___x_249_ == 0)
{
v___y_231_ = v_suppressElabErrors_244_;
v___y_232_ = v_fileName_240_;
v___y_233_ = v___f_247_;
v___y_234_ = v_ref_243_;
v___y_235_ = v_fileMap_241_;
v___y_236_ = v___y_239_;
v___y_237_ = v___x_249_;
goto v___jp_230_;
}
else
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = l_Lean_warningAsError;
v___x_251_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_options_242_, v___x_250_);
v___y_231_ = v_suppressElabErrors_244_;
v___y_232_ = v_fileName_240_;
v___y_233_ = v___f_247_;
v___y_234_ = v_ref_243_;
v___y_235_ = v_fileMap_241_;
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
lean_ctor_set(v___x_363_, 0, v___y_358_);
lean_ctor_set(v___x_363_, 1, v_hint_359_);
v___x_364_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_362_, v___y_357_, v___x_363_, v___y_360_, v___y_361_);
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
v___y_357_ = v_argStx_373_;
v___y_358_ = v_msg_394_;
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
v___y_357_ = v_argStx_373_;
v___y_358_ = v_msg_394_;
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
v___y_357_ = v_argStx_373_;
v___y_358_ = v_msg_394_;
v_hint_359_ = v___x_401_;
v___y_360_ = v___y_369_;
v___y_361_ = v___y_370_;
goto v___jp_356_;
}
}
else
{
v___y_357_ = v_argStx_373_;
v___y_358_ = v_msg_394_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object* v_upperBound_472_, lean_object* v_snd_473_, lean_object* v_fst_474_, lean_object* v_a_475_, lean_object* v_b_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_a_481_; uint8_t v___x_485_; 
v___x_485_ = lean_nat_dec_lt(v_a_475_, v_upperBound_472_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec(v_a_475_);
lean_dec(v_fst_474_);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v_b_476_);
return v___x_486_;
}
else
{
uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_487_ = 0;
v___x_488_ = lean_box(0);
v___x_489_ = lean_box(v___x_487_);
v___x_490_ = lean_array_get(v___x_489_, v_snd_473_, v_a_475_);
lean_dec(v___x_489_);
v___x_491_ = lean_unbox(v___x_490_);
lean_dec(v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc(v_a_475_);
lean_inc(v_fst_474_);
v___x_492_ = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed), 5, 2);
lean_closure_set(v___x_492_, 0, v_fst_474_);
lean_closure_set(v___x_492_, 1, v_a_475_);
v___x_493_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_492_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_dec_ref_known(v___x_493_, 1);
v_a_481_ = v___x_488_;
goto v___jp_480_;
}
else
{
lean_dec(v_a_475_);
lean_dec(v_fst_474_);
return v___x_493_;
}
}
else
{
v_a_481_ = v___x_488_;
goto v___jp_480_;
}
}
v___jp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_add(v_a_475_, v___x_482_);
lean_dec(v_a_475_);
v_a_475_ = v___x_483_;
v_b_476_ = v_a_481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object* v_upperBound_494_, lean_object* v_snd_495_, lean_object* v_fst_496_, lean_object* v_a_497_, lean_object* v_b_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_494_, v_snd_495_, v_fst_496_, v_a_497_, v_b_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec_ref(v_snd_495_);
lean_dec(v_upperBound_494_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(lean_object* v_as_503_, size_t v_sz_504_, size_t v_i_505_, lean_object* v_b_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_lt(v_i_505_, v_sz_504_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_b_506_);
return v___x_511_;
}
else
{
lean_object* v_a_512_; lean_object* v_snd_513_; lean_object* v_fst_514_; lean_object* v_snd_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_a_512_ = lean_array_uget_borrowed(v_as_503_, v_i_505_);
v_snd_513_ = lean_ctor_get(v_a_512_, 1);
v_fst_514_ = lean_ctor_get(v_snd_513_, 0);
v_snd_515_ = lean_ctor_get(v_snd_513_, 1);
v___x_516_ = lean_box(0);
v___x_517_ = lean_array_get_size(v_snd_515_);
v___x_518_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_514_);
v___x_519_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_517_, v_snd_515_, v_fst_514_, v___x_518_, v___x_516_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_519_) == 0)
{
size_t v___x_520_; size_t v___x_521_; 
lean_dec_ref_known(v___x_519_, 1);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_add(v_i_505_, v___x_520_);
v_i_505_ = v___x_521_;
v_b_506_ = v___x_516_;
goto _start;
}
else
{
return v___x_519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object* v_as_523_, lean_object* v_sz_524_, lean_object* v_i_525_, lean_object* v_b_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
size_t v_sz_boxed_530_; size_t v_i_boxed_531_; lean_object* v_res_532_; 
v_sz_boxed_530_ = lean_unbox_usize(v_sz_524_);
lean_dec(v_sz_524_);
v_i_boxed_531_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_523_, v_sz_boxed_530_, v_i_boxed_531_, v_b_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v_as_523_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(lean_object* v_hi_533_, lean_object* v_pivot_534_, lean_object* v_as_535_, lean_object* v_i_536_, lean_object* v_k_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_nat_dec_lt(v_k_537_, v_hi_533_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v_k_537_);
v___x_539_ = lean_array_fswap(v_as_535_, v_i_536_, v_hi_533_);
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v_i_536_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v_fst_542_; lean_object* v_fst_543_; lean_object* v_start_544_; lean_object* v_start_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_541_ = lean_array_fget_borrowed(v_as_535_, v_k_537_);
v_fst_542_ = lean_ctor_get(v___x_541_, 0);
v_fst_543_ = lean_ctor_get(v_pivot_534_, 0);
v_start_544_ = lean_ctor_get(v_fst_542_, 0);
v_start_545_ = lean_ctor_get(v_fst_543_, 0);
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_add(v_start_544_, v___x_546_);
v___x_548_ = lean_nat_dec_le(v___x_547_, v_start_545_);
lean_dec(v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
v___x_549_ = lean_nat_add(v_k_537_, v___x_546_);
lean_dec(v_k_537_);
v_k_537_ = v___x_549_;
goto _start;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_array_fswap(v_as_535_, v_i_536_, v_k_537_);
v___x_552_ = lean_nat_add(v_i_536_, v___x_546_);
lean_dec(v_i_536_);
v___x_553_ = lean_nat_add(v_k_537_, v___x_546_);
lean_dec(v_k_537_);
v_as_535_ = v___x_551_;
v_i_536_ = v___x_552_;
v_k_537_ = v___x_553_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg___boxed(lean_object* v_hi_555_, lean_object* v_pivot_556_, lean_object* v_as_557_, lean_object* v_i_558_, lean_object* v_k_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_555_, v_pivot_556_, v_as_557_, v_i_558_, v_k_559_);
lean_dec_ref(v_pivot_556_);
lean_dec(v_hi_555_);
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(lean_object* v_x1_561_, lean_object* v_x2_562_){
_start:
{
lean_object* v_fst_563_; lean_object* v_fst_564_; lean_object* v_start_565_; lean_object* v_start_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_fst_563_ = lean_ctor_get(v_x1_561_, 0);
v_fst_564_ = lean_ctor_get(v_x2_562_, 0);
v_start_565_ = lean_ctor_get(v_fst_563_, 0);
v_start_566_ = lean_ctor_get(v_fst_564_, 0);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_start_565_, v___x_567_);
v___x_569_ = lean_nat_dec_le(v___x_568_, v_start_566_);
lean_dec(v___x_568_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(lean_object* v_a_680_, lean_object* v_x_681_){
_start:
{
if (lean_obj_tag(v_x_681_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_box(0);
return v___x_682_;
}
else
{
lean_object* v_key_683_; lean_object* v_value_684_; lean_object* v_tail_685_; uint8_t v___x_686_; 
v_key_683_ = lean_ctor_get(v_x_681_, 0);
v_value_684_ = lean_ctor_get(v_x_681_, 1);
v_tail_685_ = lean_ctor_get(v_x_681_, 2);
v___x_686_ = l_Lean_Syntax_instBEqRange_beq(v_key_683_, v_a_680_);
if (v___x_686_ == 0)
{
v_x_681_ = v_tail_685_;
goto _start;
}
else
{
lean_object* v___x_688_; 
lean_inc(v_value_684_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_value_684_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(lean_object* v_a_689_, lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_689_, v_x_690_);
lean_dec(v_x_690_);
lean_dec_ref(v_a_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object* v_m_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_buckets_694_; lean_object* v___x_695_; uint64_t v___x_696_; uint64_t v___x_697_; uint64_t v___x_698_; uint64_t v_fold_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v___x_705_; size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_buckets_694_ = lean_ctor_get(v_m_692_, 1);
v___x_695_ = lean_array_get_size(v_buckets_694_);
v___x_696_ = l_Lean_Syntax_instHashableRange_hash(v_a_693_);
v___x_697_ = 32ULL;
v___x_698_ = lean_uint64_shift_right(v___x_696_, v___x_697_);
v_fold_699_ = lean_uint64_xor(v___x_696_, v___x_698_);
v___x_700_ = 16ULL;
v___x_701_ = lean_uint64_shift_right(v_fold_699_, v___x_700_);
v___x_702_ = lean_uint64_xor(v_fold_699_, v___x_701_);
v___x_703_ = lean_uint64_to_usize(v___x_702_);
v___x_704_ = lean_usize_of_nat(v___x_695_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_sub(v___x_704_, v___x_705_);
v___x_707_ = lean_usize_land(v___x_703_, v___x_706_);
v___x_708_ = lean_array_uget_borrowed(v_buckets_694_, v___x_707_);
v___x_709_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_693_, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object* v_m_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_710_, v_a_711_);
lean_dec_ref(v_a_711_);
lean_dec_ref(v_m_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(uint8_t v___x_713_, lean_object* v_as_714_, lean_object* v_bs_715_, lean_object* v_i_716_, lean_object* v_cs_717_){
_start:
{
uint8_t v___y_719_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = lean_array_get_size(v_as_714_);
v___x_726_ = lean_nat_dec_lt(v_i_716_, v___x_725_);
if (v___x_726_ == 0)
{
lean_dec(v_i_716_);
return v_cs_717_;
}
else
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_array_get_size(v_bs_715_);
v___x_728_ = lean_nat_dec_lt(v_i_716_, v___x_727_);
if (v___x_728_ == 0)
{
lean_dec(v_i_716_);
return v_cs_717_;
}
else
{
lean_object* v_a_729_; uint8_t v___x_730_; 
v_a_729_ = lean_array_fget_borrowed(v_as_714_, v_i_716_);
v___x_730_ = lean_unbox(v_a_729_);
if (v___x_730_ == 0)
{
lean_object* v_b_731_; uint8_t v___x_732_; 
v_b_731_ = lean_array_fget_borrowed(v_bs_715_, v_i_716_);
v___x_732_ = lean_unbox(v_b_731_);
v___y_719_ = v___x_732_;
goto v___jp_718_;
}
else
{
v___y_719_ = v___x_713_;
goto v___jp_718_;
}
}
}
v___jp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_i_716_, v___x_720_);
lean_dec(v_i_716_);
v___x_722_ = lean_box(v___y_719_);
v___x_723_ = lean_array_push(v_cs_717_, v___x_722_);
v_i_716_ = v___x_721_;
v_cs_717_ = v___x_723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object* v___x_733_, lean_object* v_as_734_, lean_object* v_bs_735_, lean_object* v_i_736_, lean_object* v_cs_737_){
_start:
{
uint8_t v___x_12819__boxed_738_; lean_object* v_res_739_; 
v___x_12819__boxed_738_ = lean_unbox(v___x_733_);
v_res_739_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_12819__boxed_738_, v_as_734_, v_bs_735_, v_i_736_, v_cs_737_);
lean_dec_ref(v_bs_735_);
lean_dec_ref(v_as_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(lean_object* v_msgData_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; lean_object* v_env_744_; lean_object* v___x_745_; lean_object* v_scopes_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_opts_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_743_ = lean_st_ref_get(v___y_741_);
v_env_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_env_744_);
lean_dec(v___x_743_);
v___x_745_ = lean_st_ref_get(v___y_741_);
v_scopes_746_ = lean_ctor_get(v___x_745_, 2);
lean_inc(v_scopes_746_);
lean_dec(v___x_745_);
v___x_747_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_748_ = l_List_head_x21___redArg(v___x_747_, v_scopes_746_);
lean_dec(v_scopes_746_);
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
lean_ctor_set(v___x_755_, 1, v_msgData_740_);
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
lean_object* v___x_803_; lean_object* v_scopes_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v_opts_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_803_ = lean_st_ref_get(v___y_801_);
v_scopes_804_ = lean_ctor_get(v___x_803_, 2);
lean_inc(v_scopes_804_);
lean_dec(v___x_803_);
v___x_805_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_806_ = l_List_head_x21___redArg(v___x_805_, v_scopes_804_);
lean_dec(v_scopes_804_);
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
lean_object* v_a_840_; lean_object* v_macroStack_841_; lean_object* v___x_842_; lean_object* v_a_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v_macroStack_841_ = lean_ctor_get(v___y_836_, 4);
v___x_842_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msg_835_, v___y_837_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref(v___x_842_);
v___x_844_ = l_Lean_Elab_getBetterRef(v_a_840_, v_macroStack_841_);
lean_dec(v_a_840_);
lean_inc(v_macroStack_841_);
v___x_845_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_a_843_, v_macroStack_841_, v___y_837_);
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
lean_ctor_set(v___x_850_, 0, v___x_844_);
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
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v_nbuckets_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_943_ = lean_array_get_size(v_data_942_);
v___x_944_ = lean_unsigned_to_nat(2u);
v_nbuckets_945_ = lean_nat_mul(v___x_943_, v___x_944_);
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_box(0);
v___x_948_ = lean_mk_array(v_nbuckets_945_, v___x_947_);
v___x_949_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v___x_946_, v_data_942_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object* v_a_950_, lean_object* v_x_951_){
_start:
{
if (lean_obj_tag(v_x_951_) == 0)
{
uint8_t v___x_952_; 
v___x_952_ = 0;
return v___x_952_;
}
else
{
lean_object* v_key_953_; lean_object* v_tail_954_; uint8_t v___x_955_; 
v_key_953_ = lean_ctor_get(v_x_951_, 0);
v_tail_954_ = lean_ctor_get(v_x_951_, 2);
v___x_955_ = l_Lean_Syntax_instBEqRange_beq(v_key_953_, v_a_950_);
if (v___x_955_ == 0)
{
v_x_951_ = v_tail_954_;
goto _start;
}
else
{
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object* v_a_957_, lean_object* v_x_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_957_, v_x_958_);
lean_dec(v_x_958_);
lean_dec_ref(v_a_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(lean_object* v_a_961_, lean_object* v_b_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_963_) == 0)
{
lean_dec(v_b_962_);
lean_dec_ref(v_a_961_);
return v_x_963_;
}
else
{
lean_object* v_key_964_; lean_object* v_value_965_; lean_object* v_tail_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_978_; 
v_key_964_ = lean_ctor_get(v_x_963_, 0);
v_value_965_ = lean_ctor_get(v_x_963_, 1);
v_tail_966_ = lean_ctor_get(v_x_963_, 2);
v_isSharedCheck_978_ = !lean_is_exclusive(v_x_963_);
if (v_isSharedCheck_978_ == 0)
{
v___x_968_ = v_x_963_;
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_tail_966_);
lean_inc(v_value_965_);
lean_inc(v_key_964_);
lean_dec(v_x_963_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_978_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
uint8_t v___x_970_; 
v___x_970_ = l_Lean_Syntax_instBEqRange_beq(v_key_964_, v_a_961_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_961_, v_b_962_, v_tail_966_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 2, v___x_971_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_key_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_value_965_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
else
{
lean_object* v___x_976_; 
lean_dec(v_value_965_);
lean_dec(v_key_964_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 1, v_b_962_);
lean_ctor_set(v___x_968_, 0, v_a_961_);
v___x_976_ = v___x_968_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_961_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_b_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_tail_966_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object* v_m_979_, lean_object* v_a_980_, lean_object* v_b_981_){
_start:
{
lean_object* v_size_982_; lean_object* v_buckets_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1026_; 
v_size_982_ = lean_ctor_get(v_m_979_, 0);
v_buckets_983_ = lean_ctor_get(v_m_979_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_m_979_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_985_ = v_m_979_;
v_isShared_986_ = v_isSharedCheck_1026_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_buckets_983_);
lean_inc(v_size_982_);
lean_dec(v_m_979_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1026_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; uint64_t v___x_988_; uint64_t v___x_989_; uint64_t v___x_990_; uint64_t v_fold_991_; uint64_t v___x_992_; uint64_t v___x_993_; uint64_t v___x_994_; size_t v___x_995_; size_t v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; lean_object* v_bkt_1000_; uint8_t v___x_1001_; 
v___x_987_ = lean_array_get_size(v_buckets_983_);
v___x_988_ = l_Lean_Syntax_instHashableRange_hash(v_a_980_);
v___x_989_ = 32ULL;
v___x_990_ = lean_uint64_shift_right(v___x_988_, v___x_989_);
v_fold_991_ = lean_uint64_xor(v___x_988_, v___x_990_);
v___x_992_ = 16ULL;
v___x_993_ = lean_uint64_shift_right(v_fold_991_, v___x_992_);
v___x_994_ = lean_uint64_xor(v_fold_991_, v___x_993_);
v___x_995_ = lean_uint64_to_usize(v___x_994_);
v___x_996_ = lean_usize_of_nat(v___x_987_);
v___x_997_ = ((size_t)1ULL);
v___x_998_ = lean_usize_sub(v___x_996_, v___x_997_);
v___x_999_ = lean_usize_land(v___x_995_, v___x_998_);
v_bkt_1000_ = lean_array_uget_borrowed(v_buckets_983_, v___x_999_);
v___x_1001_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_980_, v_bkt_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v_size_x27_1003_; lean_object* v___x_1004_; lean_object* v_buckets_x27_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v_size_x27_1003_ = lean_nat_add(v_size_982_, v___x_1002_);
lean_dec(v_size_982_);
lean_inc(v_bkt_1000_);
v___x_1004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1004_, 0, v_a_980_);
lean_ctor_set(v___x_1004_, 1, v_b_981_);
lean_ctor_set(v___x_1004_, 2, v_bkt_1000_);
v_buckets_x27_1005_ = lean_array_uset(v_buckets_983_, v___x_999_, v___x_1004_);
v___x_1006_ = lean_unsigned_to_nat(4u);
v___x_1007_ = lean_nat_mul(v_size_x27_1003_, v___x_1006_);
v___x_1008_ = lean_unsigned_to_nat(3u);
v___x_1009_ = lean_nat_div(v___x_1007_, v___x_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_array_get_size(v_buckets_x27_1005_);
v___x_1011_ = lean_nat_dec_le(v___x_1009_, v___x_1010_);
lean_dec(v___x_1009_);
if (v___x_1011_ == 0)
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
v_val_1012_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_buckets_x27_1005_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v_val_1012_);
lean_ctor_set(v___x_985_, 0, v_size_x27_1003_);
v___x_1014_ = v___x_985_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_size_x27_1003_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_val_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v___x_1017_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v_buckets_x27_1005_);
lean_ctor_set(v___x_985_, 0, v_size_x27_1003_);
v___x_1017_ = v___x_985_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_size_x27_1003_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_buckets_x27_1005_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v_buckets_x27_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_inc(v_bkt_1000_);
v___x_1019_ = lean_box(0);
v_buckets_x27_1020_ = lean_array_uset(v_buckets_983_, v___x_999_, v___x_1019_);
v___x_1021_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_980_, v_b_981_, v_bkt_1000_);
v___x_1022_ = lean_array_uset(v_buckets_x27_1020_, v___x_999_, v___x_1021_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_1022_);
v___x_1024_ = v___x_985_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_size_982_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(lean_object* v___x_1047_, lean_object* v_val_1048_, uint8_t v___x_1049_, lean_object* v_ci_1050_, lean_object* v_info_1051_, lean_object* v_x_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
if (lean_obj_tag(v_info_1051_) == 10)
{
lean_object* v_i_1056_; lean_object* v_stx_1057_; lean_object* v_value_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1152_; 
v_i_1056_ = lean_ctor_get(v_info_1051_, 0);
lean_inc_ref(v_i_1056_);
v_stx_1057_ = lean_ctor_get(v_i_1056_, 0);
v_value_1058_ = lean_ctor_get(v_i_1056_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_i_1056_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1060_ = v_i_1056_;
v_isShared_1061_ = v_isSharedCheck_1152_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_value_1058_);
lean_inc(v_stx_1057_);
lean_dec(v_i_1056_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1152_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_1058_, v___x_1047_);
lean_dec(v_value_1058_);
if (lean_obj_tag(v___x_1062_) == 1)
{
lean_object* v_val_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1142_; 
v_val_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1142_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_val_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1142_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Elab_Info_range_x3f(v_info_1051_);
if (lean_obj_tag(v___x_1067_) == 1)
{
lean_object* v_val_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1137_; 
v_val_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1137_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_val_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1137_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_maskAcc_1073_; lean_object* v___y_1084_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6));
lean_inc(v_stx_1057_);
v___x_1125_ = l_Lean_Syntax_isOfKind(v_stx_1057_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8));
lean_inc(v_stx_1057_);
v___x_1127_ = l_Lean_Syntax_isOfKind(v_stx_1057_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1135_; 
lean_del_object(v___x_1070_);
lean_dec(v_val_1068_);
lean_del_object(v___x_1065_);
lean_dec(v_val_1063_);
lean_del_object(v___x_1060_);
lean_dec(v_stx_1057_);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_info_1051_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v_info_1051_, 0);
lean_dec(v_unused_1136_);
v___x_1129_ = v_info_1051_;
v_isShared_1130_ = v_isSharedCheck_1135_;
goto v_resetjp_1128_;
}
else
{
lean_dec(v_info_1051_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1135_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = lean_box(0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1131_);
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
goto v___jp_1088_;
}
}
else
{
goto v___jp_1088_;
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_st_ref_take(v_val_1048_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v_maskAcc_1073_);
v___x_1076_ = v___x_1060_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_stx_1057_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_maskAcc_1073_);
v___x_1076_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_1074_, v_val_1068_, v___x_1076_);
v___x_1078_ = lean_st_ref_put(v_val_1048_, v___x_1077_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1078_);
v___x_1080_ = v___x_1070_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
v___jp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0));
v___x_1087_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_1049_, v_val_1063_, v___y_1084_, v___x_1085_, v___x_1086_);
lean_dec_ref(v___y_1084_);
lean_dec(v_val_1063_);
v_maskAcc_1073_ = v___x_1087_;
goto v___jp_1072_;
}
v___jp_1088_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_st_ref_get(v_val_1048_);
v___x_1090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_1089_, v_val_1068_);
lean_dec(v___x_1089_);
if (lean_obj_tag(v___x_1090_) == 1)
{
lean_object* v_val_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1123_; 
v_val_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1123_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_val_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1123_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v_snd_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1121_; 
v_snd_1095_ = lean_ctor_get(v_val_1091_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_val_1091_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_val_1091_, 0);
lean_dec(v_unused_1122_);
v___x_1097_ = v_val_1091_;
v_isShared_1098_ = v_isSharedCheck_1121_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_snd_1095_);
lean_dec(v_val_1091_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1121_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_array_get_size(v_val_1063_);
v___x_1100_ = lean_array_get_size(v_snd_1095_);
v___x_1101_ = lean_nat_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1102_ = l_Lean_Elab_Info_stx(v_info_1051_);
lean_dec_ref_known(v_info_1051_, 1);
v___x_1103_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2);
v___x_1104_ = l_Nat_reprFast(v___x_1100_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 3);
lean_ctor_set(v___x_1093_, 0, v___x_1104_);
v___x_1106_ = v___x_1093_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = l_Lean_MessageData_ofFormat(v___x_1106_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 7);
lean_ctor_set(v___x_1097_, 1, v___x_1107_);
lean_ctor_set(v___x_1097_, 0, v___x_1103_);
v___x_1109_ = v___x_1097_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Nat_reprFast(v___x_1099_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 3);
lean_ctor_set(v___x_1065_, 0, v___x_1112_);
v___x_1114_ = v___x_1065_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = l_Lean_MessageData_ofFormat(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1111_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v___x_1102_, v___x_1116_, v___y_1053_, v___y_1054_);
lean_dec(v___x_1102_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_dec_ref_known(v___x_1117_, 1);
v___y_1084_ = v_snd_1095_;
goto v___jp_1083_;
}
else
{
lean_dec(v_snd_1095_);
lean_del_object(v___x_1070_);
lean_dec(v_val_1068_);
lean_dec(v_val_1063_);
lean_del_object(v___x_1060_);
lean_dec(v_stx_1057_);
return v___x_1117_;
}
}
}
}
}
else
{
lean_del_object(v___x_1097_);
lean_del_object(v___x_1093_);
lean_del_object(v___x_1065_);
lean_dec_ref_known(v_info_1051_, 1);
v___y_1084_ = v_snd_1095_;
goto v___jp_1083_;
}
}
}
}
else
{
lean_dec(v___x_1090_);
lean_del_object(v___x_1065_);
lean_dec_ref_known(v_info_1051_, 1);
v_maskAcc_1073_ = v_val_1063_;
goto v___jp_1072_;
}
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_dec(v___x_1067_);
lean_dec(v_val_1063_);
lean_del_object(v___x_1060_);
lean_dec(v_stx_1057_);
lean_dec_ref_known(v_info_1051_, 1);
v___x_1138_ = lean_box(0);
if (v_isShared_1066_ == 0)
{
lean_ctor_set_tag(v___x_1065_, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1138_);
v___x_1140_ = v___x_1065_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
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
else
{
lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v___x_1062_);
lean_del_object(v___x_1060_);
lean_dec(v_stx_1057_);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_info_1051_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_info_1051_, 0);
lean_dec(v_unused_1151_);
v___x_1144_ = v_info_1051_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_dec(v_info_1051_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = lean_box(0);
if (v_isShared_1145_ == 0)
{
lean_ctor_set_tag(v___x_1144_, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
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
else
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref(v_info_1051_);
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(lean_object* v___x_1155_, lean_object* v_val_1156_, lean_object* v___x_1157_, lean_object* v_ci_1158_, lean_object* v_info_1159_, lean_object* v_x_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v___x_13391__boxed_1164_; lean_object* v_res_1165_; 
v___x_13391__boxed_1164_ = lean_unbox(v___x_1157_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v___x_1155_, v_val_1156_, v___x_13391__boxed_1164_, v_ci_1158_, v_info_1159_, v_x_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v_x_1160_);
lean_dec_ref(v_ci_1158_);
lean_dec(v_val_1156_);
lean_dec(v___x_1155_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(lean_object* v_postNode_1166_, lean_object* v_ci_1167_, lean_object* v_i_1168_, lean_object* v_cs_1169_, lean_object* v_x_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; 
lean_inc(v___y_1172_);
lean_inc_ref(v___y_1171_);
v___x_1174_ = lean_apply_6(v_postNode_1166_, v_ci_1167_, v_i_1168_, v_cs_1169_, v___y_1171_, v___y_1172_, lean_box(0));
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(lean_object* v_postNode_1175_, lean_object* v_ci_1176_, lean_object* v_i_1177_, lean_object* v_cs_1178_, lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(v_postNode_1175_, v_ci_1176_, v_i_1177_, v_cs_1178_, v_x_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v_x_1179_);
return v_res_1183_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_instMonadEIO(lean_box(0));
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(lean_object* v_msg_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v_toApplicative_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1224_; 
v___x_1191_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0);
v___x_1192_ = l_StateRefT_x27_instMonad___redArg(v___x_1191_);
v_toApplicative_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1192_, 1);
lean_dec(v_unused_1225_);
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_toApplicative_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_toFunctor_1197_; lean_object* v_toSeq_1198_; lean_object* v_toSeqLeft_1199_; lean_object* v_toSeqRight_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1222_; 
v_toFunctor_1197_ = lean_ctor_get(v_toApplicative_1193_, 0);
v_toSeq_1198_ = lean_ctor_get(v_toApplicative_1193_, 2);
v_toSeqLeft_1199_ = lean_ctor_get(v_toApplicative_1193_, 3);
v_toSeqRight_1200_ = lean_ctor_get(v_toApplicative_1193_, 4);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_toApplicative_1193_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_dec(v_unused_1223_);
v___x_1202_ = v_toApplicative_1193_;
v_isShared_1203_ = v_isSharedCheck_1222_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_toSeqRight_1200_);
lean_inc(v_toSeqLeft_1199_);
lean_inc(v_toSeq_1198_);
lean_inc(v_toFunctor_1197_);
lean_dec(v_toApplicative_1193_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1222_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___f_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___f_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; lean_object* v___x_1213_; 
v___f_1204_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1));
v___f_1205_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2));
lean_inc_ref(v_toFunctor_1197_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toFunctor_1197_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toFunctor_1197_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___f_1206_);
lean_ctor_set(v___x_1208_, 1, v___f_1207_);
v___f_1209_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1209_, 0, v_toSeqRight_1200_);
v___f_1210_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1210_, 0, v_toSeqLeft_1199_);
v___f_1211_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1211_, 0, v_toSeq_1198_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 4, v___f_1209_);
lean_ctor_set(v___x_1202_, 3, v___f_1210_);
lean_ctor_set(v___x_1202_, 2, v___f_1211_);
lean_ctor_set(v___x_1202_, 1, v___f_1204_);
lean_ctor_set(v___x_1202_, 0, v___x_1208_);
v___x_1213_ = v___x_1202_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___f_1204_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v___f_1211_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v___f_1210_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v___f_1209_);
v___x_1213_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v___f_1205_);
lean_ctor_set(v___x_1195_, 0, v___x_1213_);
v___x_1215_ = v___x_1195_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___f_1205_);
v___x_1215_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_11883__overap_1218_; lean_object* v___x_1219_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = l_instInhabitedOfMonad___redArg(v___x_1215_, v___x_1216_);
v___x_11883__overap_1218_ = lean_panic_fn_borrowed(v___x_1217_, v_msg_1187_);
lean_dec(v___x_1217_);
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
v___x_1219_ = lean_apply_3(v___x_11883__overap_1218_, v___y_1188_, v___y_1189_, lean_box(0));
return v___x_1219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(lean_object* v_msg_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1230_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2));
v___x_1235_ = lean_unsigned_to_nat(21u);
v___x_1236_ = lean_unsigned_to_nat(65u);
v___x_1237_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1));
v___x_1238_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0));
v___x_1239_ = l_mkPanicMessageWithDecl(v___x_1238_, v___x_1237_, v___x_1236_, v___x_1235_, v___x_1234_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(lean_object* v_preNode_1240_, lean_object* v_postNode_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
switch(lean_obj_tag(v_x_1243_))
{
case 0:
{
lean_object* v_i_1247_; lean_object* v_t_1248_; lean_object* v___x_1249_; 
v_i_1247_ = lean_ctor_get(v_x_1243_, 0);
lean_inc_ref(v_i_1247_);
v_t_1248_ = lean_ctor_get(v_x_1243_, 1);
lean_inc_ref(v_t_1248_);
lean_dec_ref_known(v_x_1243_, 2);
v___x_1249_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1247_, v_x_1242_);
v_x_1242_ = v___x_1249_;
v_x_1243_ = v_t_1248_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1242_) == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref_known(v_x_1243_, 2);
lean_dec_ref(v_postNode_1241_);
lean_dec_ref(v_preNode_1240_);
v___x_1251_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3);
v___x_1252_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v___x_1251_, v___y_1244_, v___y_1245_);
return v___x_1252_;
}
else
{
lean_object* v_i_1253_; lean_object* v_children_1254_; lean_object* v_val_1255_; lean_object* v___x_1256_; 
v_i_1253_ = lean_ctor_get(v_x_1243_, 0);
lean_inc_ref_n(v_i_1253_, 2);
v_children_1254_ = lean_ctor_get(v_x_1243_, 1);
lean_inc_ref_n(v_children_1254_, 2);
lean_dec_ref_known(v_x_1243_, 2);
v_val_1255_ = lean_ctor_get(v_x_1242_, 0);
lean_inc_n(v_val_1255_, 2);
lean_inc_ref(v_preNode_1240_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
v___x_1256_ = lean_apply_6(v_preNode_1240_, v_val_1255_, v_i_1253_, v_children_1254_, v___y_1244_, v___y_1245_, lean_box(0));
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; uint8_t v___x_1258_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = lean_unbox(v_a_1257_);
lean_dec(v_a_1257_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_preNode_1240_);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_x_1242_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v_x_1242_, 0);
lean_dec(v_unused_1284_);
v___x_1260_ = v_x_1242_;
v_isShared_1261_ = v_isSharedCheck_1283_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v_x_1242_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1283_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_box(0);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
v___x_1263_ = lean_apply_7(v_postNode_1241_, v_val_1255_, v_i_1253_, v_children_1254_, v___x_1262_, v___y_1244_, v___y_1245_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1274_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_a_1264_);
v___x_1269_ = v___x_1260_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1269_);
v___x_1271_ = v___x_1266_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_del_object(v___x_1260_);
v_a_1275_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1263_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1263_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1242_, v_i_1253_);
v___x_1286_ = l_Lean_PersistentArray_toList___redArg(v_children_1254_);
v___x_1287_ = lean_box(0);
lean_inc_ref(v_postNode_1241_);
v___x_1288_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1240_, v_postNode_1241_, v___x_1285_, v___x_1286_, v___x_1287_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
v___x_1290_ = lean_apply_7(v_postNode_1241_, v_val_1255_, v_i_1253_, v_children_1254_, v_a_1289_, v___y_1244_, v___y_1245_, lean_box(0));
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v_a_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_a_1300_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1290_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1290_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_val_1255_);
lean_dec_ref(v_children_1254_);
lean_dec_ref(v_i_1253_);
lean_dec_ref(v_postNode_1241_);
v_a_1308_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1288_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1288_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_val_1255_);
lean_dec_ref(v_children_1254_);
lean_dec_ref_known(v_x_1242_, 1);
lean_dec_ref(v_i_1253_);
lean_dec_ref(v_postNode_1241_);
lean_dec_ref(v_preNode_1240_);
v_a_1316_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1256_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1256_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
default: 
{
lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_x_1242_);
lean_dec_ref(v_postNode_1241_);
lean_dec_ref(v_preNode_1240_);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_x_1243_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v_x_1243_, 0);
lean_dec(v_unused_1332_);
v___x_1325_ = v_x_1243_;
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v_x_1243_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = lean_box(0);
if (v_isShared_1326_ == 0)
{
lean_ctor_set_tag(v___x_1325_, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(lean_object* v_preNode_1333_, lean_object* v_postNode_1334_, lean_object* v___x_1335_, lean_object* v_x_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v___x_1335_);
lean_dec_ref(v_postNode_1334_);
lean_dec_ref(v_preNode_1333_);
v___x_1341_ = l_List_reverse___redArg(v_x_1337_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
else
{
lean_object* v_head_1343_; lean_object* v_tail_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1362_; 
v_head_1343_ = lean_ctor_get(v_x_1336_, 0);
v_tail_1344_ = lean_ctor_get(v_x_1336_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_x_1336_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1346_ = v_x_1336_;
v_isShared_1347_ = v_isSharedCheck_1362_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_tail_1344_);
lean_inc(v_head_1343_);
lean_dec(v_x_1336_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1362_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; 
lean_inc(v___x_1335_);
lean_inc_ref(v_postNode_1334_);
lean_inc_ref(v_preNode_1333_);
v___x_1348_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1333_, v_postNode_1334_, v___x_1335_, v_head_1343_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_x_1337_);
lean_ctor_set(v___x_1346_, 0, v_a_1349_);
v___x_1351_ = v___x_1346_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1349_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_x_1337_);
v___x_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
v_x_1336_ = v_tail_1344_;
v_x_1337_ = v___x_1351_;
goto _start;
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_del_object(v___x_1346_);
lean_dec(v_tail_1344_);
lean_dec(v_x_1337_);
lean_dec(v___x_1335_);
lean_dec_ref(v_postNode_1334_);
lean_dec_ref(v_preNode_1333_);
v_a_1354_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1348_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1348_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(lean_object* v_preNode_1363_, lean_object* v_postNode_1364_, lean_object* v___x_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1363_, v_postNode_1364_, v___x_1365_, v_x_1366_, v_x_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(lean_object* v_preNode_1372_, lean_object* v_postNode_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1372_, v_postNode_1373_, v_x_1374_, v_x_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object* v_preNode_1380_, lean_object* v_postNode_1381_, lean_object* v_ctx_x3f_1382_, lean_object* v_t_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___f_1387_; lean_object* v___x_1388_; 
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1387_, 0, v_postNode_1381_);
v___x_1388_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1380_, v___f_1387_, v_ctx_x3f_1382_, v_t_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1396_; 
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v___x_1388_, 0);
lean_dec(v_unused_1397_);
v___x_1390_ = v___x_1388_;
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
else
{
lean_dec(v___x_1388_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = lean_box(0);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1392_);
v___x_1394_ = v___x_1390_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1388_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1388_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object* v_preNode_1406_, lean_object* v_postNode_1407_, lean_object* v_ctx_x3f_1408_, lean_object* v_t_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v_preNode_1406_, v_postNode_1407_, v_ctx_x3f_1408_, v_t_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(uint8_t v___x_1414_, lean_object* v_x_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_box(v___x_1414_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object* v___x_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v___x_14040__boxed_1430_; lean_object* v_res_1431_; 
v___x_14040__boxed_1430_ = lean_unbox(v___x_1423_);
v_res_1431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v___x_14040__boxed_1430_, v_x_1424_, v_x_1425_, v_x_1426_, v___y_1427_, v___y_1428_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec_ref(v_x_1426_);
lean_dec_ref(v_x_1425_);
lean_dec_ref(v_x_1424_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(uint8_t v___x_1432_, lean_object* v_val_1433_, lean_object* v_as_1434_, size_t v_sz_1435_, size_t v_i_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_usize_dec_lt(v_i_1436_, v_sz_1435_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_dec(v_val_1433_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_b_1437_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1443_ = lean_box(v___x_1432_);
v___f_1444_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1444_, 0, v___x_1443_);
v___x_1445_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
v___x_1446_ = lean_box(v___x_1432_);
lean_inc(v_val_1433_);
v___f_1447_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1447_, 0, v___x_1445_);
lean_closure_set(v___f_1447_, 1, v_val_1433_);
lean_closure_set(v___f_1447_, 2, v___x_1446_);
v_a_1448_ = lean_array_uget_borrowed(v_as_1434_, v_i_1436_);
v___x_1449_ = lean_box(0);
lean_inc(v_a_1448_);
v___x_1450_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v___f_1444_, v___f_1447_, v___x_1449_, v_a_1448_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; 
lean_dec_ref_known(v___x_1450_, 1);
v___x_1451_ = lean_box(0);
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_add(v_i_1436_, v___x_1452_);
v_i_1436_ = v___x_1453_;
v_b_1437_ = v___x_1451_;
goto _start;
}
else
{
lean_dec(v_val_1433_);
return v___x_1450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object* v___x_1455_, lean_object* v_val_1456_, lean_object* v_as_1457_, lean_object* v_sz_1458_, lean_object* v_i_1459_, lean_object* v_b_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
uint8_t v___x_14065__boxed_1464_; size_t v_sz_boxed_1465_; size_t v_i_boxed_1466_; lean_object* v_res_1467_; 
v___x_14065__boxed_1464_ = lean_unbox(v___x_1455_);
v_sz_boxed_1465_ = lean_unbox_usize(v_sz_1458_);
lean_dec(v_sz_1458_);
v_i_boxed_1466_ = lean_unbox_usize(v_i_1459_);
lean_dec(v_i_1459_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_14065__boxed_1464_, v_val_1456_, v_as_1457_, v_sz_boxed_1465_, v_i_boxed_1466_, v_b_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec_ref(v_as_1457_);
return v_res_1467_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_unsigned_to_nat(16u);
v___x_1470_ = lean_mk_array(v___x_1469_, v___x_1468_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__0, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0(lean_object* v_cmdStx_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1545_; 
v___x_1478_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_1475_, v___y_1476_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1545_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1545_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_1484_ = l_Lean_Linter_getLinterValue(v___x_1483_, v_a_1479_);
lean_dec(v_a_1479_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = lean_box(0);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1485_);
v___x_1487_ = v___x_1481_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
else
{
uint8_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = 0;
v___x_1490_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1474_, v___x_1489_);
if (lean_obj_tag(v___x_1490_) == 1)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_infoState_1495_; lean_object* v_trees_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; size_t v_sz_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
lean_dec_ref_known(v___x_1490_, 1);
lean_del_object(v___x_1481_);
v___x_1491_ = lean_st_ref_get(v___y_1476_);
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__1, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1);
v___x_1494_ = lean_st_mk_ref(v___x_1493_);
v_infoState_1495_ = lean_ctor_get(v___x_1491_, 8);
lean_inc_ref(v_infoState_1495_);
lean_dec(v___x_1491_);
v_trees_1496_ = lean_ctor_get(v_infoState_1495_, 2);
lean_inc_ref(v_trees_1496_);
lean_dec_ref(v_infoState_1495_);
v___x_1497_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1496_);
lean_dec_ref(v_trees_1496_);
v___x_1498_ = lean_box(0);
v_sz_1499_ = lean_array_size(v___x_1497_);
v___x_1500_ = ((size_t)0ULL);
lean_inc(v___x_1494_);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_1484_, v___x_1494_, v___x_1497_, v_sz_1499_, v___x_1500_, v___x_1498_, v___y_1475_, v___y_1476_);
lean_dec_ref(v___x_1497_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1502_; lean_object* v___y_1504_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1528_; lean_object* v_size_1534_; lean_object* v_buckets_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
lean_dec_ref_known(v___x_1501_, 1);
v___x_1502_ = lean_st_ref_get(v___x_1494_);
lean_dec(v___x_1494_);
v_size_1534_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_size_1534_);
v_buckets_1535_ = lean_ctor_get(v___x_1502_, 1);
lean_inc_ref(v_buckets_1535_);
lean_dec(v___x_1502_);
v___x_1536_ = lean_mk_empty_array_with_capacity(v_size_1534_);
lean_dec(v_size_1534_);
v___x_1537_ = lean_array_get_size(v_buckets_1535_);
v___x_1538_ = lean_nat_dec_lt(v___x_1492_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_dec_ref(v_buckets_1535_);
v___y_1528_ = v___x_1536_;
goto v___jp_1527_;
}
else
{
size_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_usize_of_nat(v___x_1537_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_1535_, v___x_1500_, v___x_1539_, v___x_1536_);
lean_dec_ref(v_buckets_1535_);
v___y_1528_ = v___x_1540_;
goto v___jp_1527_;
}
v___jp_1503_:
{
size_t v_sz_1505_; lean_object* v___x_1506_; 
v_sz_1505_ = lean_array_size(v___y_1504_);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___y_1504_, v_sz_1505_, v___x_1500_, v___x_1498_, v___y_1475_, v___y_1476_);
lean_dec_ref(v___y_1504_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v___x_1506_, 0);
lean_dec(v_unused_1514_);
v___x_1508_ = v___x_1506_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_dec(v___x_1506_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1498_);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1498_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
return v___x_1506_;
}
}
v___jp_1515_:
{
lean_object* v___x_1520_; 
v___x_1520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v___y_1516_, v___y_1518_, v___y_1517_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec(v___y_1516_);
v___y_1504_ = v___x_1520_;
goto v___jp_1503_;
}
v___jp_1521_:
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_nat_dec_le(v___y_1525_, v___y_1524_);
if (v___x_1526_ == 0)
{
lean_dec(v___y_1524_);
lean_inc(v___y_1525_);
v___y_1516_ = v___y_1522_;
v___y_1517_ = v___y_1525_;
v___y_1518_ = v___y_1523_;
v___y_1519_ = v___y_1525_;
goto v___jp_1515_;
}
else
{
v___y_1516_ = v___y_1522_;
v___y_1517_ = v___y_1525_;
v___y_1518_ = v___y_1523_;
v___y_1519_ = v___y_1524_;
goto v___jp_1515_;
}
}
v___jp_1527_:
{
lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1529_ = lean_array_get_size(v___y_1528_);
v___x_1530_ = lean_nat_dec_eq(v___x_1529_, v___x_1492_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1531_ = lean_unsigned_to_nat(1u);
v___x_1532_ = lean_nat_sub(v___x_1529_, v___x_1531_);
v___x_1533_ = lean_nat_dec_le(v___x_1492_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_inc(v___x_1532_);
v___y_1522_ = v___x_1529_;
v___y_1523_ = v___y_1528_;
v___y_1524_ = v___x_1532_;
v___y_1525_ = v___x_1532_;
goto v___jp_1521_;
}
else
{
v___y_1522_ = v___x_1529_;
v___y_1523_ = v___y_1528_;
v___y_1524_ = v___x_1532_;
v___y_1525_ = v___x_1492_;
goto v___jp_1521_;
}
}
else
{
v___y_1504_ = v___y_1528_;
goto v___jp_1503_;
}
}
}
else
{
lean_dec(v___x_1494_);
return v___x_1501_;
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_dec(v___x_1490_);
v___x_1541_ = lean_box(0);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1541_);
v___x_1543_ = v___x_1481_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___boxed(lean_object* v_cmdStx_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_1546_, v___y_1547_, v___y_1548_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v_cmdStx_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(lean_object* v_o_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_1562_, v___y_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(lean_object* v_o_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object* v_00_u03b2_1572_, lean_object* v_m_1573_, lean_object* v_a_1574_, lean_object* v_b_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_1573_, v_a_1574_, v_b_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object* v_00_u03b2_1577_, lean_object* v_m_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_1578_, v_a_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object* v_00_u03b2_1581_, lean_object* v_m_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(v_00_u03b2_1581_, v_m_1582_, v_a_1583_);
lean_dec_ref(v_a_1583_);
lean_dec_ref(v_m_1582_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(lean_object* v_00_u03b1_1585_, lean_object* v_ref_1586_, lean_object* v_msg_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_1586_, v_msg_1587_, v___y_1588_, v___y_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_ref_1593_, lean_object* v_msg_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(v_00_u03b1_1592_, v_ref_1593_, v_msg_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v_ref_1593_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object* v_upperBound_1599_, lean_object* v_snd_1600_, lean_object* v_fst_1601_, lean_object* v_inst_1602_, lean_object* v_R_1603_, lean_object* v_a_1604_, lean_object* v_b_1605_, lean_object* v_c_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_1599_, v_snd_1600_, v_fst_1601_, v_a_1604_, v_b_1605_, v___y_1607_, v___y_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object* v_upperBound_1611_, lean_object* v_snd_1612_, lean_object* v_fst_1613_, lean_object* v_inst_1614_, lean_object* v_R_1615_, lean_object* v_a_1616_, lean_object* v_b_1617_, lean_object* v_c_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(v_upperBound_1611_, v_snd_1612_, v_fst_1613_, v_inst_1614_, v_R_1615_, v_a_1616_, v_b_1617_, v_c_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_snd_1612_);
lean_dec(v_upperBound_1611_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object* v_n_1623_, lean_object* v_as_1624_, lean_object* v_lo_1625_, lean_object* v_hi_1626_, lean_object* v_w_1627_, lean_object* v_hlo_1628_, lean_object* v_hhi_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_1623_, v_as_1624_, v_lo_1625_, v_hi_1626_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object* v_n_1631_, lean_object* v_as_1632_, lean_object* v_lo_1633_, lean_object* v_hi_1634_, lean_object* v_w_1635_, lean_object* v_hlo_1636_, lean_object* v_hhi_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(v_n_1631_, v_as_1632_, v_lo_1633_, v_hi_1634_, v_w_1635_, v_hlo_1636_, v_hhi_1637_);
lean_dec(v_hi_1634_);
lean_dec(v_n_1631_);
return v_res_1638_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object* v_00_u03b2_1639_, lean_object* v_a_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1640_, v_x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1643_, lean_object* v_a_1644_, lean_object* v_x_1645_){
_start:
{
uint8_t v_res_1646_; lean_object* v_r_1647_; 
v_res_1646_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_1643_, v_a_1644_, v_x_1645_);
lean_dec(v_x_1645_);
lean_dec_ref(v_a_1644_);
v_r_1647_ = lean_box(v_res_1646_);
return v_r_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(lean_object* v_00_u03b2_1648_, lean_object* v_data_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_data_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(lean_object* v_00_u03b2_1651_, lean_object* v_a_1652_, lean_object* v_b_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1652_, v_b_1653_, v_x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(lean_object* v_00_u03b2_1656_, lean_object* v_a_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_1657_, v_x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1660_, lean_object* v_a_1661_, lean_object* v_x_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(v_00_u03b2_1660_, v_a_1661_, v_x_1662_);
lean_dec(v_x_1662_);
lean_dec_ref(v_a_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(lean_object* v_msgData_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_1664_, v___y_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(lean_object* v_msgData_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(lean_object* v_00_u03b1_1674_, lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_1675_, v___y_1676_, v___y_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_msg_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(v_00_u03b1_1680_, v_msg_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_object* v_00_u03b1_1686_, lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1687_, v___y_1688_, v___y_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_msg_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(v_00_u03b1_1692_, v_msg_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_object* v_00_u03b1_1698_, lean_object* v_preNode_1699_, lean_object* v_postNode_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1699_, v_postNode_1700_, v_x_1701_, v_x_1702_, v___y_1703_, v___y_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(lean_object* v_00_u03b1_1707_, lean_object* v_preNode_1708_, lean_object* v_postNode_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(v_00_u03b1_1707_, v_preNode_1708_, v_postNode_1709_, v_x_1710_, v_x_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(lean_object* v_n_1716_, lean_object* v_lo_1717_, lean_object* v_hi_1718_, lean_object* v_hhi_1719_, lean_object* v_pivot_1720_, lean_object* v_as_1721_, lean_object* v_i_1722_, lean_object* v_k_1723_, lean_object* v_ilo_1724_, lean_object* v_ik_1725_, lean_object* v_w_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_1718_, v_pivot_1720_, v_as_1721_, v_i_1722_, v_k_1723_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(lean_object* v_n_1728_, lean_object* v_lo_1729_, lean_object* v_hi_1730_, lean_object* v_hhi_1731_, lean_object* v_pivot_1732_, lean_object* v_as_1733_, lean_object* v_i_1734_, lean_object* v_k_1735_, lean_object* v_ilo_1736_, lean_object* v_ik_1737_, lean_object* v_w_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(v_n_1728_, v_lo_1729_, v_hi_1730_, v_hhi_1731_, v_pivot_1732_, v_as_1733_, v_i_1734_, v_k_1735_, v_ilo_1736_, v_ik_1737_, v_w_1738_);
lean_dec_ref(v_pivot_1732_);
lean_dec(v_hi_1730_);
lean_dec(v_lo_1729_);
lean_dec(v_n_1728_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1740_, lean_object* v_i_1741_, lean_object* v_source_1742_, lean_object* v_target_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v_i_1741_, v_source_1742_, v_target_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(lean_object* v_msgData_1745_, lean_object* v_macroStack_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_1745_, v_macroStack_1746_, v___y_1748_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_1751_, lean_object* v_macroStack_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_1751_, v_macroStack_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_object* v_00_u03b1_1757_, lean_object* v_preNode_1758_, lean_object* v_postNode_1759_, lean_object* v___x_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1758_, v_postNode_1759_, v___x_1760_, v_x_1761_, v_x_1762_, v___y_1763_, v___y_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_preNode_1768_, lean_object* v_postNode_1769_, lean_object* v___x_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(v_00_u03b1_1767_, v_preNode_1768_, v_postNode_1769_, v___x_1770_, v_x_1771_, v_x_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_x_1778_, v_x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l_Lean_Linter_unusedSimpArgs));
v___x_1783_ = l_Lean_Elab_Command_addLinter(v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
return v_res_1785_;
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
