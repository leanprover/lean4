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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
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
lean_object* v___x_47_; lean_object* v_toCold_48_; lean_object* v_env_49_; lean_object* v_options_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_47_ = lean_st_ref_get(v___y_45_);
v_toCold_48_ = lean_ctor_get(v___y_44_, 0);
v_env_49_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_env_49_);
lean_dec(v___x_47_);
v_options_50_ = lean_ctor_get(v_toCold_48_, 2);
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
lean_ctor_set(v___x_54_, 1, v_msgData_43_);
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
v_ref_65_ = lean_ctor_get(v___y_62_, 2);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_89_, uint8_t v___y_90_, lean_object* v_x_91_){
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
return v___x_99_;
}
else
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_101_ = lean_string_dec_eq(v_str_94_, v___x_100_);
if (v___x_101_ == 0)
{
return v___x_101_;
}
else
{
return v_suppressElabErrors_89_;
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
return v___x_103_;
}
else
{
return v_suppressElabErrors_89_;
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
return v___x_109_;
}
else
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_111_ = lean_string_dec_eq(v_str_106_, v___x_110_);
if (v___x_111_ == 0)
{
return v___x_111_;
}
else
{
lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_113_ = lean_string_dec_eq(v_str_105_, v___x_112_);
if (v___x_113_ == 0)
{
return v___x_113_;
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
return v___y_90_;
}
}
default: 
{
return v___y_90_;
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
return v___x_116_;
}
else
{
return v_suppressElabErrors_89_;
}
}
default: 
{
return v___y_90_;
}
}
}
else
{
return v___y_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_117_, lean_object* v___y_118_, lean_object* v_x_119_){
_start:
{
uint8_t v_suppressElabErrors_boxed_120_; uint8_t v___y_4807__boxed_121_; uint8_t v_res_122_; lean_object* v_r_123_; 
v_suppressElabErrors_boxed_120_ = lean_unbox(v_suppressElabErrors_117_);
v___y_4807__boxed_121_ = lean_unbox(v___y_118_);
v_res_122_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_120_, v___y_4807__boxed_121_, v_x_119_);
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
lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; uint8_t v___y_151_; uint8_t v___y_152_; lean_object* v___y_153_; lean_object* v_currNamespace_154_; lean_object* v_openDecls_155_; lean_object* v___y_156_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; uint8_t v___y_187_; uint8_t v___y_188_; uint8_t v___y_189_; lean_object* v___y_190_; lean_object* v___y_191_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; uint8_t v___y_215_; uint8_t v___y_216_; uint8_t v___y_217_; lean_object* v___y_218_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; uint8_t v___y_228_; uint8_t v___y_229_; uint8_t v___y_230_; uint8_t v___x_235_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; uint8_t v___y_243_; uint8_t v___y_244_; uint8_t v___y_245_; uint8_t v___y_247_; uint8_t v___x_265_; 
v___x_235_ = 2;
v___x_265_ = l_Lean_instBEqMessageSeverity_beq(v_severity_141_, v___x_235_);
if (v___x_265_ == 0)
{
v___y_247_ = v___x_265_;
goto v___jp_246_;
}
else
{
uint8_t v___x_266_; 
lean_inc_ref(v_msgData_140_);
v___x_266_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_140_);
v___y_247_ = v___x_266_;
goto v___jp_246_;
}
v___jp_146_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v_env_161_; lean_object* v_nextMacroScope_162_; lean_object* v_ngen_163_; lean_object* v_auxDeclNGen_164_; lean_object* v_traceState_165_; lean_object* v_cache_166_; lean_object* v_messages_167_; lean_object* v_infoState_168_; lean_object* v_snapshotTasks_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_180_; 
lean_inc(v_openDecls_155_);
lean_inc(v_currNamespace_154_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_currNamespace_154_);
lean_ctor_set(v___x_157_, 1, v_openDecls_155_);
v___x_158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___y_153_);
lean_inc_ref(v___y_148_);
lean_inc_ref(v___y_150_);
v___x_159_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_159_, 0, v___y_150_);
lean_ctor_set(v___x_159_, 1, v___y_149_);
lean_ctor_set(v___x_159_, 2, v___y_147_);
lean_ctor_set(v___x_159_, 3, v___y_148_);
lean_ctor_set(v___x_159_, 4, v___x_158_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*5, v___y_152_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*5 + 1, v___y_151_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*5 + 2, v_isSilent_142_);
v___x_160_ = lean_st_ref_take(v___y_156_);
v_env_161_ = lean_ctor_get(v___x_160_, 0);
v_nextMacroScope_162_ = lean_ctor_get(v___x_160_, 1);
v_ngen_163_ = lean_ctor_get(v___x_160_, 2);
v_auxDeclNGen_164_ = lean_ctor_get(v___x_160_, 3);
v_traceState_165_ = lean_ctor_get(v___x_160_, 4);
v_cache_166_ = lean_ctor_get(v___x_160_, 5);
v_messages_167_ = lean_ctor_get(v___x_160_, 6);
v_infoState_168_ = lean_ctor_get(v___x_160_, 7);
v_snapshotTasks_169_ = lean_ctor_get(v___x_160_, 8);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_180_ == 0)
{
v___x_171_ = v___x_160_;
v_isShared_172_ = v_isSharedCheck_180_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_snapshotTasks_169_);
lean_inc(v_infoState_168_);
lean_inc(v_messages_167_);
lean_inc(v_cache_166_);
lean_inc(v_traceState_165_);
lean_inc(v_auxDeclNGen_164_);
lean_inc(v_ngen_163_);
lean_inc(v_nextMacroScope_162_);
lean_inc(v_env_161_);
lean_dec(v___x_160_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_180_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = lean_box(0);
v___x_174_ = l_Lean_MessageLog_add(v___x_159_, v_messages_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 6, v___x_174_);
v___x_176_ = v___x_171_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_env_161_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_nextMacroScope_162_);
lean_ctor_set(v_reuseFailAlloc_179_, 2, v_ngen_163_);
lean_ctor_set(v_reuseFailAlloc_179_, 3, v_auxDeclNGen_164_);
lean_ctor_set(v_reuseFailAlloc_179_, 4, v_traceState_165_);
lean_ctor_set(v_reuseFailAlloc_179_, 5, v_cache_166_);
lean_ctor_set(v_reuseFailAlloc_179_, 6, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_179_, 7, v_infoState_168_);
lean_ctor_set(v_reuseFailAlloc_179_, 8, v_snapshotTasks_169_);
v___x_176_ = v_reuseFailAlloc_179_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_st_ref_put(v___y_156_, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_173_);
return v___x_178_;
}
}
}
v___jp_181_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_207_; 
v___x_192_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_140_);
v___x_193_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3(v___x_192_, v___y_143_, v___y_144_);
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_207_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_207_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_207_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
lean_inc_ref_n(v___y_186_, 2);
v___x_198_ = l_Lean_FileMap_toPosition(v___y_186_, v___y_190_);
lean_dec(v___y_190_);
v___x_199_ = l_Lean_FileMap_toPosition(v___y_186_, v___y_191_);
lean_dec(v___y_191_);
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
v___x_201_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___closed__0));
if (v___y_189_ == 0)
{
lean_del_object(v___x_196_);
lean_dec_ref(v___y_182_);
v___y_147_ = v___x_200_;
v___y_148_ = v___x_201_;
v___y_149_ = v___x_198_;
v___y_150_ = v___y_185_;
v___y_151_ = v___y_187_;
v___y_152_ = v___y_188_;
v___y_153_ = v_a_194_;
v_currNamespace_154_ = v___y_183_;
v_openDecls_155_ = v___y_184_;
v___y_156_ = v___y_144_;
goto v___jp_146_;
}
else
{
uint8_t v___x_202_; 
lean_inc(v_a_194_);
v___x_202_ = l_Lean_MessageData_hasTag(v___y_182_, v_a_194_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec_ref_known(v___x_200_, 1);
lean_dec_ref(v___x_198_);
lean_dec(v_a_194_);
v___x_203_ = lean_box(0);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_203_);
v___x_205_ = v___x_196_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
else
{
lean_del_object(v___x_196_);
v___y_147_ = v___x_200_;
v___y_148_ = v___x_201_;
v___y_149_ = v___x_198_;
v___y_150_ = v___y_185_;
v___y_151_ = v___y_187_;
v___y_152_ = v___y_188_;
v___y_153_ = v_a_194_;
v_currNamespace_154_ = v___y_183_;
v_openDecls_155_ = v___y_184_;
v___y_156_ = v___y_144_;
goto v___jp_146_;
}
}
}
}
v___jp_208_:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Syntax_getTailPos_x3f(v___y_212_, v___y_216_);
lean_dec(v___y_212_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_inc(v___y_218_);
v___y_182_ = v___y_209_;
v___y_183_ = v___y_210_;
v___y_184_ = v___y_211_;
v___y_185_ = v___y_214_;
v___y_186_ = v___y_213_;
v___y_187_ = v___y_215_;
v___y_188_ = v___y_216_;
v___y_189_ = v___y_217_;
v___y_190_ = v___y_218_;
v___y_191_ = v___y_218_;
goto v___jp_181_;
}
else
{
lean_object* v_val_220_; 
v_val_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_val_220_);
lean_dec_ref_known(v___x_219_, 1);
v___y_182_ = v___y_209_;
v___y_183_ = v___y_210_;
v___y_184_ = v___y_211_;
v___y_185_ = v___y_214_;
v___y_186_ = v___y_213_;
v___y_187_ = v___y_215_;
v___y_188_ = v___y_216_;
v___y_189_ = v___y_217_;
v___y_190_ = v___y_218_;
v___y_191_ = v_val_220_;
goto v___jp_181_;
}
}
v___jp_221_:
{
lean_object* v_ref_231_; lean_object* v___x_232_; 
v_ref_231_ = l_Lean_replaceRef(v_ref_139_, v___y_227_);
v___x_232_ = l_Lean_Syntax_getPos_x3f(v_ref_231_, v___y_228_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___y_209_ = v___y_222_;
v___y_210_ = v___y_223_;
v___y_211_ = v___y_224_;
v___y_212_ = v_ref_231_;
v___y_213_ = v___y_226_;
v___y_214_ = v___y_225_;
v___y_215_ = v___y_230_;
v___y_216_ = v___y_228_;
v___y_217_ = v___y_229_;
v___y_218_ = v___x_233_;
goto v___jp_208_;
}
else
{
lean_object* v_val_234_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_232_, 1);
v___y_209_ = v___y_222_;
v___y_210_ = v___y_223_;
v___y_211_ = v___y_224_;
v___y_212_ = v_ref_231_;
v___y_213_ = v___y_226_;
v___y_214_ = v___y_225_;
v___y_215_ = v___y_230_;
v___y_216_ = v___y_228_;
v___y_217_ = v___y_229_;
v___y_218_ = v_val_234_;
goto v___jp_208_;
}
}
v___jp_236_:
{
if (v___y_245_ == 0)
{
v___y_222_ = v___y_237_;
v___y_223_ = v___y_240_;
v___y_224_ = v___y_241_;
v___y_225_ = v___y_239_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_242_;
v___y_228_ = v___y_243_;
v___y_229_ = v___y_244_;
v___y_230_ = v_severity_141_;
goto v___jp_221_;
}
else
{
v___y_222_ = v___y_237_;
v___y_223_ = v___y_240_;
v___y_224_ = v___y_241_;
v___y_225_ = v___y_239_;
v___y_226_ = v___y_238_;
v___y_227_ = v___y_242_;
v___y_228_ = v___y_243_;
v___y_229_ = v___y_244_;
v___y_230_ = v___x_235_;
goto v___jp_221_;
}
}
v___jp_246_:
{
if (v___y_247_ == 0)
{
lean_object* v_toCold_248_; lean_object* v_ref_249_; uint8_t v_suppressElabErrors_250_; lean_object* v_fileName_251_; lean_object* v_fileMap_252_; lean_object* v_options_253_; lean_object* v_currNamespace_254_; lean_object* v_openDecls_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___f_258_; uint8_t v___x_259_; uint8_t v___x_260_; 
v_toCold_248_ = lean_ctor_get(v___y_143_, 0);
v_ref_249_ = lean_ctor_get(v___y_143_, 2);
v_suppressElabErrors_250_ = lean_ctor_get_uint8(v___y_143_, sizeof(void*)*3 + 1);
v_fileName_251_ = lean_ctor_get(v_toCold_248_, 0);
v_fileMap_252_ = lean_ctor_get(v_toCold_248_, 1);
v_options_253_ = lean_ctor_get(v_toCold_248_, 2);
v_currNamespace_254_ = lean_ctor_get(v_toCold_248_, 4);
v_openDecls_255_ = lean_ctor_get(v_toCold_248_, 5);
v___x_256_ = lean_box(v_suppressElabErrors_250_);
v___x_257_ = lean_box(v___y_247_);
v___f_258_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_258_, 0, v___x_256_);
lean_closure_set(v___f_258_, 1, v___x_257_);
v___x_259_ = 1;
v___x_260_ = l_Lean_instBEqMessageSeverity_beq(v_severity_141_, v___x_259_);
if (v___x_260_ == 0)
{
v___y_237_ = v___f_258_;
v___y_238_ = v_fileMap_252_;
v___y_239_ = v_fileName_251_;
v___y_240_ = v_currNamespace_254_;
v___y_241_ = v_openDecls_255_;
v___y_242_ = v_ref_249_;
v___y_243_ = v___y_247_;
v___y_244_ = v_suppressElabErrors_250_;
v___y_245_ = v___x_260_;
goto v___jp_236_;
}
else
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = l_Lean_warningAsError;
v___x_262_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_options_253_, v___x_261_);
v___y_237_ = v___f_258_;
v___y_238_ = v_fileMap_252_;
v___y_239_ = v_fileName_251_;
v___y_240_ = v_currNamespace_254_;
v___y_241_ = v_openDecls_255_;
v___y_242_ = v_ref_249_;
v___y_243_ = v___y_247_;
v___y_244_ = v_suppressElabErrors_250_;
v___y_245_ = v___x_262_;
goto v___jp_236_;
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref(v_msgData_140_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_267_, lean_object* v_msgData_268_, lean_object* v_severity_269_, lean_object* v_isSilent_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
uint8_t v_severity_boxed_274_; uint8_t v_isSilent_boxed_275_; lean_object* v_res_276_; 
v_severity_boxed_274_ = lean_unbox(v_severity_269_);
v_isSilent_boxed_275_ = lean_unbox(v_isSilent_270_);
v_res_276_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_267_, v_msgData_268_, v_severity_boxed_274_, v_isSilent_boxed_275_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v_ref_267_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(lean_object* v_ref_277_, lean_object* v_msgData_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
uint8_t v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; 
v___x_282_ = 1;
v___x_283_ = 0;
v___x_284_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1(v_ref_277_, v_msgData_278_, v___x_282_, v___x_283_, v___y_279_, v___y_280_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0___boxed(lean_object* v_ref_285_, lean_object* v_msgData_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_ref_285_, v_msgData_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v_ref_285_);
return v_res_290_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__0));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__2));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(lean_object* v_linterOption_297_, lean_object* v_stx_298_, lean_object* v_msg_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_name_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_321_; 
v_name_303_ = lean_ctor_get(v_linterOption_297_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_linterOption_297_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v_linterOption_297_, 1);
lean_dec(v_unused_322_);
v___x_305_ = v_linterOption_297_;
v_isShared_306_ = v_isSharedCheck_321_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_name_303_);
lean_dec(v_linterOption_297_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_321_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__1);
lean_inc(v_name_303_);
v___x_308_ = l_Lean_MessageData_ofName(v_name_303_);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 7);
lean_ctor_set(v___x_305_, 1, v___x_308_);
lean_ctor_set(v___x_305_, 0, v___x_307_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_308_);
v___x_310_ = v_reuseFailAlloc_320_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_disable_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_311_ = lean_obj_once(&l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3, &l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___closed__3);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v_disable_313_ = l_Lean_MessageData_note(v___x_312_);
v___x_314_ = l_Lean_Linter_linterMessageTag;
v___x_315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_315_, 0, v_msg_299_);
lean_ctor_set(v___x_315_, 1, v_disable_313_);
v___x_316_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_317_, 0, v_name_303_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
lean_inc(v_stx_298_);
v___x_318_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_318_, 0, v_stx_298_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0(v_stx_298_, v___x_318_, v___y_300_, v___y_301_);
lean_dec(v_stx_298_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0___boxed(lean_object* v_linterOption_323_, lean_object* v_stx_324_, lean_object* v_msg_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v_linterOption_323_, v_stx_324_, v_msg_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_329_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__2));
v___x_335_ = l_Lean_stringToMessageData(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__6));
v___x_342_ = l_Lean_MessageData_ofFormat(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__12));
v___x_353_ = l_Lean_stringToMessageData(v___x_352_);
return v___x_353_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__13);
v___x_355_ = l_Lean_MessageData_note(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__15));
v___x_358_ = l_Lean_stringToMessageData(v___x_357_);
return v___x_358_;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__17));
v___x_361_ = l_Lean_stringToMessageData(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(lean_object* v_stx_362_, lean_object* v_i_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v_hint_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v_simpArgs_378_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_376_ = lean_box(0);
v___x_377_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__1));
v_simpArgs_378_ = l_Lean_Elab_Tactic_getSimpParams(v_stx_362_);
v___x_429_ = lean_array_get_size(v_simpArgs_378_);
v___x_430_ = lean_nat_dec_lt(v_i_363_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec_ref(v_simpArgs_378_);
v___x_431_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__16);
v___x_432_ = l_Nat_reprFast(v_i_363_);
v___x_433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
v___x_434_ = l_Lean_MessageData_ofFormat(v___x_433_);
v___x_435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_431_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__18);
v___x_437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_435_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = l_Lean_MessageData_ofSyntax(v_stx_362_);
v___x_439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v___x_439_, v_a_364_, v_a_365_);
return v___x_440_;
}
else
{
v___y_380_ = v_a_364_;
v___y_381_ = v_a_365_;
goto v___jp_379_;
}
v___jp_367_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v___y_369_);
lean_ctor_set(v___x_374_, 1, v_hint_370_);
v___x_375_ = l_Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0(v___x_373_, v___y_368_, v___x_374_, v___y_371_, v___y_372_);
return v___x_375_;
}
v___jp_379_:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_argStx_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_msg_388_; lean_object* v_otherArgs_389_; lean_object* v___x_390_; 
v___x_382_ = lean_array_get_size(v_simpArgs_378_);
v___x_383_ = lean_unsigned_to_nat(0u);
v_argStx_384_ = lean_array_get(v___x_376_, v_simpArgs_378_, v_i_363_);
v___x_385_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__3);
lean_inc(v_argStx_384_);
v___x_386_ = l_Lean_MessageData_ofSyntax(v_argStx_384_);
v___x_387_ = l_Lean_indentD(v___x_386_);
v_msg_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msg_388_, 0, v___x_385_);
lean_ctor_set(v_msg_388_, 1, v___x_387_);
v_otherArgs_389_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__4));
v___x_390_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v___x_382_, v_i_363_, v_simpArgs_378_, v___x_383_, v_otherArgs_389_);
lean_dec_ref(v_simpArgs_378_);
lean_dec(v_i_363_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
lean_inc(v_stx_362_);
v___x_392_ = l_Lean_Elab_Tactic_setSimpParams(v_stx_362_, v_a_391_);
lean_dec(v_a_391_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_377_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_box(0);
v___x_395_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
lean_ctor_set(v___x_395_, 2, v___x_394_);
lean_ctor_set(v___x_395_, 3, v___x_394_);
lean_ctor_set(v___x_395_, 4, v___x_394_);
lean_ctor_set(v___x_395_, 5, v___x_394_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v_stx_362_);
v___x_397_ = 4;
v___x_398_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_398_, 0, v___x_395_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_394_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*3, v___x_397_);
v___x_399_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__7);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_400_);
v___x_402_ = lean_array_push(v___x_401_, v___x_398_);
v___x_403_ = 0;
v___x_404_ = l_Lean_MessageData_hint(v___x_399_, v___x_402_, v___x_394_, v___x_394_, v___x_403_, v___y_380_, v___y_381_);
lean_dec_ref(v___x_402_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
lean_inc(v_argStx_384_);
v___x_406_ = l_Lean_Syntax_getKind(v_argStx_384_);
v___x_407_ = ((lean_object*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__11));
v___x_408_ = lean_name_eq(v___x_406_, v___x_407_);
lean_dec(v___x_406_);
if (v___x_408_ == 0)
{
v___y_368_ = v_argStx_384_;
v___y_369_ = v_msg_388_;
v_hint_370_ = v_a_405_;
v___y_371_ = v___y_380_;
v___y_372_ = v___y_381_;
goto v___jp_367_;
}
else
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = l_Lean_Syntax_getArg(v_argStx_384_, v___x_400_);
v___x_410_ = l_Lean_Syntax_isNone(v___x_409_);
lean_dec(v___x_409_);
if (v___x_410_ == 0)
{
if (v___x_408_ == 0)
{
v___y_368_ = v_argStx_384_;
v___y_369_ = v_msg_388_;
v_hint_370_ = v_a_405_;
v___y_371_ = v___y_380_;
v___y_372_ = v___y_381_;
goto v___jp_367_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_obj_once(&l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14, &l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14_once, _init_l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___closed__14);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v_a_405_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___y_368_ = v_argStx_384_;
v___y_369_ = v_msg_388_;
v_hint_370_ = v___x_412_;
v___y_371_ = v___y_380_;
v___y_372_ = v___y_381_;
goto v___jp_367_;
}
}
else
{
v___y_368_ = v_argStx_384_;
v___y_369_ = v_msg_388_;
v_hint_370_ = v_a_405_;
v___y_371_ = v___y_380_;
v___y_372_ = v___y_381_;
goto v___jp_367_;
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref_known(v_msg_388_, 2);
lean_dec(v_argStx_384_);
v_a_413_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_404_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_404_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref_known(v_msg_388_, 2);
lean_dec(v_argStx_384_);
lean_dec(v_stx_362_);
v_a_421_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_390_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_390_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed(lean_object* v_stx_441_, lean_object* v_i_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused(v_stx_441_, v_i_442_, v_a_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(lean_object* v_upperBound_447_, lean_object* v_i_448_, lean_object* v_simpArgs_449_, lean_object* v_inst_450_, lean_object* v_R_451_, lean_object* v_a_452_, lean_object* v_b_453_, lean_object* v_c_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___redArg(v_upperBound_447_, v_i_448_, v_simpArgs_449_, v_a_452_, v_b_453_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1___boxed(lean_object* v_upperBound_459_, lean_object* v_i_460_, lean_object* v_simpArgs_461_, lean_object* v_inst_462_, lean_object* v_R_463_, lean_object* v_a_464_, lean_object* v_b_465_, lean_object* v_c_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__1(v_upperBound_459_, v_i_460_, v_simpArgs_461_, v_inst_462_, v_R_463_, v_a_464_, v_b_465_, v_c_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec_ref(v_simpArgs_461_);
lean_dec(v_i_460_);
lean_dec(v_upperBound_459_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(lean_object* v_00_u03b1_471_, lean_object* v_msg_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___redArg(v_msg_472_, v___y_473_, v___y_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2___boxed(lean_object* v_00_u03b1_477_, lean_object* v_msg_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2(v_00_u03b1_477_, v_msg_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(lean_object* v_upperBound_483_, lean_object* v_snd_484_, lean_object* v_fst_485_, lean_object* v_a_486_, lean_object* v_b_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_a_492_; uint8_t v___x_496_; 
v___x_496_ = lean_nat_dec_lt(v_a_486_, v_upperBound_483_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v_a_486_);
lean_dec(v_fst_485_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v_b_487_);
return v___x_497_;
}
else
{
uint8_t v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_498_ = 0;
v___x_499_ = lean_box(0);
v___x_500_ = lean_box(v___x_498_);
v___x_501_ = lean_array_get(v___x_500_, v_snd_484_, v_a_486_);
lean_dec(v___x_500_);
v___x_502_ = lean_unbox(v___x_501_);
lean_dec(v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_inc(v_a_486_);
lean_inc(v_fst_485_);
v___x_503_ = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused___boxed), 5, 2);
lean_closure_set(v___x_503_, 0, v_fst_485_);
lean_closure_set(v___x_503_, 1, v_a_486_);
v___x_504_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_503_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_dec_ref_known(v___x_504_, 1);
v_a_492_ = v___x_499_;
goto v___jp_491_;
}
else
{
lean_dec(v_a_486_);
lean_dec(v_fst_485_);
return v___x_504_;
}
}
else
{
v_a_492_ = v___x_499_;
goto v___jp_491_;
}
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_a_486_, v___x_493_);
lean_dec(v_a_486_);
v_a_486_ = v___x_494_;
v_b_487_ = v_a_492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg___boxed(lean_object* v_upperBound_505_, lean_object* v_snd_506_, lean_object* v_fst_507_, lean_object* v_a_508_, lean_object* v_b_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_505_, v_snd_506_, v_fst_507_, v_a_508_, v_b_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v_snd_506_);
lean_dec(v_upperBound_505_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(lean_object* v_as_514_, size_t v_sz_515_, size_t v_i_516_, lean_object* v_b_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
uint8_t v___x_521_; 
v___x_521_ = lean_usize_dec_lt(v_i_516_, v_sz_515_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v_b_517_);
return v___x_522_;
}
else
{
lean_object* v_a_523_; lean_object* v_snd_524_; lean_object* v_fst_525_; lean_object* v_snd_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_a_523_ = lean_array_uget_borrowed(v_as_514_, v_i_516_);
v_snd_524_ = lean_ctor_get(v_a_523_, 1);
v_fst_525_ = lean_ctor_get(v_snd_524_, 0);
v_snd_526_ = lean_ctor_get(v_snd_524_, 1);
v___x_527_ = lean_box(0);
v___x_528_ = lean_array_get_size(v_snd_526_);
v___x_529_ = lean_unsigned_to_nat(0u);
lean_inc(v_fst_525_);
v___x_530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v___x_528_, v_snd_526_, v_fst_525_, v___x_529_, v___x_527_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_530_) == 0)
{
size_t v___x_531_; size_t v___x_532_; 
lean_dec_ref_known(v___x_530_, 1);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_516_, v___x_531_);
v_i_516_ = v___x_532_;
v_b_517_ = v___x_527_;
goto _start;
}
else
{
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8___boxed(lean_object* v_as_534_, lean_object* v_sz_535_, lean_object* v_i_536_, lean_object* v_b_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
size_t v_sz_boxed_541_; size_t v_i_boxed_542_; lean_object* v_res_543_; 
v_sz_boxed_541_ = lean_unbox_usize(v_sz_535_);
lean_dec(v_sz_535_);
v_i_boxed_542_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v_as_534_, v_sz_boxed_541_, v_i_boxed_542_, v_b_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v_as_534_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(lean_object* v_hi_544_, lean_object* v_pivot_545_, lean_object* v_as_546_, lean_object* v_i_547_, lean_object* v_k_548_){
_start:
{
uint8_t v___x_549_; 
v___x_549_ = lean_nat_dec_lt(v_k_548_, v_hi_544_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v_k_548_);
v___x_550_ = lean_array_fswap(v_as_546_, v_i_547_, v_hi_544_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_i_547_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v_fst_553_; lean_object* v_fst_554_; lean_object* v_start_555_; lean_object* v_start_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_552_ = lean_array_fget_borrowed(v_as_546_, v_k_548_);
v_fst_553_ = lean_ctor_get(v___x_552_, 0);
v_fst_554_ = lean_ctor_get(v_pivot_545_, 0);
v_start_555_ = lean_ctor_get(v_fst_553_, 0);
v_start_556_ = lean_ctor_get(v_fst_554_, 0);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_add(v_start_555_, v___x_557_);
v___x_559_ = lean_nat_dec_le(v___x_558_, v_start_556_);
lean_dec(v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
v___x_560_ = lean_nat_add(v_k_548_, v___x_557_);
lean_dec(v_k_548_);
v_k_548_ = v___x_560_;
goto _start;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_array_fswap(v_as_546_, v_i_547_, v_k_548_);
v___x_563_ = lean_nat_add(v_i_547_, v___x_557_);
lean_dec(v_i_547_);
v___x_564_ = lean_nat_add(v_k_548_, v___x_557_);
lean_dec(v_k_548_);
v_as_546_ = v___x_562_;
v_i_547_ = v___x_563_;
v_k_548_ = v___x_564_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg___boxed(lean_object* v_hi_566_, lean_object* v_pivot_567_, lean_object* v_as_568_, lean_object* v_i_569_, lean_object* v_k_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_566_, v_pivot_567_, v_as_568_, v_i_569_, v_k_570_);
lean_dec_ref(v_pivot_567_);
lean_dec(v_hi_566_);
return v_res_571_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg___lam__0(lean_object* v_x1_572_, lean_object* v_x2_573_){
_start:
{
lean_object* v_fst_574_; lean_object* v_fst_575_; lean_object* v_start_576_; lean_object* v_start_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_fst_574_ = lean_ctor_get(v_x1_572_, 0);
v_fst_575_ = lean_ctor_get(v_x2_573_, 0);
v_start_576_ = lean_ctor_get(v_fst_574_, 0);
v_start_577_ = lean_ctor_get(v_fst_575_, 0);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_start_576_, v___x_578_);
v___x_580_ = lean_nat_dec_le(v___x_579_, v_start_577_);
lean_dec(v___x_579_);
return v___x_580_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(lean_object* v_as_636_, size_t v_i_637_, size_t v_stop_638_, lean_object* v_b_639_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11___boxed(lean_object* v_as_646_, lean_object* v_i_647_, lean_object* v_stop_648_, lean_object* v_b_649_){
_start:
{
size_t v_i_boxed_650_; size_t v_stop_boxed_651_; lean_object* v_res_652_; 
v_i_boxed_650_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_stop_boxed_651_ = lean_unbox_usize(v_stop_648_);
lean_dec(v_stop_648_);
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_as_646_, v_i_boxed_650_, v_stop_boxed_651_, v_b_649_);
lean_dec_ref(v_as_646_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(lean_object* v_o_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_env_658_; lean_object* v___x_659_; lean_object* v_toEnvExtension_660_; lean_object* v_asyncMode_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_merged_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v___x_656_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_657_ = lean_st_ref_get(v___y_654_);
v_env_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc_ref(v_env_658_);
lean_dec(v___x_657_);
v___x_659_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_660_ = lean_ctor_get(v___x_659_, 0);
v_asyncMode_661_ = lean_ctor_get(v_toEnvExtension_660_, 2);
v___x_662_ = lean_box(0);
v___x_663_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_656_, v___x_659_, v_env_658_, v_asyncMode_661_, v___x_662_);
v_merged_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_663_, 1);
lean_dec(v_unused_673_);
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_merged_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v_merged_664_);
lean_ctor_set(v___x_666_, 0, v_o_653_);
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_o_653_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_merged_664_);
v___x_669_ = v_reuseFailAlloc_671_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg___boxed(lean_object* v_o_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_674_, v___y_675_);
lean_dec(v___y_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_scopes_683_; lean_object* v___x_684_; lean_object* v_opts_685_; lean_object* v___x_686_; 
v___x_681_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_682_ = lean_st_ref_get(v___y_679_);
v_scopes_683_ = lean_ctor_get(v___x_682_, 2);
lean_inc(v_scopes_683_);
lean_dec(v___x_682_);
v___x_684_ = l_List_head_x21___redArg(v___x_681_, v_scopes_683_);
lean_dec(v_scopes_683_);
v_opts_685_ = lean_ctor_get(v___x_684_, 1);
lean_inc_ref(v_opts_685_);
lean_dec(v___x_684_);
v___x_686_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_opts_685_, v___y_679_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0___boxed(lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(lean_object* v_a_691_, lean_object* v_x_692_){
_start:
{
if (lean_obj_tag(v_x_692_) == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_box(0);
return v___x_693_;
}
else
{
lean_object* v_key_694_; lean_object* v_value_695_; lean_object* v_tail_696_; uint8_t v___x_697_; 
v_key_694_ = lean_ctor_get(v_x_692_, 0);
v_value_695_ = lean_ctor_get(v_x_692_, 1);
v_tail_696_ = lean_ctor_get(v_x_692_, 2);
v___x_697_ = l_Lean_Syntax_instBEqRange_beq(v_key_694_, v_a_691_);
if (v___x_697_ == 0)
{
v_x_692_ = v_tail_696_;
goto _start;
}
else
{
lean_object* v___x_699_; 
lean_inc(v_value_695_);
v___x_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_699_, 0, v_value_695_);
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg___boxed(lean_object* v_a_700_, lean_object* v_x_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_700_, v_x_701_);
lean_dec(v_x_701_);
lean_dec_ref(v_a_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(lean_object* v_m_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_buckets_705_; lean_object* v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; uint64_t v_fold_710_; uint64_t v___x_711_; uint64_t v___x_712_; uint64_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v_buckets_705_ = lean_ctor_get(v_m_703_, 1);
v___x_706_ = lean_array_get_size(v_buckets_705_);
v___x_707_ = l_Lean_Syntax_instHashableRange_hash(v_a_704_);
v___x_708_ = 32ULL;
v___x_709_ = lean_uint64_shift_right(v___x_707_, v___x_708_);
v_fold_710_ = lean_uint64_xor(v___x_707_, v___x_709_);
v___x_711_ = 16ULL;
v___x_712_ = lean_uint64_shift_right(v_fold_710_, v___x_711_);
v___x_713_ = lean_uint64_xor(v_fold_710_, v___x_712_);
v___x_714_ = lean_uint64_to_usize(v___x_713_);
v___x_715_ = lean_usize_of_nat(v___x_706_);
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_sub(v___x_715_, v___x_716_);
v___x_718_ = lean_usize_land(v___x_714_, v___x_717_);
v___x_719_ = lean_array_uget_borrowed(v_buckets_705_, v___x_718_);
v___x_720_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_704_, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg___boxed(lean_object* v_m_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_721_, v_a_722_);
lean_dec_ref(v_a_722_);
lean_dec_ref(v_m_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(uint8_t v___x_724_, lean_object* v_as_725_, lean_object* v_bs_726_, lean_object* v_i_727_, lean_object* v_cs_728_){
_start:
{
uint8_t v___y_730_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_as_725_);
v___x_737_ = lean_nat_dec_lt(v_i_727_, v___x_736_);
if (v___x_737_ == 0)
{
lean_dec(v_i_727_);
return v_cs_728_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = lean_array_get_size(v_bs_726_);
v___x_739_ = lean_nat_dec_lt(v_i_727_, v___x_738_);
if (v___x_739_ == 0)
{
lean_dec(v_i_727_);
return v_cs_728_;
}
else
{
lean_object* v_a_740_; uint8_t v___x_741_; 
v_a_740_ = lean_array_fget_borrowed(v_as_725_, v_i_727_);
v___x_741_ = lean_unbox(v_a_740_);
if (v___x_741_ == 0)
{
lean_object* v_b_742_; uint8_t v___x_743_; 
v_b_742_ = lean_array_fget_borrowed(v_bs_726_, v_i_727_);
v___x_743_ = lean_unbox(v_b_742_);
v___y_730_ = v___x_743_;
goto v___jp_729_;
}
else
{
v___y_730_ = v___x_724_;
goto v___jp_729_;
}
}
}
v___jp_729_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_unsigned_to_nat(1u);
v___x_732_ = lean_nat_add(v_i_727_, v___x_731_);
lean_dec(v_i_727_);
v___x_733_ = lean_box(v___y_730_);
v___x_734_ = lean_array_push(v_cs_728_, v___x_733_);
v_i_727_ = v___x_732_;
v_cs_728_ = v___x_734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3___boxed(lean_object* v___x_744_, lean_object* v_as_745_, lean_object* v_bs_746_, lean_object* v_i_747_, lean_object* v_cs_748_){
_start:
{
uint8_t v___x_12843__boxed_749_; lean_object* v_res_750_; 
v___x_12843__boxed_749_ = lean_unbox(v___x_744_);
v_res_750_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_12843__boxed_749_, v_as_745_, v_bs_746_, v_i_747_, v_cs_748_);
lean_dec_ref(v_bs_746_);
lean_dec_ref(v_as_745_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(lean_object* v_msgData_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; lean_object* v_env_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_scopes_758_; lean_object* v___x_759_; lean_object* v_opts_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_754_ = lean_st_ref_get(v___y_752_);
v_env_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc_ref(v_env_755_);
lean_dec(v___x_754_);
v___x_756_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_757_ = lean_st_ref_get(v___y_752_);
v_scopes_758_ = lean_ctor_get(v___x_757_, 2);
lean_inc(v_scopes_758_);
lean_dec(v___x_757_);
v___x_759_ = l_List_head_x21___redArg(v___x_756_, v_scopes_758_);
lean_dec(v_scopes_758_);
v_opts_760_ = lean_ctor_get(v___x_759_, 1);
lean_inc_ref(v_opts_760_);
lean_dec(v___x_759_);
v___x_761_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__2);
v___x_762_ = lean_unsigned_to_nat(32u);
v___x_763_ = lean_mk_empty_array_with_capacity(v___x_762_);
lean_dec_ref(v___x_763_);
v___x_764_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__2_spec__3___closed__5);
v___x_765_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_765_, 0, v_env_755_);
lean_ctor_set(v___x_765_, 1, v___x_761_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
lean_ctor_set(v___x_765_, 3, v_opts_760_);
v___x_766_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_msgData_751_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_768_, v___y_769_);
lean_dec(v___y_769_);
return v_res_771_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_box(1);
v___x_773_ = l_Lean_MessageData_ofFormat(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__2));
v___x_778_ = l_Lean_MessageData_ofFormat(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
return v_x_779_;
}
else
{
lean_object* v_head_781_; lean_object* v_tail_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_804_; 
v_head_781_ = lean_ctor_get(v_x_780_, 0);
v_tail_782_ = lean_ctor_get(v_x_780_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_780_);
if (v_isSharedCheck_804_ == 0)
{
v___x_784_ = v_x_780_;
v_isShared_785_ = v_isSharedCheck_804_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_tail_782_);
lean_inc(v_head_781_);
lean_dec(v_x_780_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_804_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_before_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_802_; 
v_before_786_ = lean_ctor_get(v_head_781_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_head_781_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_head_781_, 1);
lean_dec(v_unused_803_);
v___x_788_ = v_head_781_;
v_isShared_789_ = v_isSharedCheck_802_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_before_786_);
lean_dec(v_head_781_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_802_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 7);
lean_ctor_set(v___x_788_, 1, v___x_790_);
lean_ctor_set(v___x_788_, 0, v_x_779_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_x_779_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_790_);
v___x_792_ = v_reuseFailAlloc_801_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__3);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 7);
lean_ctor_set(v___x_784_, 1, v___x_793_);
lean_ctor_set(v___x_784_, 0, v___x_792_);
v___x_795_ = v___x_784_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___x_793_);
v___x_795_ = v_reuseFailAlloc_800_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = l_Lean_MessageData_ofSyntax(v_before_786_);
v___x_797_ = l_Lean_indentD(v___x_796_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_795_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v_x_779_ = v___x_798_;
v_x_780_ = v_tail_782_;
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
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__1));
v___x_809_ = l_Lean_MessageData_ofFormat(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(lean_object* v_msgData_810_, lean_object* v_macroStack_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v_scopes_816_; lean_object* v___x_817_; lean_object* v_opts_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_814_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_815_ = lean_st_ref_get(v___y_812_);
v_scopes_816_ = lean_ctor_get(v___x_815_, 2);
lean_inc(v_scopes_816_);
lean_dec(v___x_815_);
v___x_817_ = l_List_head_x21___redArg(v___x_814_, v_scopes_816_);
lean_dec(v_scopes_816_);
v_opts_818_ = lean_ctor_get(v___x_817_, 1);
lean_inc_ref(v_opts_818_);
lean_dec(v___x_817_);
v___x_819_ = l_Lean_Elab_pp_macroStack;
v___x_820_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_warnUnused_spec__0_spec__0_spec__1_spec__5(v_opts_818_, v___x_819_);
lean_dec_ref(v_opts_818_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec(v_macroStack_811_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v_msgData_810_);
return v___x_821_;
}
else
{
if (lean_obj_tag(v_macroStack_811_) == 0)
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v_msgData_810_);
return v___x_822_;
}
else
{
lean_object* v_head_823_; lean_object* v_after_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_839_; 
v_head_823_ = lean_ctor_get(v_macroStack_811_, 0);
lean_inc(v_head_823_);
v_after_824_ = lean_ctor_get(v_head_823_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_head_823_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v_head_823_, 0);
lean_dec(v_unused_840_);
v___x_826_ = v_head_823_;
v_isShared_827_ = v_isSharedCheck_839_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_after_824_);
lean_dec(v_head_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_839_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21___closed__0);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 7);
lean_ctor_set(v___x_826_, 1, v___x_828_);
lean_ctor_set(v___x_826_, 0, v_msgData_810_);
v___x_830_ = v___x_826_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_msgData_810_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_838_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_msgData_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_831_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___closed__2);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_MessageData_ofSyntax(v_after_824_);
v___x_834_ = l_Lean_indentD(v___x_833_);
v_msgData_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_835_, 0, v___x_832_);
lean_ctor_set(v_msgData_835_, 1, v___x_834_);
v___x_836_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12_spec__21(v_msgData_835_, v_macroStack_811_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v_msgData_841_, lean_object* v_macroStack_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_841_, v_macroStack_842_, v___y_843_);
lean_dec(v___y_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(lean_object* v_msg_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Elab_Command_getRef___redArg(v___y_847_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v_macroStack_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_865_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref_known(v___x_850_, 1);
v_macroStack_852_ = lean_ctor_get(v___y_847_, 4);
v___x_853_ = l_Lean_Elab_getBetterRef(v_a_851_, v_macroStack_852_);
lean_dec(v_a_851_);
v___x_854_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msg_846_, v___y_848_);
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref(v___x_854_);
lean_inc(v_macroStack_852_);
v___x_856_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_a_855_, v_macroStack_852_, v___y_848_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_865_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_853_);
lean_ctor_set(v___x_861_, 1, v_a_857_);
if (v_isShared_860_ == 0)
{
lean_ctor_set_tag(v___x_859_, 1);
lean_ctor_set(v___x_859_, 0, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v_msg_846_);
v_a_866_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_850_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_850_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg___boxed(lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(lean_object* v_ref_879_, lean_object* v_msg_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Elab_Command_getRef___redArg(v___y_881_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v_fileName_886_; lean_object* v_fileMap_887_; lean_object* v_currRecDepth_888_; lean_object* v_cmdPos_889_; lean_object* v_macroStack_890_; lean_object* v_quotContext_x3f_891_; lean_object* v_currMacroScope_892_; lean_object* v_snap_x3f_893_; lean_object* v_cancelTk_x3f_894_; uint8_t v_suppressElabErrors_895_; lean_object* v_ref_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v_fileName_886_ = lean_ctor_get(v___y_881_, 0);
v_fileMap_887_ = lean_ctor_get(v___y_881_, 1);
v_currRecDepth_888_ = lean_ctor_get(v___y_881_, 2);
v_cmdPos_889_ = lean_ctor_get(v___y_881_, 3);
v_macroStack_890_ = lean_ctor_get(v___y_881_, 4);
v_quotContext_x3f_891_ = lean_ctor_get(v___y_881_, 5);
v_currMacroScope_892_ = lean_ctor_get(v___y_881_, 6);
v_snap_x3f_893_ = lean_ctor_get(v___y_881_, 8);
v_cancelTk_x3f_894_ = lean_ctor_get(v___y_881_, 9);
v_suppressElabErrors_895_ = lean_ctor_get_uint8(v___y_881_, sizeof(void*)*10);
v_ref_896_ = l_Lean_replaceRef(v_ref_879_, v_a_885_);
lean_dec(v_a_885_);
lean_inc(v_cancelTk_x3f_894_);
lean_inc(v_snap_x3f_893_);
lean_inc(v_currMacroScope_892_);
lean_inc(v_quotContext_x3f_891_);
lean_inc(v_macroStack_890_);
lean_inc(v_cmdPos_889_);
lean_inc(v_currRecDepth_888_);
lean_inc_ref(v_fileMap_887_);
lean_inc_ref(v_fileName_886_);
v___x_897_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_897_, 0, v_fileName_886_);
lean_ctor_set(v___x_897_, 1, v_fileMap_887_);
lean_ctor_set(v___x_897_, 2, v_currRecDepth_888_);
lean_ctor_set(v___x_897_, 3, v_cmdPos_889_);
lean_ctor_set(v___x_897_, 4, v_macroStack_890_);
lean_ctor_set(v___x_897_, 5, v_quotContext_x3f_891_);
lean_ctor_set(v___x_897_, 6, v_currMacroScope_892_);
lean_ctor_set(v___x_897_, 7, v_ref_896_);
lean_ctor_set(v___x_897_, 8, v_snap_x3f_893_);
lean_ctor_set(v___x_897_, 9, v_cancelTk_x3f_894_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*10, v_suppressElabErrors_895_);
v___x_898_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_880_, v___x_897_, v___y_882_);
lean_dec_ref_known(v___x_897_, 10);
return v___x_898_;
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v_msg_880_);
v_a_899_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_884_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_884_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg___boxed(lean_object* v_ref_907_, lean_object* v_msg_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_907_, v_msg_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v_ref_907_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
if (lean_obj_tag(v_x_914_) == 0)
{
return v_x_913_;
}
else
{
lean_object* v_key_915_; lean_object* v_value_916_; lean_object* v_tail_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_940_; 
v_key_915_ = lean_ctor_get(v_x_914_, 0);
v_value_916_ = lean_ctor_get(v_x_914_, 1);
v_tail_917_ = lean_ctor_get(v_x_914_, 2);
v_isSharedCheck_940_ = !lean_is_exclusive(v_x_914_);
if (v_isSharedCheck_940_ == 0)
{
v___x_919_ = v_x_914_;
v_isShared_920_ = v_isSharedCheck_940_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_tail_917_);
lean_inc(v_value_916_);
lean_inc(v_key_915_);
lean_dec(v_x_914_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_940_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; uint64_t v___x_922_; uint64_t v___x_923_; uint64_t v___x_924_; uint64_t v_fold_925_; uint64_t v___x_926_; uint64_t v___x_927_; uint64_t v___x_928_; size_t v___x_929_; size_t v___x_930_; size_t v___x_931_; size_t v___x_932_; size_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_921_ = lean_array_get_size(v_x_913_);
v___x_922_ = l_Lean_Syntax_instHashableRange_hash(v_key_915_);
v___x_923_ = 32ULL;
v___x_924_ = lean_uint64_shift_right(v___x_922_, v___x_923_);
v_fold_925_ = lean_uint64_xor(v___x_922_, v___x_924_);
v___x_926_ = 16ULL;
v___x_927_ = lean_uint64_shift_right(v_fold_925_, v___x_926_);
v___x_928_ = lean_uint64_xor(v_fold_925_, v___x_927_);
v___x_929_ = lean_uint64_to_usize(v___x_928_);
v___x_930_ = lean_usize_of_nat(v___x_921_);
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_sub(v___x_930_, v___x_931_);
v___x_933_ = lean_usize_land(v___x_929_, v___x_932_);
v___x_934_ = lean_array_uget_borrowed(v_x_913_, v___x_933_);
lean_inc(v___x_934_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 2, v___x_934_);
v___x_936_ = v___x_919_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_key_915_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_value_916_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v___x_934_);
v___x_936_ = v_reuseFailAlloc_939_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = lean_array_uset(v_x_913_, v___x_933_, v___x_936_);
v_x_913_ = v___x_937_;
v_x_914_ = v_tail_917_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(lean_object* v_i_941_, lean_object* v_source_942_, lean_object* v_target_943_){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_array_get_size(v_source_942_);
v___x_945_ = lean_nat_dec_lt(v_i_941_, v___x_944_);
if (v___x_945_ == 0)
{
lean_dec_ref(v_source_942_);
lean_dec(v_i_941_);
return v_target_943_;
}
else
{
lean_object* v_es_946_; lean_object* v___x_947_; lean_object* v_source_948_; lean_object* v_target_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_es_946_ = lean_array_fget(v_source_942_, v_i_941_);
v___x_947_ = lean_box(0);
v_source_948_ = lean_array_fset(v_source_942_, v_i_941_, v___x_947_);
v_target_949_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_target_943_, v_es_946_);
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = lean_nat_add(v_i_941_, v___x_950_);
lean_dec(v_i_941_);
v_i_941_ = v___x_951_;
v_source_942_ = v_source_948_;
v_target_943_ = v_target_949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(lean_object* v_data_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_nbuckets_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_954_ = lean_array_get_size(v_data_953_);
v___x_955_ = lean_unsigned_to_nat(2u);
v_nbuckets_956_ = lean_nat_mul(v___x_954_, v___x_955_);
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_box(0);
v___x_959_ = lean_mk_array(v_nbuckets_956_, v___x_958_);
v___x_960_ = lean_array_propagate_mark(v_data_953_, v___x_959_);
v___x_961_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v___x_957_, v_data_953_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(lean_object* v_a_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_963_) == 0)
{
uint8_t v___x_964_; 
v___x_964_ = 0;
return v___x_964_;
}
else
{
lean_object* v_key_965_; lean_object* v_tail_966_; uint8_t v___x_967_; 
v_key_965_ = lean_ctor_get(v_x_963_, 0);
v_tail_966_ = lean_ctor_get(v_x_963_, 2);
v___x_967_ = l_Lean_Syntax_instBEqRange_beq(v_key_965_, v_a_962_);
if (v___x_967_ == 0)
{
v_x_963_ = v_tail_966_;
goto _start;
}
else
{
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg___boxed(lean_object* v_a_969_, lean_object* v_x_970_){
_start:
{
uint8_t v_res_971_; lean_object* v_r_972_; 
v_res_971_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_969_, v_x_970_);
lean_dec(v_x_970_);
lean_dec_ref(v_a_969_);
v_r_972_ = lean_box(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(lean_object* v_a_973_, lean_object* v_b_974_, lean_object* v_x_975_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_dec(v_b_974_);
lean_dec_ref(v_a_973_);
return v_x_975_;
}
else
{
lean_object* v_key_976_; lean_object* v_value_977_; lean_object* v_tail_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_990_; 
v_key_976_ = lean_ctor_get(v_x_975_, 0);
v_value_977_ = lean_ctor_get(v_x_975_, 1);
v_tail_978_ = lean_ctor_get(v_x_975_, 2);
v_isSharedCheck_990_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_990_ == 0)
{
v___x_980_ = v_x_975_;
v_isShared_981_ = v_isSharedCheck_990_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_tail_978_);
lean_inc(v_value_977_);
lean_inc(v_key_976_);
lean_dec(v_x_975_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_990_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
uint8_t v___x_982_; 
v___x_982_ = l_Lean_Syntax_instBEqRange_beq(v_key_976_, v_a_973_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_973_, v_b_974_, v_tail_978_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 2, v___x_983_);
v___x_985_ = v___x_980_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_key_976_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_value_977_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
else
{
lean_object* v___x_988_; 
lean_dec(v_value_977_);
lean_dec(v_key_976_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v_b_974_);
lean_ctor_set(v___x_980_, 0, v_a_973_);
v___x_988_ = v___x_980_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_973_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_b_974_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_tail_978_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(lean_object* v_m_991_, lean_object* v_a_992_, lean_object* v_b_993_){
_start:
{
lean_object* v_size_994_; lean_object* v_buckets_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1038_; 
v_size_994_ = lean_ctor_get(v_m_991_, 0);
v_buckets_995_ = lean_ctor_get(v_m_991_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_m_991_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_997_ = v_m_991_;
v_isShared_998_ = v_isSharedCheck_1038_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_buckets_995_);
lean_inc(v_size_994_);
lean_dec(v_m_991_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1038_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; uint64_t v___x_1000_; uint64_t v___x_1001_; uint64_t v___x_1002_; uint64_t v_fold_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; uint64_t v___x_1006_; size_t v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; lean_object* v_bkt_1012_; uint8_t v___x_1013_; 
v___x_999_ = lean_array_get_size(v_buckets_995_);
v___x_1000_ = l_Lean_Syntax_instHashableRange_hash(v_a_992_);
v___x_1001_ = 32ULL;
v___x_1002_ = lean_uint64_shift_right(v___x_1000_, v___x_1001_);
v_fold_1003_ = lean_uint64_xor(v___x_1000_, v___x_1002_);
v___x_1004_ = 16ULL;
v___x_1005_ = lean_uint64_shift_right(v_fold_1003_, v___x_1004_);
v___x_1006_ = lean_uint64_xor(v_fold_1003_, v___x_1005_);
v___x_1007_ = lean_uint64_to_usize(v___x_1006_);
v___x_1008_ = lean_usize_of_nat(v___x_999_);
v___x_1009_ = ((size_t)1ULL);
v___x_1010_ = lean_usize_sub(v___x_1008_, v___x_1009_);
v___x_1011_ = lean_usize_land(v___x_1007_, v___x_1010_);
v_bkt_1012_ = lean_array_uget_borrowed(v_buckets_995_, v___x_1011_);
v___x_1013_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_992_, v_bkt_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; lean_object* v_size_x27_1015_; lean_object* v___x_1016_; lean_object* v_buckets_x27_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1014_ = lean_unsigned_to_nat(1u);
v_size_x27_1015_ = lean_nat_add(v_size_994_, v___x_1014_);
lean_dec(v_size_994_);
lean_inc(v_bkt_1012_);
v___x_1016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1016_, 0, v_a_992_);
lean_ctor_set(v___x_1016_, 1, v_b_993_);
lean_ctor_set(v___x_1016_, 2, v_bkt_1012_);
v_buckets_x27_1017_ = lean_array_uset(v_buckets_995_, v___x_1011_, v___x_1016_);
v___x_1018_ = lean_unsigned_to_nat(4u);
v___x_1019_ = lean_nat_mul(v_size_x27_1015_, v___x_1018_);
v___x_1020_ = lean_unsigned_to_nat(3u);
v___x_1021_ = lean_nat_div(v___x_1019_, v___x_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_array_get_size(v_buckets_x27_1017_);
v___x_1023_ = lean_nat_dec_le(v___x_1021_, v___x_1022_);
lean_dec(v___x_1021_);
if (v___x_1023_ == 0)
{
lean_object* v_val_1024_; lean_object* v___x_1026_; 
v_val_1024_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_buckets_x27_1017_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_val_1024_);
lean_ctor_set(v___x_997_, 0, v_size_x27_1015_);
v___x_1026_ = v___x_997_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_size_x27_1015_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_val_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
else
{
lean_object* v___x_1029_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_buckets_x27_1017_);
lean_ctor_set(v___x_997_, 0, v_size_x27_1015_);
v___x_1029_ = v___x_997_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_size_x27_1015_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_buckets_x27_1017_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v___x_1031_; lean_object* v_buckets_x27_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_inc(v_bkt_1012_);
v___x_1031_ = lean_box(0);
v_buckets_x27_1032_ = lean_array_uset(v_buckets_995_, v___x_1011_, v___x_1031_);
v___x_1033_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_992_, v_b_993_, v_bkt_1012_);
v___x_1034_ = lean_array_uset(v_buckets_x27_1032_, v___x_1011_, v___x_1033_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1034_);
v___x_1036_ = v___x_997_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_size_994_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__1));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__3));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(lean_object* v___x_1059_, lean_object* v_val_1060_, uint8_t v___x_1061_, lean_object* v_ci_1062_, lean_object* v_info_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
if (lean_obj_tag(v_info_1063_) == 10)
{
lean_object* v_i_1068_; lean_object* v_stx_1069_; lean_object* v_value_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1164_; 
v_i_1068_ = lean_ctor_get(v_info_1063_, 0);
lean_inc_ref(v_i_1068_);
v_stx_1069_ = lean_ctor_get(v_i_1068_, 0);
v_value_1070_ = lean_ctor_get(v_i_1068_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_i_1068_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1072_ = v_i_1068_;
v_isShared_1073_ = v_isSharedCheck_1164_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_value_1070_);
lean_inc(v_stx_1069_);
lean_dec(v_i_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1164_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; 
v___x_1074_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_value_1070_, v___x_1059_);
lean_dec(v_value_1070_);
if (lean_obj_tag(v___x_1074_) == 1)
{
lean_object* v_val_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1154_; 
v_val_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1154_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_val_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1154_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Elab_Info_range_x3f(v_info_1063_);
if (lean_obj_tag(v___x_1079_) == 1)
{
lean_object* v_val_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1149_; 
v_val_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1149_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_val_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1149_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_maskAcc_1085_; lean_object* v___y_1096_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__6));
lean_inc(v_stx_1069_);
v___x_1137_ = l_Lean_Syntax_isOfKind(v_stx_1069_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__8));
lean_inc(v_stx_1069_);
v___x_1139_ = l_Lean_Syntax_isOfKind(v_stx_1069_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1147_; 
lean_del_object(v___x_1082_);
lean_dec(v_val_1080_);
lean_del_object(v___x_1077_);
lean_dec(v_val_1075_);
lean_del_object(v___x_1072_);
lean_dec(v_stx_1069_);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_info_1063_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v_info_1063_, 0);
lean_dec(v_unused_1148_);
v___x_1141_ = v_info_1063_;
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_info_1063_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_box(0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1143_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
else
{
goto v___jp_1100_;
}
}
else
{
goto v___jp_1100_;
}
v___jp_1084_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_st_ref_take(v_val_1060_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v_maskAcc_1085_);
v___x_1088_ = v___x_1072_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_stx_1069_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_maskAcc_1085_);
v___x_1088_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v___x_1086_, v_val_1080_, v___x_1088_);
v___x_1090_ = lean_st_ref_put(v_val_1060_, v___x_1089_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1090_);
v___x_1092_ = v___x_1082_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
v___jp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__0));
v___x_1099_ = l_Array_zipWithMAux___at___00Lean_Linter_unusedSimpArgs_spec__3(v___x_1061_, v_val_1075_, v___y_1096_, v___x_1097_, v___x_1098_);
lean_dec_ref(v___y_1096_);
lean_dec(v_val_1075_);
v_maskAcc_1085_ = v___x_1099_;
goto v___jp_1084_;
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_st_ref_get(v_val_1060_);
v___x_1102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v___x_1101_, v_val_1080_);
lean_dec(v___x_1101_);
if (lean_obj_tag(v___x_1102_) == 1)
{
lean_object* v_val_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1135_; 
v_val_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1135_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_val_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1135_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_snd_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1133_; 
v_snd_1107_ = lean_ctor_get(v_val_1103_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_val_1103_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v_val_1103_, 0);
lean_dec(v_unused_1134_);
v___x_1109_ = v_val_1103_;
v_isShared_1110_ = v_isSharedCheck_1133_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snd_1107_);
lean_dec(v_val_1103_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1133_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = lean_array_get_size(v_val_1075_);
v___x_1112_ = lean_array_get_size(v_snd_1107_);
v___x_1113_ = lean_nat_dec_eq(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1114_ = l_Lean_Elab_Info_stx(v_info_1063_);
lean_dec_ref_known(v_info_1063_, 1);
v___x_1115_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__2);
v___x_1116_ = l_Nat_reprFast(v___x_1112_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 3);
lean_ctor_set(v___x_1105_, 0, v___x_1116_);
v___x_1118_ = v___x_1105_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = l_Lean_MessageData_ofFormat(v___x_1118_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 7);
lean_ctor_set(v___x_1109_, 1, v___x_1119_);
lean_ctor_set(v___x_1109_, 0, v___x_1115_);
v___x_1121_ = v___x_1109_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___closed__4);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = l_Nat_reprFast(v___x_1111_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 3);
lean_ctor_set(v___x_1077_, 0, v___x_1124_);
v___x_1126_ = v___x_1077_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = l_Lean_MessageData_ofFormat(v___x_1126_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1123_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v___x_1114_, v___x_1128_, v___y_1065_, v___y_1066_);
lean_dec(v___x_1114_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_dec_ref_known(v___x_1129_, 1);
v___y_1096_ = v_snd_1107_;
goto v___jp_1095_;
}
else
{
lean_dec(v_snd_1107_);
lean_del_object(v___x_1082_);
lean_dec(v_val_1080_);
lean_dec(v_val_1075_);
lean_del_object(v___x_1072_);
lean_dec(v_stx_1069_);
return v___x_1129_;
}
}
}
}
}
else
{
lean_del_object(v___x_1109_);
lean_del_object(v___x_1105_);
lean_del_object(v___x_1077_);
lean_dec_ref_known(v_info_1063_, 1);
v___y_1096_ = v_snd_1107_;
goto v___jp_1095_;
}
}
}
}
else
{
lean_dec(v___x_1102_);
lean_del_object(v___x_1077_);
lean_dec_ref_known(v_info_1063_, 1);
v_maskAcc_1085_ = v_val_1075_;
goto v___jp_1084_;
}
}
}
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec(v___x_1079_);
lean_dec(v_val_1075_);
lean_del_object(v___x_1072_);
lean_dec(v_stx_1069_);
lean_dec_ref_known(v_info_1063_, 1);
v___x_1150_ = lean_box(0);
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1150_);
v___x_1152_ = v___x_1077_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v___x_1074_);
lean_del_object(v___x_1072_);
lean_dec(v_stx_1069_);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_info_1063_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v_info_1063_, 0);
lean_dec(v_unused_1163_);
v___x_1156_ = v_info_1063_;
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
else
{
lean_dec(v_info_1063_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_box(0);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v_info_1063_);
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed(lean_object* v___x_1167_, lean_object* v_val_1168_, lean_object* v___x_1169_, lean_object* v_ci_1170_, lean_object* v_info_1171_, lean_object* v_x_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
uint8_t v___x_13417__boxed_1176_; lean_object* v_res_1177_; 
v___x_13417__boxed_1176_ = lean_unbox(v___x_1169_);
v_res_1177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1(v___x_1167_, v_val_1168_, v___x_13417__boxed_1176_, v_ci_1170_, v_info_1171_, v_x_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec_ref(v_x_1172_);
lean_dec_ref(v_ci_1170_);
lean_dec(v_val_1168_);
lean_dec(v___x_1167_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(lean_object* v_postNode_1178_, lean_object* v_ci_1179_, lean_object* v_i_1180_, lean_object* v_cs_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
v___x_1186_ = lean_apply_6(v_postNode_1178_, v_ci_1179_, v_i_1180_, v_cs_1181_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed(lean_object* v_postNode_1187_, lean_object* v_ci_1188_, lean_object* v_i_1189_, lean_object* v_cs_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0(v_postNode_1187_, v_ci_1188_, v_i_1189_, v_cs_1190_, v_x_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v_x_1191_);
return v_res_1195_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_instMonadEIO___redArg();
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(lean_object* v_msg_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_toApplicative_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1236_; 
v___x_1203_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__0);
v___x_1204_ = l_StateRefT_x27_instMonad___redArg(v___x_1203_);
v_toApplicative_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1204_, 1);
lean_dec(v_unused_1237_);
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1236_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_toApplicative_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1236_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_toFunctor_1209_; lean_object* v_toSeq_1210_; lean_object* v_toSeqLeft_1211_; lean_object* v_toSeqRight_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1234_; 
v_toFunctor_1209_ = lean_ctor_get(v_toApplicative_1205_, 0);
v_toSeq_1210_ = lean_ctor_get(v_toApplicative_1205_, 2);
v_toSeqLeft_1211_ = lean_ctor_get(v_toApplicative_1205_, 3);
v_toSeqRight_1212_ = lean_ctor_get(v_toApplicative_1205_, 4);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_toApplicative_1205_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v_toApplicative_1205_, 1);
lean_dec(v_unused_1235_);
v___x_1214_ = v_toApplicative_1205_;
v_isShared_1215_ = v_isSharedCheck_1234_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_toSeqRight_1212_);
lean_inc(v_toSeqLeft_1211_);
lean_inc(v_toSeq_1210_);
lean_inc(v_toFunctor_1209_);
lean_dec(v_toApplicative_1205_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1234_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___x_1225_; 
v___f_1216_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__1));
v___f_1217_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___closed__2));
lean_inc_ref(v_toFunctor_1209_);
v___f_1218_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1218_, 0, v_toFunctor_1209_);
v___f_1219_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1219_, 0, v_toFunctor_1209_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___f_1218_);
lean_ctor_set(v___x_1220_, 1, v___f_1219_);
v___f_1221_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1221_, 0, v_toSeqRight_1212_);
v___f_1222_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1222_, 0, v_toSeqLeft_1211_);
v___f_1223_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1223_, 0, v_toSeq_1210_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 4, v___f_1221_);
lean_ctor_set(v___x_1214_, 3, v___f_1222_);
lean_ctor_set(v___x_1214_, 2, v___f_1223_);
lean_ctor_set(v___x_1214_, 1, v___f_1216_);
lean_ctor_set(v___x_1214_, 0, v___x_1220_);
v___x_1225_ = v___x_1214_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___f_1216_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v___f_1223_);
lean_ctor_set(v_reuseFailAlloc_1233_, 3, v___f_1222_);
lean_ctor_set(v_reuseFailAlloc_1233_, 4, v___f_1221_);
v___x_1225_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___f_1217_);
lean_ctor_set(v___x_1207_, 0, v___x_1225_);
v___x_1227_ = v___x_1207_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___f_1217_);
v___x_1227_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_11887__overap_1230_; lean_object* v___x_1231_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = l_instInhabitedOfMonad___redArg(v___x_1227_, v___x_1228_);
v___x_11887__overap_1230_ = lean_panic_fn_borrowed(v___x_1229_, v_msg_1199_);
lean_dec(v___x_1229_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1200_);
v___x_1231_ = lean_apply_3(v___x_11887__overap_1230_, v___y_1200_, v___y_1201_, lean_box(0));
return v___x_1231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg___boxed(lean_object* v_msg_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1242_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__2));
v___x_1247_ = lean_unsigned_to_nat(21u);
v___x_1248_ = lean_unsigned_to_nat(65u);
v___x_1249_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__1));
v___x_1250_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__0));
v___x_1251_ = l_mkPanicMessageWithDecl(v___x_1250_, v___x_1249_, v___x_1248_, v___x_1247_, v___x_1246_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(lean_object* v_preNode_1252_, lean_object* v_postNode_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
switch(lean_obj_tag(v_x_1255_))
{
case 0:
{
lean_object* v_i_1259_; lean_object* v_t_1260_; lean_object* v___x_1261_; 
v_i_1259_ = lean_ctor_get(v_x_1255_, 0);
lean_inc_ref(v_i_1259_);
v_t_1260_ = lean_ctor_get(v_x_1255_, 1);
lean_inc_ref(v_t_1260_);
lean_dec_ref_known(v_x_1255_, 2);
v___x_1261_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1259_, v_x_1254_);
v_x_1254_ = v___x_1261_;
v_x_1255_ = v_t_1260_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref_known(v_x_1255_, 2);
lean_dec_ref(v_postNode_1253_);
lean_dec_ref(v_preNode_1252_);
v___x_1263_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___closed__3);
v___x_1264_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v___x_1263_, v___y_1256_, v___y_1257_);
return v___x_1264_;
}
else
{
lean_object* v_i_1265_; lean_object* v_children_1266_; lean_object* v_val_1267_; lean_object* v___x_1268_; 
v_i_1265_ = lean_ctor_get(v_x_1255_, 0);
lean_inc_ref_n(v_i_1265_, 2);
v_children_1266_ = lean_ctor_get(v_x_1255_, 1);
lean_inc_ref_n(v_children_1266_, 2);
lean_dec_ref_known(v_x_1255_, 2);
v_val_1267_ = lean_ctor_get(v_x_1254_, 0);
lean_inc_n(v_val_1267_, 2);
lean_inc_ref(v_preNode_1252_);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
v___x_1268_ = lean_apply_6(v_preNode_1252_, v_val_1267_, v_i_1265_, v_children_1266_, v___y_1256_, v___y_1257_, lean_box(0));
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; uint8_t v___x_1270_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = lean_unbox(v_a_1269_);
lean_dec(v_a_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1295_; 
lean_dec_ref(v_preNode_1252_);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_x_1254_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v_x_1254_, 0);
lean_dec(v_unused_1296_);
v___x_1272_ = v_x_1254_;
v_isShared_1273_ = v_isSharedCheck_1295_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v_x_1254_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1295_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_box(0);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
v___x_1275_ = lean_apply_7(v_postNode_1253_, v_val_1267_, v_i_1265_, v_children_1266_, v___x_1274_, v___y_1256_, v___y_1257_, lean_box(0));
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1286_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v_a_1276_);
v___x_1281_ = v___x_1272_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_del_object(v___x_1272_);
v_a_1287_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1275_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1275_);
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
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1254_, v_i_1265_);
v___x_1298_ = l_Lean_PersistentArray_toList___redArg(v_children_1266_);
v___x_1299_ = lean_box(0);
lean_inc_ref(v_postNode_1253_);
v___x_1300_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1252_, v_postNode_1253_, v___x_1297_, v___x_1298_, v___x_1299_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1302_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
v___x_1302_ = lean_apply_7(v_postNode_1253_, v_val_1267_, v_i_1265_, v_children_1266_, v_a_1301_, v___y_1256_, v___y_1257_, lean_box(0));
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_a_1303_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1307_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
v_a_1312_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1302_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1302_);
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
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v_val_1267_);
lean_dec_ref(v_children_1266_);
lean_dec_ref(v_i_1265_);
lean_dec_ref(v_postNode_1253_);
v_a_1320_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1300_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1300_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
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
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_val_1267_);
lean_dec_ref(v_children_1266_);
lean_dec_ref(v_i_1265_);
lean_dec_ref_known(v_x_1254_, 1);
lean_dec_ref(v_postNode_1253_);
lean_dec_ref(v_preNode_1252_);
v_a_1328_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1268_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1268_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
default: 
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_x_1254_);
lean_dec_ref(v_postNode_1253_);
lean_dec_ref(v_preNode_1252_);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_x_1255_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v_x_1255_, 0);
lean_dec(v_unused_1344_);
v___x_1337_ = v_x_1255_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v_x_1255_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_box(0);
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(lean_object* v_preNode_1345_, lean_object* v_postNode_1346_, lean_object* v___x_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec(v___x_1347_);
lean_dec_ref(v_postNode_1346_);
lean_dec_ref(v_preNode_1345_);
v___x_1353_ = l_List_reverse___redArg(v_x_1349_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
else
{
lean_object* v_head_1355_; lean_object* v_tail_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1374_; 
v_head_1355_ = lean_ctor_get(v_x_1348_, 0);
v_tail_1356_ = lean_ctor_get(v_x_1348_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_x_1348_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1358_ = v_x_1348_;
v_isShared_1359_ = v_isSharedCheck_1374_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_tail_1356_);
lean_inc(v_head_1355_);
lean_dec(v_x_1348_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1374_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; 
lean_inc(v___x_1347_);
lean_inc_ref(v_postNode_1346_);
lean_inc_ref(v_preNode_1345_);
v___x_1360_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1345_, v_postNode_1346_, v___x_1347_, v_head_1355_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 1, v_x_1349_);
lean_ctor_set(v___x_1358_, 0, v_a_1361_);
v___x_1363_ = v___x_1358_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1361_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_x_1349_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v_x_1348_ = v_tail_1356_;
v_x_1349_ = v___x_1363_;
goto _start;
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_del_object(v___x_1358_);
lean_dec(v_tail_1356_);
lean_dec(v_x_1349_);
lean_dec(v___x_1347_);
lean_dec_ref(v_postNode_1346_);
lean_dec_ref(v_preNode_1345_);
v_a_1366_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1360_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1360_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg___boxed(lean_object* v_preNode_1375_, lean_object* v_postNode_1376_, lean_object* v___x_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1375_, v_postNode_1376_, v___x_1377_, v_x_1378_, v_x_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg___boxed(lean_object* v_preNode_1384_, lean_object* v_postNode_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1384_, v_postNode_1385_, v_x_1386_, v_x_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(lean_object* v_preNode_1392_, lean_object* v_postNode_1393_, lean_object* v_ctx_x3f_1394_, lean_object* v_t_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___f_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1399_, 0, v_postNode_1393_);
v___x_1400_ = lean_box(0);
v___x_1401_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1392_, v___f_1399_, v_ctx_x3f_1394_, v_t_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1409_);
v___x_1403_ = v___x_1401_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v___x_1401_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1400_);
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1400_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_a_1410_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1401_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1401_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5___boxed(lean_object* v_preNode_1418_, lean_object* v_postNode_1419_, lean_object* v_ctx_x3f_1420_, lean_object* v_t_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v_preNode_1418_, v_postNode_1419_, v_ctx_x3f_1420_, v_t_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(uint8_t v___x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_box(v___x_1426_);
v___x_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed(lean_object* v___x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v___x_14066__boxed_1442_; lean_object* v_res_1443_; 
v___x_14066__boxed_1442_ = lean_unbox(v___x_1435_);
v_res_1443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0(v___x_14066__boxed_1442_, v_x_1436_, v_x_1437_, v_x_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec_ref(v_x_1438_);
lean_dec_ref(v_x_1437_);
lean_dec_ref(v_x_1436_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(uint8_t v___x_1444_, lean_object* v_val_1445_, lean_object* v_as_1446_, size_t v_sz_1447_, size_t v_i_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_usize_dec_lt(v_i_1448_, v_sz_1447_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
lean_dec(v_val_1445_);
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_b_1449_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1455_ = lean_box(v___x_1444_);
v___f_1456_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1456_, 0, v___x_1455_);
v___x_1457_ = l_Lean_Elab_Tactic_instImpl_00___x40_Lean_Elab_Tactic_Simp_2597418670____hygCtx___hyg_9_;
v___x_1458_ = lean_box(v___x_1444_);
lean_inc(v_val_1445_);
v___f_1459_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1459_, 0, v___x_1457_);
lean_closure_set(v___f_1459_, 1, v_val_1445_);
lean_closure_set(v___f_1459_, 2, v___x_1458_);
v___x_1460_ = lean_box(0);
v_a_1461_ = lean_array_uget_borrowed(v_as_1446_, v_i_1448_);
v___x_1462_ = lean_box(0);
lean_inc(v_a_1461_);
v___x_1463_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5(v___f_1456_, v___f_1459_, v___x_1462_, v_a_1461_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1463_) == 0)
{
size_t v___x_1464_; size_t v___x_1465_; 
lean_dec_ref_known(v___x_1463_, 1);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_add(v_i_1448_, v___x_1464_);
v_i_1448_ = v___x_1465_;
v_b_1449_ = v___x_1460_;
goto _start;
}
else
{
lean_dec(v_val_1445_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7___boxed(lean_object* v___x_1467_, lean_object* v_val_1468_, lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
uint8_t v___x_14091__boxed_1476_; size_t v_sz_boxed_1477_; size_t v_i_boxed_1478_; lean_object* v_res_1479_; 
v___x_14091__boxed_1476_ = lean_unbox(v___x_1467_);
v_sz_boxed_1477_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1478_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_14091__boxed_1476_, v_val_1468_, v_as_1469_, v_sz_boxed_1477_, v_i_boxed_1478_, v_b_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec_ref(v_as_1469_);
return v_res_1479_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_unsigned_to_nat(16u);
v___x_1482_ = lean_mk_array(v___x_1481_, v___x_1480_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__0, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__0_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__0);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0(lean_object* v_cmdStx_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1557_; 
v___x_1490_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0(v___y_1487_, v___y_1488_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1557_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1557_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = l_Lean_Elab_Tactic_linter_unusedSimpArgs;
v___x_1496_ = l_Lean_Linter_getLinterValue(v___x_1495_, v_a_1491_);
lean_dec(v_a_1491_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = lean_box(0);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1497_);
v___x_1499_ = v___x_1493_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
else
{
uint8_t v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = 0;
v___x_1502_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1486_, v___x_1501_);
if (lean_obj_tag(v___x_1502_) == 1)
{
lean_object* v___x_1503_; lean_object* v_infoState_1504_; lean_object* v_trees_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; size_t v_sz_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
lean_dec_ref_known(v___x_1502_, 1);
lean_del_object(v___x_1493_);
v___x_1503_ = lean_st_ref_get(v___y_1488_);
v_infoState_1504_ = lean_ctor_get(v___x_1503_, 8);
lean_inc_ref(v_infoState_1504_);
lean_dec(v___x_1503_);
v_trees_1505_ = lean_ctor_get(v_infoState_1504_, 2);
lean_inc_ref(v_trees_1505_);
lean_dec_ref(v_infoState_1504_);
v___x_1506_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1505_);
lean_dec_ref(v_trees_1505_);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_obj_once(&l_Lean_Linter_unusedSimpArgs___lam__0___closed__1, &l_Lean_Linter_unusedSimpArgs___lam__0___closed__1_once, _init_l_Lean_Linter_unusedSimpArgs___lam__0___closed__1);
v___x_1509_ = lean_st_mk_ref(v___x_1508_);
v___x_1510_ = lean_box(0);
v_sz_1511_ = lean_array_size(v___x_1506_);
v___x_1512_ = ((size_t)0ULL);
lean_inc(v___x_1509_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__7(v___x_1496_, v___x_1509_, v___x_1506_, v_sz_1511_, v___x_1512_, v___x_1510_, v___y_1487_, v___y_1488_);
lean_dec_ref(v___x_1506_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; lean_object* v___y_1516_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1540_; lean_object* v_size_1546_; lean_object* v_buckets_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
lean_dec_ref_known(v___x_1513_, 1);
v___x_1514_ = lean_st_ref_get(v___x_1509_);
lean_dec(v___x_1509_);
v_size_1546_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_size_1546_);
v_buckets_1547_ = lean_ctor_get(v___x_1514_, 1);
lean_inc_ref(v_buckets_1547_);
lean_dec(v___x_1514_);
v___x_1548_ = lean_mk_empty_array_with_capacity(v_size_1546_);
lean_dec(v_size_1546_);
v___x_1549_ = lean_array_get_size(v_buckets_1547_);
v___x_1550_ = lean_nat_dec_lt(v___x_1507_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_dec_ref(v_buckets_1547_);
v___y_1540_ = v___x_1548_;
goto v___jp_1539_;
}
else
{
size_t v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_usize_of_nat(v___x_1549_);
v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_unusedSimpArgs_spec__11(v_buckets_1547_, v___x_1512_, v___x_1551_, v___x_1548_);
lean_dec_ref(v_buckets_1547_);
v___y_1540_ = v___x_1552_;
goto v___jp_1539_;
}
v___jp_1515_:
{
size_t v_sz_1517_; lean_object* v___x_1518_; 
v_sz_1517_ = lean_array_size(v___y_1516_);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_unusedSimpArgs_spec__8(v___y_1516_, v_sz_1517_, v___x_1512_, v___x_1510_, v___y_1487_, v___y_1488_);
lean_dec_ref(v___y_1516_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v___x_1518_, 0);
lean_dec(v_unused_1526_);
v___x_1520_ = v___x_1518_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_dec(v___x_1518_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1510_);
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1510_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
return v___x_1518_;
}
}
v___jp_1527_:
{
lean_object* v___x_1532_; 
v___x_1532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v___y_1529_, v___y_1530_, v___y_1528_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec(v___y_1529_);
v___y_1516_ = v___x_1532_;
goto v___jp_1515_;
}
v___jp_1533_:
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_nat_dec_le(v___y_1537_, v___y_1535_);
if (v___x_1538_ == 0)
{
lean_dec(v___y_1535_);
lean_inc(v___y_1537_);
v___y_1528_ = v___y_1537_;
v___y_1529_ = v___y_1534_;
v___y_1530_ = v___y_1536_;
v___y_1531_ = v___y_1537_;
goto v___jp_1527_;
}
else
{
v___y_1528_ = v___y_1537_;
v___y_1529_ = v___y_1534_;
v___y_1530_ = v___y_1536_;
v___y_1531_ = v___y_1535_;
goto v___jp_1527_;
}
}
v___jp_1539_:
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = lean_array_get_size(v___y_1540_);
v___x_1542_ = lean_nat_dec_eq(v___x_1541_, v___x_1507_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_sub(v___x_1541_, v___x_1543_);
v___x_1545_ = lean_nat_dec_le(v___x_1507_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_inc(v___x_1544_);
v___y_1534_ = v___x_1541_;
v___y_1535_ = v___x_1544_;
v___y_1536_ = v___y_1540_;
v___y_1537_ = v___x_1544_;
goto v___jp_1533_;
}
else
{
v___y_1534_ = v___x_1541_;
v___y_1535_ = v___x_1544_;
v___y_1536_ = v___y_1540_;
v___y_1537_ = v___x_1507_;
goto v___jp_1533_;
}
}
else
{
v___y_1516_ = v___y_1540_;
goto v___jp_1515_;
}
}
}
else
{
lean_dec(v___x_1509_);
return v___x_1513_;
}
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_dec(v___x_1502_);
v___x_1553_ = lean_box(0);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1553_);
v___x_1555_ = v___x_1493_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_unusedSimpArgs___lam__0___boxed(lean_object* v_cmdStx_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Linter_unusedSimpArgs___lam__0(v_cmdStx_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v_cmdStx_1558_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(lean_object* v_o_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___redArg(v_o_1574_, v___y_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0___boxed(lean_object* v_o_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_unusedSimpArgs_spec__0_spec__0(v_o_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1(lean_object* v_00_u03b2_1584_, lean_object* v_m_1585_, lean_object* v_a_1586_, lean_object* v_b_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1___redArg(v_m_1585_, v_a_1586_, v_b_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(lean_object* v_00_u03b2_1589_, lean_object* v_m_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___redArg(v_m_1590_, v_a_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2___boxed(lean_object* v_00_u03b2_1593_, lean_object* v_m_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2(v_00_u03b2_1593_, v_m_1594_, v_a_1595_);
lean_dec_ref(v_a_1595_);
lean_dec_ref(v_m_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(lean_object* v_00_u03b1_1597_, lean_object* v_ref_1598_, lean_object* v_msg_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___redArg(v_ref_1598_, v_msg_1599_, v___y_1600_, v___y_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4___boxed(lean_object* v_00_u03b1_1604_, lean_object* v_ref_1605_, lean_object* v_msg_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4(v_00_u03b1_1604_, v_ref_1605_, v_msg_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v_ref_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(lean_object* v_upperBound_1611_, lean_object* v_snd_1612_, lean_object* v_fst_1613_, lean_object* v_inst_1614_, lean_object* v_R_1615_, lean_object* v_a_1616_, lean_object* v_b_1617_, lean_object* v_c_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___redArg(v_upperBound_1611_, v_snd_1612_, v_fst_1613_, v_a_1616_, v_b_1617_, v___y_1619_, v___y_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6___boxed(lean_object* v_upperBound_1623_, lean_object* v_snd_1624_, lean_object* v_fst_1625_, lean_object* v_inst_1626_, lean_object* v_R_1627_, lean_object* v_a_1628_, lean_object* v_b_1629_, lean_object* v_c_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Linter_unusedSimpArgs_spec__6(v_upperBound_1623_, v_snd_1624_, v_fst_1625_, v_inst_1626_, v_R_1627_, v_a_1628_, v_b_1629_, v_c_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec_ref(v_snd_1624_);
lean_dec(v_upperBound_1623_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(lean_object* v_n_1635_, lean_object* v_as_1636_, lean_object* v_lo_1637_, lean_object* v_hi_1638_, lean_object* v_w_1639_, lean_object* v_hlo_1640_, lean_object* v_hhi_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___redArg(v_n_1635_, v_as_1636_, v_lo_1637_, v_hi_1638_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9___boxed(lean_object* v_n_1643_, lean_object* v_as_1644_, lean_object* v_lo_1645_, lean_object* v_hi_1646_, lean_object* v_w_1647_, lean_object* v_hlo_1648_, lean_object* v_hhi_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9(v_n_1643_, v_as_1644_, v_lo_1645_, v_hi_1646_, v_w_1647_, v_hlo_1648_, v_hhi_1649_);
lean_dec(v_hi_1646_);
lean_dec(v_n_1643_);
return v_res_1650_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(lean_object* v_00_u03b2_1651_, lean_object* v_a_1652_, lean_object* v_x_1653_){
_start:
{
uint8_t v___x_1654_; 
v___x_1654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___redArg(v_a_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1655_, lean_object* v_a_1656_, lean_object* v_x_1657_){
_start:
{
uint8_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__2(v_00_u03b2_1655_, v_a_1656_, v_x_1657_);
lean_dec(v_x_1657_);
lean_dec_ref(v_a_1656_);
v_r_1659_ = lean_box(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3(lean_object* v_00_u03b2_1660_, lean_object* v_data_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3___redArg(v_data_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4(lean_object* v_00_u03b2_1663_, lean_object* v_a_1664_, lean_object* v_b_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__4___redArg(v_a_1664_, v_b_1665_, v_x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(lean_object* v_00_u03b2_1668_, lean_object* v_a_1669_, lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___redArg(v_a_1669_, v_x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1672_, lean_object* v_a_1673_, lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_unusedSimpArgs_spec__2_spec__6(v_00_u03b2_1672_, v_a_1673_, v_x_1674_);
lean_dec(v_x_1674_);
lean_dec_ref(v_a_1673_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(lean_object* v_msgData_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___redArg(v_msgData_1676_, v___y_1678_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11___boxed(lean_object* v_msgData_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__11(v_msgData_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(lean_object* v_00_u03b1_1686_, lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___redArg(v_msg_1687_, v___y_1688_, v___y_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_msg_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9(v_00_u03b1_1692_, v_msg_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(lean_object* v_00_u03b1_1698_, lean_object* v_msg_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___redArg(v_msg_1699_, v___y_1700_, v___y_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1704_, lean_object* v_msg_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__15(v_00_u03b1_1704_, v_msg_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(lean_object* v_00_u03b1_1710_, lean_object* v_preNode_1711_, lean_object* v_postNode_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___redArg(v_preNode_1711_, v_postNode_1712_, v_x_1713_, v_x_1714_, v___y_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_preNode_1720_, lean_object* v_postNode_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11(v_00_u03b1_1719_, v_preNode_1720_, v_postNode_1721_, v_x_1722_, v_x_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(lean_object* v_n_1728_, lean_object* v_lo_1729_, lean_object* v_hi_1730_, lean_object* v_hhi_1731_, lean_object* v_pivot_1732_, lean_object* v_as_1733_, lean_object* v_i_1734_, lean_object* v_k_1735_, lean_object* v_ilo_1736_, lean_object* v_ik_1737_, lean_object* v_w_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___redArg(v_hi_1730_, v_pivot_1732_, v_as_1733_, v_i_1734_, v_k_1735_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16___boxed(lean_object* v_n_1740_, lean_object* v_lo_1741_, lean_object* v_hi_1742_, lean_object* v_hhi_1743_, lean_object* v_pivot_1744_, lean_object* v_as_1745_, lean_object* v_i_1746_, lean_object* v_k_1747_, lean_object* v_ilo_1748_, lean_object* v_ik_1749_, lean_object* v_w_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_unusedSimpArgs_spec__9_spec__16(v_n_1740_, v_lo_1741_, v_hi_1742_, v_hhi_1743_, v_pivot_1744_, v_as_1745_, v_i_1746_, v_k_1747_, v_ilo_1748_, v_ik_1749_, v_w_1750_);
lean_dec_ref(v_pivot_1744_);
lean_dec(v_hi_1742_);
lean_dec(v_lo_1741_);
lean_dec(v_n_1740_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1752_, lean_object* v_i_1753_, lean_object* v_source_1754_, lean_object* v_target_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4___redArg(v_i_1753_, v_source_1754_, v_target_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(lean_object* v_msgData_1757_, lean_object* v_macroStack_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___redArg(v_msgData_1757_, v_macroStack_1758_, v___y_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_1763_, lean_object* v_macroStack_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Linter_unusedSimpArgs_spec__4_spec__9_spec__12(v_msgData_1763_, v_macroStack_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(lean_object* v_00_u03b1_1769_, lean_object* v_preNode_1770_, lean_object* v_postNode_1771_, lean_object* v___x_1772_, lean_object* v_x_1773_, lean_object* v_x_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___redArg(v_preNode_1770_, v_postNode_1771_, v___x_1772_, v_x_1773_, v_x_1774_, v___y_1775_, v___y_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_preNode_1780_, lean_object* v_postNode_1781_, lean_object* v___x_1782_, lean_object* v_x_1783_, lean_object* v_x_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_unusedSimpArgs_spec__5_spec__11_spec__16(v_00_u03b1_1779_, v_preNode_1780_, v_postNode_1781_, v___x_1782_, v_x_1783_, v_x_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15(lean_object* v_00_u03b2_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_unusedSimpArgs_spec__1_spec__3_spec__4_spec__15___redArg(v_x_1790_, v_x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lean_Linter_unusedSimpArgs));
v___x_1795_ = l_Lean_Elab_Command_addLinter(v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2____boxed(lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lean_Linter_UnusedSimpArgs_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedSimpArgs_2198311501____hygCtx___hyg_2_();
return v_res_1797_;
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
